// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.daml.lf.engine

import java.util

import com.digitalasset.daml.lf.CompiledPackages
import com.digitalasset.daml.lf.data.Ref
import com.digitalasset.daml.lf.data._
import com.digitalasset.daml.lf.language.Ast._
import com.digitalasset.daml.lf.language.Util._
import com.digitalasset.daml.lf.speedy.SValue
import com.digitalasset.daml.lf.value.Value
import com.digitalasset.daml.lf.value.Value._

import scala.annotation.tailrec
import scala.collection.immutable.HashMap
import scala.util.control.NoStackTrace

private[engine] object ValueTranslator {

  private def ArrayList[X](as: X*): util.ArrayList[X] = {
    val a = new util.ArrayList[X](as.length)
    as.foreach(a.add)
    a
  }

  // we use this for easier error handling in translateValues
  private final case class ValueTranslationError(err: Error)
      extends RuntimeException(err.toString, null, true, false)

  private final case object ValueTranslationMissingPackage
      extends RuntimeException
      with NoStackTrace

  private def fail(s: String): Nothing =
    throw ValueTranslationError(Error(s))

  private def fail(e: Error): Nothing =
    throw ValueTranslationError(e)

  private def missingPackage: Nothing =
    throw ValueTranslationMissingPackage

  private def collectPkgIds(typ: Type): Set[Ref.PackageId] = {
    val pkgIds = Set.newBuilder[Ref.PackageId]
    def go(typ0: Type): Unit =
      typ0 match {
        case TBuiltin(_) =>
        case TTyCon(tycon) => pkgIds += tycon.packageId
        case TApp(tyfun, arg) => go(tyfun); go(arg)
        case TStruct(_) | TSynApp(_, _) | TForall(_, _) | TNat(_) | TVar(_) =>
          fail(s"unserializable type ${typ0.pretty}")
      }
    go(typ)
    pkgIds.result()
  }

  private def needPackages(pkgs: List[Ref.PackageId], restart: => Result[SValue]): Result[SValue] =
    pkgs match {
      case head :: tail =>
        ResultNeedPackage(head, _ => needPackages(tail, restart))
      case Nil =>
        restart
    }
}

private[engine] final class ValueTranslator(compiledPackages: CompiledPackages) {

  import ValueTranslator._

  // note: all the types in params must be closed.
  //
  // this is not tail recursive, but it doesn't really matter, since types are bounded
  // by what's in the source, which should be short enough...
  private[this] def replaceParameters(params: ImmArray[(TypeVarName, Type)], typ0: Type): Type =
    if (params.isEmpty) { // optimization
      typ0
    } else {
      val paramsMap: Map[TypeVarName, Type] = Map(params.toSeq: _*)

      def go(typ: Type): Type =
        typ match {
          case TVar(v) =>
            paramsMap.get(v) match {
              case None =>
                fail(s"Got out of bounds type variable $v when replacing parameters")
              case Some(ty) => ty
            }
          case TTyCon(_) | TBuiltin(_) | TNat(_) => typ
          case TApp(tyfun, arg) => TApp(go(tyfun), go(arg))
          case forall: TForall =>
            fail(
              s"Unexpected forall when replacing parameters in command translation -- all types should be serializable, and foralls are not: $forall")
          case struct: TStruct =>
            fail(
              s"Unexpected struct when replacing parameters in command translation -- all types should be serializable, and structs are not: $struct")
          case syn: TSynApp =>
            fail(
              s"Unexpected type synonym application when replacing parameters in command translation -- all types should be serializable, and synonyms are not: $syn")
        }

      go(typ0)
    }

  private[this] def labeledRecordToMap(
      fields: ImmArray[(Option[String], Value[AbsoluteContractId])])
    : Option[Map[String, Value[AbsoluteContractId]]] = {
    @tailrec
    def go(
        fields: ImmArray[(Option[String], Value[AbsoluteContractId])],
        map: Map[String, Value[AbsoluteContractId]])
      : Option[Map[String, Value[AbsoluteContractId]]] = {
      fields match {
        case ImmArray() => Some(map)
        case ImmArrayCons((None, _), _) => None
        case ImmArrayCons((Some(label), value), tail) =>
          go(tail, map + (label -> value))
      }
    }
    go(fields, Map.empty)
  }

  // since we get these values from third-party users of the library, check the recursion limit
  // here, too.
  private[engine] def translateValue(ty0: Type, v0: Value[AbsoluteContractId]): Result[SValue] = {
    import SValue.{SValue => _, _}

    def go(nesting: Int, ty: Type, value: Value[AbsoluteContractId]): SValue = {
      if (nesting > Value.MAXIMUM_NESTING) {
        fail(s"Provided value exceeds maximum nesting level of ${Value.MAXIMUM_NESTING}")
      } else {
        val newNesting = nesting + 1
        (ty, value) match {
          // simple values
          case (TUnit, ValueUnit) =>
            SUnit
          case (TBool, ValueBool(b)) =>
            if (b) SValue.SValue.True else SValue.SValue.False
          case (TInt64, ValueInt64(i)) =>
            SInt64(i)
          case (TTimestamp, ValueTimestamp(t)) =>
            STimestamp(t)
          case (TDate, ValueDate(t)) =>
            SDate(t)
          case (TText, ValueText(t)) =>
            SText(t)
          case (TNumeric(TNat(s)), ValueNumeric(d)) =>
            Numeric.fromBigDecimal(s, d).fold(fail, SNumeric)
          case (TParty, ValueParty(p)) =>
            SParty(p)
          case (TContractId(typ), ValueContractId(c)) =>
            typ match {
              case TTyCon(_) => SContractId(c)
              case _ => fail(s"Expected a type constructor but found $typ.")
            }

          // optional
          case (TOptional(elemType), ValueOptional(mb)) =>
            SOptional(mb.map(go(newNesting, elemType, _)))

          // list
          case (TList(elemType), ValueList(ls)) =>
            SList(ls.map(go(newNesting, elemType, _)))

          // textMap
          case (TTextMap(elemType), ValueTextMap(map)) =>
            type O[_] = HashMap[String, SValue]
            STextMap(map.iterator.map { case (k, v) => k -> go(newNesting, elemType, v) }.to[O])

          // genMap
          case (TGenMap(keyType, valueType), ValueGenMap(entries)) =>
            SGenMap(entries.iterator.map {
              case (k, v) => go(newNesting, keyType, k) -> go(newNesting, valueType, v)
            })

          // variants
          case (
              TTyConApp(typeVariantId, tyConArgs),
              ValueVariant(mbVariantId, constructorName, val0)) =>
            mbVariantId match {
              case Some(valueVariantId) if typeVariantId != valueVariantId =>
                fail(
                  s"Mismatching variant id, the type tells us $typeVariantId, but the value tells us $valueVariantId")
              case _ =>
                compiledPackages.getPackage(typeVariantId.packageId) match {
                  // if the package is not there, look for all the packages in the value and restart.
                  case None =>
                    missingPackage
                  case Some(pkg) =>
                    PackageLookup.lookupVariant(pkg, typeVariantId.qualifiedName) match {
                      case Left(err) => fail(err)
                      case Right((dataTypParams, variantDef: DataVariant)) =>
                        variantDef.constructorRank.get(constructorName) match {
                          case None =>
                            fail(
                              s"Couldn't find provided variant constructor $constructorName in variant $typeVariantId")
                          case Some(rank) =>
                            val (_, argTyp) = variantDef.variants(rank)
                            if (dataTypParams.length != tyConArgs.length) {
                              sys.error(
                                "TODO(FM) impossible: type constructor applied to wrong number of parameters, this should never happen on a well-typed package, return better error")
                            }
                            val instantiatedArgTyp =
                              replaceParameters(dataTypParams.map(_._1).zip(tyConArgs), argTyp)
                            SVariant(
                              typeVariantId,
                              constructorName,
                              rank,
                              go(newNesting, instantiatedArgTyp, val0))
                        }
                    }
                }
            }
          // records
          case (TTyConApp(typeRecordId, tyConArgs), ValueRecord(mbRecordId, flds)) =>
            mbRecordId match {
              case Some(valueRecordId) if typeRecordId != valueRecordId =>
                fail(
                  s"Mismatching record id, the type tells us $typeRecordId, but the value tells us $valueRecordId")
              case _ =>
                compiledPackages.getPackage(typeRecordId.packageId) match {
                  // if the package is not there, ask for all missing packages in the value and restart.
                  case None =>
                    missingPackage
                  case Some(pkg) =>
                    PackageLookup.lookupRecord(pkg, typeRecordId.qualifiedName) match {
                      case Left(err) => throw ValueTranslationError(err)
                      case Right((dataTypParams, DataRecord(recordFlds, _))) =>
                        // note that we check the number of fields _before_ checking if we can do
                        // field reordering by looking at the labels. this means that it's forbidden to
                        // repeat keys even if we provide all the labels, which might be surprising
                        // since in JavaScript / Scala / most languages (but _not_ JSON, interestingly)
                        // it's ok to do `{"a": 1, "a": 2}`, where the second occurrence would just win.
                        if (recordFlds.length != flds.length) {
                          fail(
                            s"Expecting ${recordFlds.length} field for record $typeRecordId, but got ${flds.length}")
                        }
                        if (dataTypParams.length != tyConArgs.length) {
                          sys.error(
                            "TODO(FM) impossible: type constructor applied to wrong number of parameters, this should never happen on a well-typed package, return better error")
                        }
                        val params = dataTypParams.map(_._1).zip(tyConArgs)
                        val fields = labeledRecordToMap(flds) match {
                          case None =>
                            (recordFlds zip flds).map {
                              case ((lbl, typ), (mbLbl, v)) =>
                                mbLbl
                                  .filter(_ != lbl)
                                  .foreach(lbl_ =>
                                    fail(
                                      s"Mismatching record label $lbl_ (expecting $lbl) for record $typeRecordId"))
                                val replacedTyp = replaceParameters(params, typ)
                                lbl -> go(newNesting, replacedTyp, v)
                            }
                          case Some(labeledRecords) =>
                            recordFlds.map {
                              case ((lbl, typ)) =>
                                labeledRecords
                                  .get(lbl)
                                  .fold(fail(s"Missing record label $lbl for record $typeRecordId")) {
                                    v =>
                                      val replacedTyp = replaceParameters(params, typ)
                                      lbl -> go(newNesting, replacedTyp, v)
                                  }
                            }
                        }

                        SRecord(
                          typeRecordId,
                          Ref.Name.Array(fields.map(_._1).toSeq: _*),
                          ArrayList(fields.map(_._2).toSeq: _*)
                        )
                    }
                }
            }

          case (TTyCon(typeEnumId), ValueEnum(mbId, constructor)) =>
            mbId match {
              case Some(valueEnumId) if valueEnumId != typeEnumId =>
                fail(
                  s"Mismatching enum id, the type tells us $typeEnumId, but the value tells us $valueEnumId")
              case _ =>
                compiledPackages.getPackage(typeEnumId.packageId) match {
                  case None =>
                    missingPackage
                  case Some(pkg) =>
                    PackageLookup.lookupEnum(pkg, typeEnumId.qualifiedName) match {
                      case Left(err) => throw ValueTranslationError(err)
                      case Right(dataDef: DataEnum) =>
                        dataDef.constructorRank.get(constructor) match {
                          case Some(rank) =>
                            SEnum(typeEnumId, constructor, rank)
                          case None =>
                            fail(
                              s"Couldn't find provided variant constructor $constructor in enum $typeEnumId")
                        }
                    }
                }
            }

          // every other pairs of types and values are invalid
          case (otherType, otherValue) =>
            fail(s"mismatching type: $otherType and value: $otherValue")
        }
      }
    }

    def restart: Result[SValue] =
      try {
        ResultDone(go(0, ty0, v0))
      } catch {
        case ValueTranslationError(e) => ResultError(e)
        case ValueTranslationMissingPackage =>
          // if one package is missing, we collect all of them, ask for loading them, and restart.
          needPackages(
            collectPkgIds(ty0).filterNot(compiledPackages.packages.isDefinedAt).toList,
            restart
          )
      }

    restart
  }

}
