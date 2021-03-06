// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf.engine

import com.daml.lf.command._
import com.daml.lf.data.Ref._
import com.daml.lf.data._
import com.daml.lf.language.Ast._
import com.daml.lf.speedy.{SValue, Command => SpeedyCommand}
import com.daml.lf.value.Value

import scala.annotation.tailrec

private[engine] class CommandPreprocessor(compiledPackages: MutableCompiledPackages) {

  private val valueTranslator = new ValueTranslator(compiledPackages)

  private[engine] def translateValue(
      ty0: Type,
      v0: Value[Value.AbsoluteContractId],
  ): Result[SValue] = {

    valueTranslator.translateValue(ty0, v0) match {
      case ResultNeedPackage(pkgId, resume) =>
        ResultNeedPackage(
          pkgId, {
            case None => ResultError(Error(s"Couldn't find package $pkgId"))
            case Some(pkg) =>
              compiledPackages.addPackage(pkgId, pkg).flatMap(_ => resume(Some(pkg)))
          }
        )
      case result =>
        result
    }
  }

  private[engine] def preprocessCreate(
      templateId: Identifier,
      argument: Value[Value.AbsoluteContractId],
  ): Result[SpeedyCommand] =
    Result.needDataType(
      compiledPackages,
      templateId,
      dataType => {
        // we rely on datatypes which are also templates to have _no_ parameters, according
        // to the DAML-LF spec.
        if (dataType.params.length > 0) {
          ResultError(Error(
            s"Unexpected type parameters ${dataType.params} for template $templateId. Template datatypes should never have parameters."))
        } else {
          translateValue(TTyCon(templateId), argument)
            .map(SpeedyCommand.Create(templateId, _))
        }
      }
    )

  private[engine] def preprocessFetch(
      templateId: Identifier,
      coid: Value.AbsoluteContractId,
  ): Result[SpeedyCommand] =
    Result.needDataType(
      compiledPackages,
      templateId,
      dataType => {
        // we rely on datatypes which are also templates to have _no_ parameters, according
        // to the DAML-LF spec.
        if (dataType.params.length > 0) {
          ResultError(Error(
            s"Unexpected type parameters ${dataType.params} for template $templateId. Template datatypes should never have parameters."))
        } else {
          ResultDone(SpeedyCommand.Fetch(templateId, SValue.SContractId(coid)))
        }
      }
    )

  private[engine] def preprocessExercise(
      templateId: Identifier,
      contractId: Value.ContractId,
      choiceId: ChoiceName,
      argument: Value[Value.AbsoluteContractId],
  ): Result[SpeedyCommand] =
    Result.needTemplate(
      compiledPackages,
      templateId,
      template => {
        template.choices.get(choiceId) match {
          case None =>
            val choicesNames: Seq[String] = template.choices.toList.map(_._1)
            ResultError(Error(
              s"Couldn't find requested choice $choiceId for template $templateId. Available choices: $choicesNames"))
          case Some(choice) =>
            val choiceTyp = choice.argBinder._2
            translateValue(choiceTyp, argument).map(
              SpeedyCommand.Exercise(templateId, SValue.SContractId(contractId), choiceId, _))
        }
      }
    )

  private[engine] def preprocessExerciseByKey(
      templateId: Identifier,
      contractKey: Value[Value.AbsoluteContractId],
      choiceId: ChoiceName,
      argument: Value[Value.AbsoluteContractId],
  ): Result[SpeedyCommand] =
    Result.needTemplate(
      compiledPackages,
      templateId,
      template => {
        (template.choices.get(choiceId), template.key) match {
          case (None, _) =>
            val choicesNames: Seq[String] = template.choices.toList.map(_._1)
            ResultError(Error(
              s"Couldn't find requested choice $choiceId for template $templateId. Available choices: $choicesNames"))
          case (_, None) =>
            ResultError(
              Error(s"Impossible to exercise by key, no key is defined for template $templateId"))
          case (Some(choice), Some(ck)) =>
            val (_, choiceType) = choice.argBinder
            for {
              arg <- translateValue(choiceType, argument)
              key <- translateValue(ck.typ, contractKey)
            } yield SpeedyCommand.ExerciseByKey(templateId, key, choiceId, arg)
        }
      }
    )

  private[engine] def preprocessCreateAndExercise(
      templateId: ValueRef,
      createArgument: Value[Value.AbsoluteContractId],
      choiceId: ChoiceName,
      choiceArgument: Value[Value.AbsoluteContractId],
  ): Result[SpeedyCommand] = {
    Result.needDataType(
      compiledPackages,
      templateId,
      dataType => {
        // we rely on datatypes which are also templates to have _no_ parameters, according
        // to the DAML-LF spec.
        if (dataType.params.length > 0) {
          ResultError(Error(
            s"Unexpected type parameters ${dataType.params} for template $templateId. Template datatypes should never have parameters."))
        } else {
          val typ = TTyCon(templateId)
          translateValue(typ, createArgument).flatMap {
            createValue =>
              Result.needTemplate(
                compiledPackages,
                templateId,
                template => {
                  template.choices.get(choiceId) match {
                    case None =>
                      val choicesNames: Seq[String] = template.choices.toList.map(_._1)
                      ResultError(Error(
                        s"Couldn't find requested choice $choiceId for template $templateId. Available choices: $choicesNames"))
                    case Some(choice) =>
                      val choiceTyp = choice.argBinder._2
                      translateValue(choiceTyp, choiceArgument).map(
                        SpeedyCommand
                          .CreateAndExercise(templateId, createValue, choiceId, _))
                  }
                }
              )
          }
        }
      }
    )
  }

  private[engine] def preprocessLookupByKey(
      templateId: ValueRef,
      contractKey: Value[Nothing],
  ): Result[SpeedyCommand] = {
    Result.needTemplate(
      compiledPackages,
      templateId,
      template => {
        template.key match {
          case None =>
            ResultError(
              Error(s"Impossible to lookup by key, no key is defined for template $templateId"))
          case Some(ck) =>
            for {
              key <- translateValue(ck.typ, contractKey)
            } yield SpeedyCommand.LookupByKey(templateId, key)
        }
      }
    )
  }

  private[engine] def preprocessCommand(cmd: Command): Result[SpeedyCommand] =
    cmd match {
      case CreateCommand(templateId, argument) =>
        preprocessCreate(templateId, argument)
      case ExerciseCommand(templateId, contractId, choiceId, argument) =>
        preprocessExercise(templateId, contractId, choiceId, argument)
      case ExerciseByKeyCommand(templateId, contractKey, choiceId, argument) =>
        preprocessExerciseByKey(
          templateId,
          contractKey,
          choiceId,
          argument
        )
      case CreateAndExerciseCommand(
          templateId,
          createArgument,
          choiceId,
          choiceArgument
          ) =>
        preprocessCreateAndExercise(
          templateId,
          createArgument,
          choiceId,
          choiceArgument
        )
    }

  private[engine] def preprocessCommands(
      cmds0: Commands,
  ): Result[ImmArray[SpeedyCommand]] = {
    // before, we had
    //
    // ```
    // Result.sequence(ImmArray(cmds.commands).map(preprocessCommand))
    // ```
    //
    // however that is bad, because it'll generate a `NeedPackage` for each command,
    // if the same package is needed for every command. If we go step by step,
    // on the other hand, we will cache the package and go through with execution
    // after the first command which demands it.
    @tailrec
    def go(
        processed: BackStack[SpeedyCommand],
        toProcess: ImmArray[Command],
    ): Result[ImmArray[SpeedyCommand]] = {
      toProcess match {
        case ImmArray() => ResultDone(processed.toImmArray)
        case ImmArrayCons(cmd, cmds) =>
          preprocessCommand(cmd) match {
            case ResultDone(processedCommand) => go(processed :+ processedCommand, cmds)
            case ResultError(err) => ResultError(err)
            case ResultNeedContract(acoid, resume) =>
              ResultNeedContract(acoid, { contract =>
                resume(contract).flatMap(processedCommand =>
                  goResume(processed :+ processedCommand, cmds))
              })
            case ResultNeedPackage(pkgId, resume) =>
              ResultNeedPackage(pkgId, { pkg =>
                resume(pkg).flatMap(processedCommand =>
                  goResume(processed :+ processedCommand, cmds))
              })
            case ResultNeedKey(key, resume) =>
              ResultNeedKey(key, { contract =>
                resume(contract).flatMap(processedCommand =>
                  goResume(processed :+ processedCommand, cmds))
              })
          }
      }
    }

    def goResume(processed: BackStack[SpeedyCommand], toProcess: ImmArray[Command]) =
      go(processed, toProcess)

    go(BackStack.empty, cmds0.commands)
  }

}
