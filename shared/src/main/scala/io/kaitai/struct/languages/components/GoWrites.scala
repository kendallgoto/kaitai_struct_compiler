package io.kaitai.struct.languages.components

import io.kaitai.struct.datatype._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype.{DataType, FixedEndian}
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format._
import io.kaitai.struct.translators.{GoTranslator, ResultLocalVar, ResultString, TranslatorResult}

trait GoWrites extends GoReads {
  def attrBytes(attr: AttrLikeSpec, id: Identifier, defEndian: Option[Endianness]): Unit = {
    attrParseIfHeader(id, attr.cond.ifExpr)

    val io = normalIO

    defEndian match {
      case Some(_: CalcEndian) | Some(InheritedEndian) =>
        attrBytesHybrid(
          () => attrBytes0(id, attr, io, Some(LittleEndian)),
          () => attrBytes0(id, attr, io, Some(BigEndian))
        )
      case None =>
        attrBytes0(id, attr, io, None)
      case Some(fe: FixedEndian) =>
        attrBytes0(id, attr, io, Some(fe))
    }

    attrParseIfFooter(attr.cond.ifExpr)
  }

  def attrBytes0(id: Identifier, attr: AttrLikeSpec, io: String, defEndian: Option[FixedEndian]): Unit = {
    if (attr.cond.repeat != NoRepeat)
      (ExtraAttrs.forAttr(attr, this) ++ List(attr)).foreach(a => condRepeatInitAttr(a.id, a.dataType))
    attr.cond.repeat match {
      case RepeatEos =>
        condRepeatEmptyCheck(id, Ast.expr.IntNum(0))
        condRepeatEosHeaderBytes(id, io, attr.dataType)
      case RepeatExpr(repeatExpr: Ast.expr) =>
        condRepeatEmptyCheck(id, repeatExpr)
        condRepeatExprHeaderBytes(id, io, attr.dataType, repeatExpr)
      case RepeatUntil(untilExpr: Ast.expr) =>
        condRepeatUntilHeader(id, io, attr.dataType, untilExpr)
      case NoRepeat =>
    }

    attrBytes2(id, attr.dataType, io, attr.cond.repeat, false, defEndian)

    attr.cond.repeat match {
      case RepeatEos =>
        condRepeatEosFooterBytes
      case _: RepeatExpr =>
        condRepeatExprFooterBytes
      case RepeatUntil(untilExpr: Ast.expr) =>
        condRepeatUntilFooter(id, io, attr.dataType, untilExpr)
      case NoRepeat =>
    }
  }

  def attrBytesTypeBytes(
    id: Identifier,
    dataType: BytesType,
    io: String,
    rep: RepeatSpec,
    isRaw: Boolean
  ): Unit = {
    val rawId = dataType.process match {
      case None => id
      case Some(_) => RawIdentifier(id)
    }
    val expr = bytesExprBytes(translator.outVarCheckRes(bytesExpr(dataType, id, None)), dataType)
    handleAssignmentBytes(rawId, expr, rep, isRaw)
    dataType.process.foreach((proc) => attrProcess(proc, rawId, id, rep))
  }

  def attrSwitchTypeBytes(
    id: Identifier,
    on: Ast.expr,
    cases: Map[Ast.expr, DataType],
    io: String,
    rep: RepeatSpec,
    defEndian: Option[FixedEndian],
    isNullable: Boolean,
    assignType: DataType
  ): Unit = {
    switchCases[DataType](id, on, cases,
      (dataType) => {
        attrBytes2(id, dataType, io, rep, false, defEndian, Some(assignType))
      },
      {
        case dataType@(t: BytesType) =>
          attrBytes2(RawIdentifier(id), dataType, io, rep, false, defEndian, Some(assignType))
        case dataType =>
          attrBytes2(id, dataType, io, rep, false, defEndian, Some(assignType))
      }
    )
  }

  def attrBytes2(
    id: Identifier,
    dataType: DataType,
    io: String,
    rep: RepeatSpec,
    isRaw: Boolean,
    defEndian: Option[FixedEndian],
    assignType: Option[DataType] = None
  ): Unit = {
    println(s"do attrBytes2 for ident $id with type $dataType, repeat $rep")
    dataType match {
      case t: UserType =>
        attrUserTypeBytes(id, t, io, rep, defEndian)
      // case t: BytesType =>
      //   attrBytesTypeBytes(id, t, io, rep, isRaw)
      case st: SwitchType =>
        attrSwitchTypeBytes(id, st.on, st.cases, io, rep, defEndian, st.isNullableSwitchRaw, st.combinedType)
      // case t: StrFromBytesType =>
      //   val r1 = bytesExprBytes(translator.outVarCheckRes(bytesExpr(t.bytes, id, defEndian)), t.bytes)
      //   val expr = translator.bytesToStr(translator.resToStr(r1), t.encoding)
      //   handleAssignmentBytes(id, expr, rep, isRaw)
      case t: EnumType =>
        // unwrap enum since we don't really care about its type name
        attrBytes2(id, t.basedOn, io, rep, isRaw, defEndian, assignType)
      case _: BitsType1 =>
        val expr = bytesExpr(dataType, id, defEndian)
        val r1 = translator.outBoolToInt(expr)
        appendToBitBytes(r1)
      case _: BitsType =>
        val expr = bytesExpr(dataType, id, defEndian)
        handleBits(ResultString(expr), dataType)
      case _ =>
        val expr = bytesExpr(dataType, id, defEndian)
        handleAssignmentBytes(id, ResultString(expr), rep, isRaw)
    }
  }

  // def bytesPadTermExpr(id: ResultLocalVar, padRight: Option[Int], terminator: Option[Seq[Byte]], include: Boolean): String = {
  //   val expr0 = translator.resToStr(id)
  //   val expr1 = padRight match {
  //     case Some(padByte) => s"kaitai.BytesStripRight($expr0, $padByte)"
  //     case None => expr0
  //   }
  //   val expr2 = terminator match {
  //     case Some(term) =>
  //       if (term.length == 1) {
  //         val t = term.head & 0xff
  //         s"kaitai.BytesTerminate($expr1, $t, $include)"
  //       } else {
  //         s"kaitai.BytesTerminateMulti($expr1, ${translator.resToStr(translator.doByteArrayLiteral(term))}, $include)"
  //       }
  //     case None => expr1
  //   }
  //   expr2
  // }

  def bytesExprBytes(id: ResultLocalVar, dataType: BytesType): ResultLocalVar = {
    dataType match {
      case BytesEosType(terminator, include, padRight, _) =>
        translator.outTransform(id, bytesPadTermExpr(id, padRight, terminator, include))
      case BytesLimitType(_, terminator, include, padRight, _) =>
        translator.outTransform(id, bytesPadTermExpr(id, padRight, terminator, include))
      case _ =>
        id
    }
  }

  def attrUserTypeBytes(id: Identifier, dataType: UserType, io: String, rep: RepeatSpec, defEndian: Option[FixedEndian]): Unit = {
    val expr = bytesExpr(dataType, id, defEndian)
    val v = ResultLocalVar(translator.allocateLocalVar())
    val tempVarName = translator.resToStr(v)
    val originalType = typeProvider.determineType(id)
    val typecast = originalType match {
      case SwitchType(_,_,_,_) => s".(${kaitaiType2NativeType2(dataType)})"
      case _ => ""
    }
    rep match {
      case NoRepeat => handleAssignmentTempVarErr(dataType, tempVarName, s"${expr}${typecast}.Bytes_()")
      case _ => handleAssignmentTempVarErr(dataType, tempVarName, s"${expr}[i]${typecast}.Bytes_()")
    }
    translator.outAddErrCheck()
    handleAssignmentSimpleBytes(id, v)
  }

  def handleAssignmentBytes(id: Identifier, expr: TranslatorResult, rep: RepeatSpec, isRaw: Boolean): Unit = {
    rep match {
      case RepeatEos => handleAssignmentRepeatEosBytes(id, expr)
      case RepeatExpr(_) => handleAssignmentRepeatExprBytes(id, expr)
      case RepeatUntil(_) => handleAssignmentRepeatUntilBytes(id, expr, isRaw)
      case NoRepeat => handleAssignmentSimpleBytes(id, expr)
    }
  }

  def handleAssignmentRepeatEosBytes(id: Identifier, expr: TranslatorResult): Unit
  def handleAssignmentRepeatExprBytes(id: Identifier, expr: TranslatorResult): Unit
  def handleAssignmentRepeatUntilBytes(id: Identifier, expr: TranslatorResult, isRaw: Boolean): Unit
  // def handleAssignmentBinaryBytes(id: Identifier, expr: TranslatorResult): Unit
  def handleAssignmentSimpleBytes(id: Identifier, expr: TranslatorResult): Unit

  def bytesExpr(dataType: DataType, id: Identifier, defEndian: Option[FixedEndian]): String
  def userTypeDebugRead(id: String, t: UserType, io: String): Unit
  def attrBytesHybrid(leProc: () => Unit, beProc: () => Unit): Unit
  def handleAssignmentTempVarErr(dataType: DataType, id: String, expr: String): Unit
  def prepareBitBytes(): Unit
  def endBitBytes(): Unit
  def appendToBitBytes(r: TranslatorResult): Unit
  def handleBits(id: TranslatorResult, attrType: DataType): Unit
  def condRepeatEmptyCheck(id: Identifier, repeatExpr: Ast.expr): Unit
  def condRepeatExprHeaderBytes(id: Identifier, io: String, dataType: DataType, repeatExpr: Ast.expr): Unit
  def condRepeatEosHeaderBytes(id: Identifier, io: String, dataType: DataType): Unit
  def condRepeatExprFooterBytes: Unit
  def condRepeatEosFooterBytes: Unit
  def kaitaiType2NativeType2(attrType: DataType): String
}
