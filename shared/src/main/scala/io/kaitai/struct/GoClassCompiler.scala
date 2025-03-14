package io.kaitai.struct

import io.kaitai.struct.datatype.DataType.{CalcIntType, KaitaiStreamType, AnyType, KaitaiStructType, UserTypeInstream}
import io.kaitai.struct.datatype.{BigEndian, CalcEndian, Endianness, FixedEndian, InheritedEndian, LittleEndian}
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format._
import io.kaitai.struct.languages.GoCompiler
import io.kaitai.struct.languages.components.ExtraAttrs

class GoClassCompiler(
  classSpecs: ClassSpecs,
  override val topClass: ClassSpec,
  config: RuntimeConfig
) extends ClassCompiler(classSpecs, topClass, config, GoCompiler) {

  val golang = lang.asInstanceOf[GoCompiler]

  override def compileAttrDeclarations(attrs: List[MemberSpec]): Unit = {
    attrs.foreach { (attr) =>
      val isNullable = if (lang.switchBytesOnlyAsRaw) {
        attr.isNullableSwitchRaw
      } else {
        attr.isNullable
      }
      golang.attributeDeclarationFromMemberSpec(attr, isNullable)
    }
  }

  override def compileClass(curClass: ClassSpec): Unit = {
    provider.nowClass = curClass

    val extraAttrs = List(
      AttrSpec(List(), IoIdentifier, KaitaiStreamType),
      AttrSpec(List(), RootIdentifier, KaitaiStructType),
      AttrSpec(List(), ParentIdentifier, curClass.parentType)
    ) ++ ExtraAttrs.forClassSpec(curClass, lang)

    if (!curClass.doc.isEmpty)
      lang.classDoc(curClass.name, curClass.doc)

    // Enums declaration defines types, so they need to go first
    compileEnums(curClass)

    if (lang.config.readStoresPos)
      golang.debugClassSequenceWithClassName(curClass.name, curClass.seq)

    // Basic struct declaration
    lang.classHeader(curClass.name)
    compileAttrDeclarations(curClass.seq ++ curClass.params ++ extraAttrs)
    if (lang.config.readStoresPos)
      lang.attributeDeclaration(SpecialIdentifier("Debug_"), AnyType, false)

    curClass.instances.foreach { case (instName, instSpec) =>
      compileInstanceDeclaration(instName, instSpec)
    }
    lang.classFooter(curClass.name)

    // Constructor = Read() function
    compileReadFunction(curClass)

    curClass.toStringExpr.foreach(expr => lang.classToString(expr))

    compileInstances(curClass)

    compileAttrReaders(curClass.seq ++ extraAttrs)

    // Recursive types
    compileSubclasses(curClass)
  }

  // Duplicate compileEagerRead to duplicate function, which we'll use for Bytes()
  def compileSeqForBytes(seq: List[AttrSpec], defEndian: Option[FixedEndian]) = {
    var wasUnaligned = false
    seq.foreach { (attr) =>
      val nowUnaligned = isUnalignedBits(attr.dataType)
      if (!wasUnaligned && nowUnaligned)
        golang.prepareBitBytes()
      if (wasUnaligned && !nowUnaligned)
        golang.endBitBytes()
      golang.attrBytes(attr, attr.id, defEndian)
      wasUnaligned = nowUnaligned
    }
    if (wasUnaligned)
      golang.endBitBytes()
  }

  def compileSeqProcForBytes(seq: List[AttrSpec], defEndian: Option[FixedEndian]) = {
    golang.bytesHeader(defEndian, seq.isEmpty)
    compileSeqForBytes(seq, defEndian)
    golang.bytesFooter()
  }

  def compileEagerBytes(seq: List[AttrSpec], endian: Option[Endianness]): Unit = {
    endian match {
      case None | Some(_: FixedEndian) =>
        compileSeqProcForBytes(seq, None)
      case Some(ce: CalcEndian) =>
        // TODO
        // lang.readHeader(None, false)
        // compileCalcEndian(ce)
        // lang.runReadCalc()
        // lang.readFooter()

        // compileSeqProc(seq, Some(LittleEndian))
        // compileSeqProc(seq, Some(BigEndian))
      case Some(InheritedEndian) =>
        // TODO
        // lang.readHeader(None, false)
        // lang.runReadCalc()
        // lang.readFooter()

        // compileSeqProc(seq, Some(LittleEndian))
        // compileSeqProc(seq, Some(BigEndian))
    }
  }
  // end Bytes() specific

  def compileReadFunction(curClass: ClassSpec) = {
    lang.classConstructorHeader(
      curClass.name,
      curClass.parentType,
      topClassName,
      curClass.meta.endian.contains(InheritedEndian),
      curClass.params
    )
    compileEagerRead(curClass.seq, curClass.meta.endian)
    compileEagerBytes(curClass.seq, curClass.meta.endian) // duplicate process here and do bytes too
    lang.classConstructorFooter
  }

  override def compileInstance(className: List[String], instName: InstanceIdentifier, instSpec: InstanceSpec, endian: Option[Endianness]): Unit = {
    // Determine datatype
    val dataType = instSpec.dataTypeComposite

    if (!instSpec.doc.isEmpty)
      lang.attributeDoc(instName, instSpec.doc)
    lang.instanceHeader(className, instName, dataType, instSpec.isNullable)
    lang.instanceCheckCacheAndReturn(instName, dataType)

    lang.instanceSetCalculated(instName)
    instSpec match {
      case vi: ValueInstanceSpec =>
        lang.attrParseIfHeader(instName, vi.ifExpr)
        lang.instanceCalculate(instName, dataType, vi.value)
        lang.attrParseIfFooter(vi.ifExpr)
      case pi: ParseInstanceSpec =>
        lang.attrParse(pi, instName, endian)
    }

    lang.instanceReturn(instName, dataType)
    lang.instanceFooter
  }

  override def compileCalcEndian(ce: CalcEndian): Unit = {
    def renderProc(result: FixedEndian): Unit = {
      val v = result match {
        case LittleEndian => Ast.expr.IntNum(1)
        case BigEndian => Ast.expr.IntNum(0)
      }
      lang.instanceCalculate(IS_LE_ID, CalcIntType, v)
    }
    lang.switchCases[FixedEndian](IS_LE_ID, ce.on, ce.cases, renderProc, renderProc)
  }
}
