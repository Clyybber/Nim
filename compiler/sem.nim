#
#
#           The Nim Compiler
#        (c) Copyright 2013 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements the semantic checking pass.

import
  ast, strutils, options, astalgo, msgs, idents, renderer,
  types, magicsys, semfold, modulepaths, lookups, passes,
  semdata, evaltempl, sempass2, semmacrosanity, lineinfos,
  strtabs, modulegraphs, wordrecg

when defined(nimfix):
  import nimfix/prettybase

import semutils

proc semMacroExpr*(c: PContext, n, nOrig: PNode, sym: PSym, flags: TExprFlags = {}): PNode
proc semConstExpr*(c: PContext, n: PNode): PNode
proc forceBool*(c: PContext, n: PNode): PNode
proc semConstBoolExpr*(c: PContext, n: PNode): PNode

proc fixupTypeAfterEval*(c: PContext, evaluated, eOrig: PNode): PNode # semexprs, sem.semConstExpr
proc fitNodePostMatch*(c: PContext, formal: PType, arg: PNode): PNode # seminst, sem.fitNode
proc fitNode*(c: PContext, formal: PType, arg: PNode; info: TLineInfo): PNode # semexprs, semexprs/semobjconstr, hlo, semstmts, semtypes, sem

proc semStmt*(c: PContext, n: PNode; flags: TExprFlags): PNode
proc semParamList*(c: PContext, n, genericParams: PNode, s: PSym)
proc semTemplateExpr*(c: PContext, n: PNode, s: PSym, flags: TExprFlags = {}): PNode
proc semExpr*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc semExprNoDeref*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc semExprWithType*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc semWhen*(c: PContext, n: PNode, semCheck: bool = true): PNode
proc semDirectOp*(c: PContext, n: PNode, flags: TExprFlags): PNode
proc semExprNoType*(c: PContext, n: PNode): PNode
proc semProcBody*(c: PContext, n: PNode): PNode
proc semOpAux*(c: PContext, n: PNode)
proc defaultConstructionError*(c: PContext, t: PType, info: TLineInfo)
proc computeRequiresInit*(c: PContext, t: PType): bool
proc tryExpr*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc tryConstExpr*(c: PContext, n: PNode): PNode
proc semOperand*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc semOverloadedCall*(c: PContext, n, nOrig: PNode,
                       filter: TSymKinds, flags: TExprFlags): PNode
proc semTypeNode*(c: PContext, n: PNode, prev: PType): PType
proc semInferredLambda*(c: PContext, pt: TIdTable, n: PNode): PNode
proc generateInstance*(c: PContext, fn: PSym, pt: TIdTable, info: TLineInfo): PSym
proc semProcAux*(c: PContext, n: PNode, kind: TSymKind,
                validPragmas: TSpecialWords, flags: TExprFlags = {}): PNode

import importer, sigmatch, vm, suggest

proc newSymS*(kind: TSymKind, n: PNode, c: PContext): PSym = # semgnrc, semtypes, semexprs, semexprs/semmagic
  result = newSym(kind, considerQuotedIdent(c, n), nextSymId c.idgen, getCurrOwner(c), n.info)
  when defined(nimsuggest):
    suggestDecl(c, n, result)

proc newSymG*(kind: TSymKind, n: PNode, c: PContext): PSym =
  # like newSymS, but considers gensym'ed symbols
  if n.kind == nkSym:
    # and sfGenSym in n.sym.flags:
    result = n.sym
    if result.kind notin {kind, skTemp}:
      localError(c.config, n.info, "cannot use symbol of kind '$1' as a '$2'" %
        [result.kind.toHumanStr, kind.toHumanStr])
    when false:
      if sfGenSym in result.flags and result.kind notin {skTemplate, skMacro, skParam}:
        # declarative context, so produce a fresh gensym:
        result = copySym(result)
        result.ast = n.sym.ast
        put(c.p, n.sym, result)
    # when there is a nested proc inside a template, semtmpl
    # will assign a wrong owner during the first pass over the
    # template; we must fix it here: see #909
    result.owner = getCurrOwner(c)
  else:
    result = newSym(kind, considerQuotedIdent(c, n), nextSymId c.idgen, getCurrOwner(c), n.info)
  #if kind in {skForVar, skLet, skVar} and result.owner.kind == skModule:
  #  incl(result.flags, sfGlobal)
  when defined(nimsuggest):
    suggestDecl(c, n, result)

proc semIdentVis*(c: PContext, kind: TSymKind, n: PNode,
                 allowed: TSymFlags): PSym =
  # identifier with visibility
  if n.kind == nkPostfix:
    if n.len == 2:
      # for gensym'ed identifiers the identifier may already have been
      # transformed to a symbol and we need to use that here:
      result = newSymG(kind, n[1], c)
      var v = considerQuotedIdent(c, n[0])
      if sfExported in allowed and v.id == ord(wStar):
        incl(result.flags, sfExported)
      else:
        if not (sfExported in allowed):
          localError(c.config, n[0].info, errXOnlyAtModuleScope % "export")
        else:
          localError(c.config, n[0].info, errInvalidVisibilityX % renderTree(n[0]))
    else:
      illFormedAst(n, c.config)
  else:
    result = newSymG(kind, n, c)

import hlo, seminst, semcall, semtypes, semstmts, semexprs

proc semStmt(c: PContext, n: PNode; flags: TExprFlags): PNode = semstmts.semStmt(c, n, flags)
proc semParamList(c: PContext, n, genericParams: PNode, s: PSym) = semstmts.semParamList(c, n, genericParams, s)
proc semTemplateExpr(c: PContext, n: PNode, s: PSym, flags: TExprFlags = {}): PNode = semexprs.semTemplateExpr(c, n, s, flags)
proc semExpr(c: PContext, n: PNode, flags: TExprFlags = {}): PNode = semexprs.semExpr(c, n, flags)
proc semExprNoDeref(c: PContext, n: PNode, flags: TExprFlags = {}): PNode = semexprs.semExprNoDeref(c, n, flags)
proc semExprWithType(c: PContext, n: PNode, flags: TExprFlags = {}): PNode = semexprs.semExprWithType(c, n, flags)
proc semWhen(c: PContext, n: PNode, semCheck: bool = true): PNode = semexprs.semWhen(c, n, semCheck)
proc semDirectOp(c: PContext, n: PNode, flags: TExprFlags): PNode = semexprs.semDirectOp(c, n, flags)
proc semExprNoType(c: PContext, n: PNode): PNode = semexprs.semExprNoType(c, n)
proc semProcBody(c: PContext, n: PNode): PNode = semexprs.semProcBody(c, n)
proc semOpAux(c: PContext, n: PNode) = semexprs.semOpAux(c, n)
proc defaultConstructionError(c: PContext, t: PType, info: TLineInfo) = semexprs.defaultConstructionError(c, t, info)
proc computeRequiresInit(c: PContext, t: PType): bool = semexprs.computeRequiresInit(c, t)
proc tryExpr*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode = semexprs.tryExpr(c, n, flags)
proc tryConstExpr*(c: PContext, n: PNode): PNode = semexprs.tryConstExpr(c, n)
proc semOperand*(c: PContext, n: PNode, flags: TExprFlags = {}): PNode = semexprs.semOperand(c, n, flags)
proc semOverloadedCall*(c: PContext, n, nOrig: PNode,
                       filter: TSymKinds, flags: TExprFlags): PNode = semcall.semOverloadedCall(c, n, nOrig, filter, flags)
proc semTypeNode*(c: PContext, n: PNode, prev: PType): PType = semtypes.semTypeNode(c, n, prev)
proc semInferredLambda*(c: PContext, pt: TIdTable, n: PNode): PNode = semstmts.semInferredLambda(c, pt, n)
proc generateInstance*(c: PContext, fn: PSym, pt: TIdTable, info: TLineInfo): PSym = seminst.generateInstance(c, fn, pt, info)
proc semProcAux*(c: PContext, n: PNode, kind: TSymKind,
                validPragmas: TSpecialWords, flags: TExprFlags = {}): PNode = semstmts.semProcAux(c, n, kind, validPragmas, flags)

proc fitNodePostMatch(c: PContext, formal: PType, arg: PNode): PNode =
  let x = arg.skipConv
  if x.kind in {nkPar, nkTupleConstr, nkCurly} and formal.kind != tyUntyped:
    changeType(c, x, formal, check=true)
  result = arg
  result = skipHiddenSubConv(result, c.graph, c.idgen)

proc fitNode(c: PContext, formal: PType, arg: PNode; info: TLineInfo): PNode =
  if arg.typ.isNil:
    localError(c.config, arg.info, "expression has no type: " &
               renderTree(arg, {renderNoComments}))
    # error correction:
    result = copyTree(arg)
    result.typ = formal
  else:
    result = indexTypesMatch(c, formal, arg.typ, arg)
    if result == nil:
      typeMismatch(c.config, info, formal, arg.typ, arg)
      # error correction:
      result = copyTree(arg)
      result.typ = formal
    else:
      result = fitNodePostMatch(c, formal, result)

when false:
  proc createEvalContext(c: PContext, mode: TEvalMode): PEvalContext =
    result = newEvalContext(c.module, mode)
    result.getType = proc (n: PNode): PNode =
      result = tryExpr(c, n)
      if result == nil:
        result = newSymNode(errorSym(c, n))
      elif result.typ == nil:
        result = newSymNode(getSysSym"void")
      else:
        result.typ = makeTypeDesc(c, result.typ)

    result.handleIsOperator = proc (n: PNode): PNode =
      result = isOpImpl(c, n)

proc hasCycle(n: PNode): bool =
  incl n.flags, nfNone
  for i in 0..<n.safeLen:
    if nfNone in n[i].flags or hasCycle(n[i]):
      result = true
      break
  excl n.flags, nfNone

proc fixupTypeAfterEval(c: PContext, evaluated, eOrig: PNode): PNode =
  # recompute the types as 'eval' isn't guaranteed to construct types nor
  # that the types are sound:
  when true:
    if eOrig.typ.kind in {tyUntyped, tyTyped, tyTypeDesc}:
      result = semExprWithType(c, evaluated)
    else:
      result = evaluated
      let expectedType = eOrig.typ.skipTypes({tyStatic})
      if hasCycle(result):
        result = localErrorNode(c, eOrig, "the resulting AST is cyclic and cannot be processed further")
      else:
        semmacrosanity.annotateType(result, expectedType, c.config)
  else:
    result = semExprWithType(c, evaluated)
    #result = fitNode(c, e.typ, result) inlined with special case:
    let arg = result
    result = indexTypesMatch(c, eOrig.typ, arg.typ, arg)
    if result == nil:
      result = arg
      # for 'tcnstseq' we support [] to become 'seq'
      if eOrig.typ.skipTypes(abstractInst).kind == tySequence and
         isArrayConstr(arg):
        arg.typ = eOrig.typ

proc semConstExpr(c: PContext, n: PNode): PNode =
  var e = semExprWithType(c, n)
  if e == nil:
    localError(c.config, n.info, errConstExprExpected)
    return n
  result = getConstExpr(c.module, e, c.idgen, c.graph)
  if result == nil:
    #if e.kind == nkEmpty: globalError(n.info, errConstExprExpected)
    result = evalConstExpr(c.module, c.idgen, c.graph, e)
    if result == nil or result.kind == nkEmpty:
      if e.info != n.info:
        pushInfoContext(c.config, n.info)
        localError(c.config, e.info, errConstExprExpected)
        popInfoContext(c.config)
      else:
        localError(c.config, e.info, errConstExprExpected)
      # error correction:
      result = e
    else:
      result = fixupTypeAfterEval(c, result, e)

proc semMacroExpr(c: PContext, n, nOrig: PNode, sym: PSym,
                  flags: TExprFlags = {}): PNode =
  rememberExpansion(c, nOrig.info, sym)
  pushInfoContext(c.config, nOrig.info, sym.detailedInfo)

  let info = getCallLineInfo(n)
  markUsed(c, info, sym)
  onUse(info, sym)
  if sym == c.p.owner:
    globalError(c.config, info, "recursive dependency: '$1'" % sym.name.s)

  let genericParams = sym.ast[genericParamsPos].len
  let suppliedParams = max(n.safeLen - 1, 0)

  if suppliedParams < genericParams:
    globalError(c.config, info, errMissingGenericParamsForTemplate % n.renderTree)

  #if c.evalContext == nil:
  #  c.evalContext = c.createEvalContext(emStatic)
  result = evalMacroCall(c.module, c.idgen, c.graph, c.templInstCounter, n, nOrig, sym)
  if efNoSemCheck notin flags:
    result = semAfterMacroCall(c, n, result, sym, flags)
  if c.config.macrosToExpand.hasKey(sym.name.s):
    message(c.config, nOrig.info, hintExpandMacro, renderTree(result))
  result = wrapInComesFrom(nOrig.info, sym, result)
  popInfoContext(c.config)

proc forceBool(c: PContext, n: PNode): PNode =
  result = fitNode(c, getSysType(c.graph, n.info, tyBool), n, n.info)
  if result == nil: result = n

proc semConstBoolExpr(c: PContext, n: PNode): PNode =
  result = forceBool(c, semConstExpr(c, n))
  if result.kind != nkIntLit:
    localError(c.config, n.info, errConstExprExpected)

proc addCodeForGenerics(c: PContext, n: PNode) =
  for i in c.lastGenericIdx..<c.generics.len:
    var prc = c.generics[i].inst.sym
    if prc.kind in {skProc, skFunc, skMethod, skConverter} and prc.magic == mNone:
      if prc.ast == nil or prc.ast[bodyPos] == nil:
        internalError(c.config, prc.info, "no code for " & prc.name.s)
      else:
        n.add prc.ast
  c.lastGenericIdx = c.generics.len

when not defined(nimHasSinkInference):
  {.pragma: nosinks.}

proc myOpen(graph: ModuleGraph; module: PSym; idgen: IdGenerator): PPassContext {.nosinks.} =
  var c = newContext(graph, module)
  c.idgen = idgen
  c.enforceVoidContext = newType(tyTyped, nextTypeId(idgen), nil)
  c.voidType = newType(tyVoid, nextTypeId(idgen), nil)

  if c.p != nil: internalError(graph.config, module.info, "sem.myOpen")
  c.instTypeBoundOp = sigmatch.instTypeBoundOp
  c.templInstCounter = new int

  pushProcCon(c, module)
  pushOwner(c, c.module)

  c.moduleScope = openScope(c)
  c.moduleScope.addSym(module) # a module knows itself

  if sfSystemModule in module.flags:
    graph.systemModule = module
  c.topLevelScope = openScope(c)
  result = c

proc isImportSystemStmt(g: ModuleGraph; n: PNode): bool =
  if g.systemModule == nil: return false
  case n.kind
  of nkImportStmt:
    for x in n:
      if x.kind == nkIdent:
        let f = checkModuleName(g.config, x, false)
        if f == g.systemModule.info.fileIndex:
          return true
  of nkImportExceptStmt, nkFromStmt:
    if n[0].kind == nkIdent:
      let f = checkModuleName(g.config, n[0], false)
      if f == g.systemModule.info.fileIndex:
        return true
  else: discard

proc isEmptyTree(n: PNode): bool =
  case n.kind
  of nkStmtList:
    for it in n:
      if not isEmptyTree(it): return false
    result = true
  of nkEmpty, nkCommentStmt: result = true
  else: result = false

proc semStmtAndGenerateGenerics(c: PContext, n: PNode): PNode =
  if c.topStmts == 0 and not isImportSystemStmt(c.graph, n):
    if sfSystemModule notin c.module.flags and not isEmptyTree(n):
      assert c.graph.systemModule != nil
      c.moduleScope.addSym c.graph.systemModule # import the "System" identifier
      importAllSymbols(c, c.graph.systemModule)
      inc c.topStmts
  else:
    inc c.topStmts
  if sfNoForward in c.module.flags:
    result = semAllTypeSections(c, n)
  else:
    result = n
  result = semStmt(c, result, {})
  when false:
    # Code generators are lazy now and can deal with undeclared procs, so these
    # steps are not required anymore and actually harmful for the upcoming
    # destructor support.
    # BUGFIX: process newly generated generics here, not at the end!
    if c.lastGenericIdx < c.generics.len:
      var a = newNodeI(nkStmtList, n.info)
      addCodeForGenerics(c, a)
      if a.len > 0:
        # a generic has been added to `a`:
        if result.kind != nkEmpty: a.add result
        result = a
  result = hloStmt(c, result)
  if c.config.cmd == cmdInteractive and not isEmptyType(result.typ):
    result = buildEchoStmt(c, result)
  if c.config.cmd == cmdIdeTools:
    appendToModule(c.module, result)
  trackStmt(c, c.module, result, isTopLevel = true)

proc recoverContext(c: PContext) =
  # clean up in case of a semantic error: We clean up the stacks, etc. This is
  # faster than wrapping every stack operation in a 'try finally' block and
  # requires far less code.
  c.currentScope = c.topLevelScope
  while getCurrOwner(c).kind != skModule: popOwner(c)
  while c.p != nil and c.p.owner.kind != skModule: c.p = c.p.next

proc myProcess(context: PPassContext, n: PNode): PNode {.nosinks.} =
  var c = PContext(context)
  # no need for an expensive 'try' if we stop after the first error anyway:
  if c.config.errorMax <= 1:
    result = semStmtAndGenerateGenerics(c, n)
  else:
    let oldContextLen = msgs.getInfoContextLen(c.config)
    let oldInGenericInst = c.inGenericInst
    try:
      result = semStmtAndGenerateGenerics(c, n)
    except ERecoverableError, ESuggestDone:
      recoverContext(c)
      c.inGenericInst = oldInGenericInst
      msgs.setInfoContextLen(c.config, oldContextLen)
      if getCurrentException() of ESuggestDone:
        c.suggestionsMade = true
        result = nil
      else:
        result = newNodeI(nkEmpty, n.info)
      #if c.config.cmd == cmdIdeTools: findSuggest(c, n)
  storeRodNode(c, result)

proc reportUnusedModules(c: PContext) =
  for i in 0..high(c.unusedImports):
    if sfUsed notin c.unusedImports[i][0].flags:
      message(c.config, c.unusedImports[i][1], warnUnusedImportX, c.unusedImports[i][0].name.s)

proc myClose(graph: ModuleGraph; context: PPassContext, n: PNode): PNode =
  var c = PContext(context)
  if c.config.cmd == cmdIdeTools and not c.suggestionsMade:
    suggestSentinel(c)
  closeScope(c)         # close module's scope
  rawCloseScope(c)      # imported symbols; don't check for unused ones!
  reportUnusedModules(c)
  result = newNode(nkStmtList)
  if n != nil:
    internalError(c.config, n.info, "n is not nil") #result := n;
  addCodeForGenerics(c, result)
  if c.module.ast != nil:
    result.add(c.module.ast)
  popOwner(c)
  popProcCon(c)
  sealRodFile(c)

const semPass* = makePass(myOpen, myProcess, myClose, isFrontend = true)
