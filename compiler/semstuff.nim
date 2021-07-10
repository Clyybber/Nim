import
  ast, astalgo, options, msgs, idents, renderer, types,
  magicsys, semdata, modulegraphs, lineinfos, cgmeth

import semtypes

# Common dependencies by semstmts and semexprs, name tbd :p

proc hasObjParam*(s: PSym): bool =
  var t = s.typ
  for col in 1..<t.len:
    if skipTypes(t[col], skipPtrs).kind == tyObject:
      return true

proc finishMethod*(c: PContext, s: PSym) =
  if hasObjParam(s):
    methodDef(c.graph, c.idgen, s)

proc prevDestructor*(c: PContext; prevOp: PSym; obj: PType; info: TLineInfo) =
  var msg = "cannot bind another '" & prevOp.name.s & "' to: " & typeToString(obj)
  if sfOverriden notin prevOp.flags:
    msg.add "; previous declaration was constructed here implicitly: " & (c.config $ prevOp.info)
  else:
    msg.add "; previous declaration was here: " & (c.config $ prevOp.info)
  localError(c.config, info, errGenerated, msg)

proc canonType*(c: PContext, t: PType): PType =
  if t.kind == tySequence:
    result = c.graph.sysTypes[tySequence]
  else:
    result = t

proc bindTypeHook*(c: PContext; s: PSym; n: PNode; op: TTypeAttachedOp) =
  let t = s.typ
  var noError = false
  let cond = if op == attachedDestructor:
               t.len == 2 and t[0] == nil and t[1].kind == tyVar
             else:
               t.len >= 2 and t[0] == nil

  if cond:
    var obj = t[1].skipTypes({tyVar})
    while true:
      incl(obj.flags, tfHasAsgn)
      if obj.kind in {tyGenericBody, tyGenericInst}: obj = obj.lastSon
      elif obj.kind == tyGenericInvocation: obj = obj[0]
      else: break
    if obj.kind in {tyObject, tyDistinct, tySequence, tyString}:
      obj = canonType(c, obj)
      let ao = getAttachedOp(c.graph, obj, op)
      if ao == s:
        discard "forward declared destructor"
      elif ao.isNil and tfCheckedForDestructor notin obj.flags:
        setAttachedOp(c.graph, c.module.position, obj, op, s)
      else:
        prevDestructor(c, ao, obj, n.info)
      noError = true
      if obj.owner.getModule != s.getModule:
        localError(c.config, n.info, errGenerated,
          "type bound operation `" & s.name.s & "` can be defined only in the same module with its type (" & obj.typeToString() & ")")
  if not noError and sfSystemModule notin s.owner.flags:
    localError(c.config, n.info, errGenerated,
      "signature for '" & s.name.s & "' must be proc[T: object](x: var T)")
  incl(s.flags, sfUsed)
  incl(s.flags, sfOverriden)

proc hasUnresolvedParams*(n: PNode; flags: TExprFlags): bool =
  result = tfUnresolved in n.typ.flags
  when false:
    case n.kind
    of nkSym:
      result = isGenericRoutineStrict(n.sym)
    of nkSymChoices:
      for ch in n:
        if hasUnresolvedParams(ch, flags):
          return true
      result = false
    else:
      result = false
    if efOperand in flags:
      if tfUnresolved notin n.typ.flags:
        result = false

const
  skipForDiscardable = {nkIfStmt, nkIfExpr, nkCaseStmt, nkOfBranch,
    nkElse, nkStmtListExpr, nkTryStmt, nkFinally, nkExceptBranch,
    nkElifBranch, nkElifExpr, nkElseExpr, nkBlockStmt, nkBlockExpr,
    nkHiddenStdConv, nkHiddenDeref}

proc implicitlyDiscardable*(n: PNode): bool =
  var n = n
  while n.kind in skipForDiscardable: n = n.lastSon
  result = n.kind in nkLastBlockStmts or
           (isCallExpr(n) and n[0].kind == nkSym and
           sfDiscardable in n[0].sym.flags)

proc discardCheck*(c: PContext, result: PNode, flags: TExprFlags) =
  if c.matchedConcept != nil or efInTypeof in flags: return

  if result.typ != nil and result.typ.kind notin {tyTyped, tyVoid}:
    if implicitlyDiscardable(result):
      var n = newNodeI(nkDiscardStmt, result.info, 1)
      n[0] = result
    elif result.typ.kind != tyError and c.config.cmd != cmdInteractive:
      var n = result
      while n.kind in skipForDiscardable: n = n.lastSon
      var s = "expression '" & $n & "' is of type '" &
          result.typ.typeToString & "' and has to be used (or discarded)"
      if result.info.line != n.info.line or
          result.info.fileIndex != n.info.fileIndex:
        s.add "; start of expression here: " & c.config$result.info
      if result.typ.kind == tyProc:
        s.add "; for a function call use ()"
      localError(c.config, n.info, s)

proc makeDeref*(n: PNode): PNode =
  var t = n.typ
  if t.kind in tyUserTypeClasses and t.isResolvedUserTypeClass:
    t = t.lastSon
  t = skipTypes(t, {tyGenericInst, tyAlias, tySink, tyOwned})
  result = n
  if t.kind in {tyVar, tyLent}:
    result = newNodeIT(nkHiddenDeref, n.info, t[0])
    result.add n
    t = skipTypes(t[0], {tyGenericInst, tyAlias, tySink, tyOwned})
  while t.kind in {tyPtr, tyRef}:
    var a = result
    let baseTyp = t.lastSon
    result = newNodeIT(nkHiddenDeref, n.info, baseTyp)
    result.add a
    t = skipTypes(baseTyp, {tyGenericInst, tyAlias, tySink, tyOwned})

proc swapResult(n: PNode, sRes: PSym, dNode: PNode) =
  ## Swap nodes that are (skResult) symbols to d(estination)Node.
  for i in 0..<n.safeLen:
    if n[i].kind == nkSym and n[i].sym == sRes:
        n[i] = dNode
    swapResult(n[i], sRes, dNode)

proc addResult*(c: PContext, n: PNode, t: PType, owner: TSymKind) =
  template genResSym(s) =
    var s = newSym(skResult, getIdent(c.cache, "result"), nextSymId c.idgen,
                   getCurrOwner(c), n.info)
    s.typ = t
    incl(s.flags, sfUsed)

  if owner == skMacro or t != nil:
    if n.len > resultPos and n[resultPos] != nil:
      if n[resultPos].sym.kind != skResult:
        localError(c.config, n.info, "incorrect result proc symbol")
      if n[resultPos].sym.owner != getCurrOwner(c):
        # re-write result with new ownership, and re-write the proc accordingly
        let sResSym = n[resultPos].sym
        genResSym(s)
        n[resultPos] = newSymNode(s)
        swapResult(n, sResSym, n[resultPos])
      c.p.resultSym = n[resultPos].sym
    else:
      genResSym(s)
      c.p.resultSym = s
      n.add newSymNode(c.p.resultSym)
    addParamOrResult(c, c.p.resultSym, owner)

proc maybeAddResult*(c: PContext, s: PSym, n: PNode) =
  if s.kind == skMacro:
    let resultType = sysTypeFromName(c.graph, n.info, "NimNode")
    addResult(c, n, resultType, s.kind)
  elif s.typ[0] != nil and not isInlineIterator(s.typ):
    addResult(c, n, s.typ[0], s.kind)

proc activate*(c: PContext, n: PNode) =
  # XXX: This proc is part of my plan for getting rid of
  # forward declarations. stay tuned.
  when false:
    # well for now it breaks code ...
    case n.kind
    of nkLambdaKinds:
      discard semLambda(c, n, {})
    of nkCallKinds:
      for i in 1..<n.len: activate(c, n[i])
    else:
      discard

