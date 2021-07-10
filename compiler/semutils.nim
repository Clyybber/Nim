import
  ast, astalgo, strutils, msgs, idents, renderer, types,
  semdata, modulegraphs, lineinfos, magicsys, typeallowed

const
  errImplOfXNotAllowed* = "implementation of '$1' is not allowed"

  errTypeMismatch* = "type mismatch: got <"
  errButExpected* = "but expected one of:"
  errUndeclaredField* = "undeclared field: '$1'"
  errUndeclaredRoutine* = "attempting to call undeclared routine: '$1'"
  errBadRoutine* = "attempting to call routine: '$1'$2"
  errAmbiguousCallXYZ* = "ambiguous call; both $1 and $2 match for: $3"

  errMissingGenericParamsForTemplate* = "'$1' has unspecified generic parameters"
  errFloatToString* = "cannot convert '$1' to '$2'"
  errConstExprExpected* = "constant expression expected"

  errExprXHasNoType* = "expression '$1' has no type (or is ambiguous)"
  errXExpectsTypeOrValue* = "'$1' expects a type or value"
  errVarForOutParamNeededX* = "for a 'var' type a variable needs to be passed; but '$1' is immutable"
  errXStackEscape* = "address of '$1' may not escape its stack frame"
  errExprHasNoAddress* = "expression has no address"
  errCannotInterpretNodeX* = "cannot evaluate '$1'"
  errNamedExprExpected* = "named expression expected"
  errNamedExprNotAllowed* = "named expression not allowed here"
  errFieldInitTwice* = "field initialized twice: '$1'"
  errUndeclaredFieldX = "undeclared field: '$1'"

  errNoSymbolToBorrowFromFound* = "no symbol to borrow from found"
  errDiscardValueX* = "value of type '$1' has to be used (or discarded)"
  errInvalidDiscard* = "statement returns no value that can be discarded"
  errInvalidControlFlowX* = "invalid control flow: $1"
  errSelectorMustBeOfCertainTypes* = "selector must be of an ordinal type, float or string"
  errExprCannotBeRaised* = "only a 'ref object' can be raised"
  errBreakOnlyInLoop = "'break' only allowed in loop construct"
  errExceptionAlreadyHandled* = "exception already handled"
  errYieldNotAllowedHere* = "'yield' only allowed in an iterator"
  errYieldNotAllowedInTryStmt = "'yield' cannot be used within 'try' in a non-inlined iterator"
  errInvalidNumberOfYieldExpr = "invalid number of 'yield' expressions"
  errCannotReturnExpr* = "current routine cannot return an expression"
  errGenericLambdaNotAllowed* = "A nested proc can have generic parameters only when " &
    "it is used as an operand to another routine and the types " &
    "of the generic paramers can be inferred from the expected signature."
  errCannotInferTypeOfTheLiteral* = "cannot infer the type of the $1"
  errCannotInferReturnType* = "cannot infer the return type of '$1'"
  errCannotInferStaticParam = "cannot infer the value of the static param '$1'"
  errProcHasNoConcreteType* = "'$1' doesn't have a concrete type, due to unspecified generic parameters."
  errLetNeedsInit* = "'let' symbol requires an initialization"
  errThreadvarCannotInit* = "a thread var cannot be initialized explicitly; this would only run for the main thread"
  errImplOfXexpected* = "implementation of '$1' expected"
  errRecursiveDependencyX* = "recursive dependency: '$1'"
  errRecursiveDependencyIteratorX* = "recursion is not supported in iterators: '$1'"
  errPragmaOnlyInHeaderOfProcX* = "pragmas are only allowed in the header of a proc; redefinition of $1"

  errStringOrIdentNodeExpected* = "string or ident node expected"
  errStringLiteralExpected* = "string literal expected"
  errIntLiteralExpected* = "integer literal expected"
  errWrongNumberOfVariables* = "wrong number of variables"
  errInvalidOrderInEnumX* = "invalid order in enum '$1'"
  errOrdinalTypeExpected* = "ordinal type expected"
  errSetTooBig* = "set is too large"
  errBaseTypeMustBeOrdinal = "base type of a set must be an ordinal"
  errInheritanceOnlyWithNonFinalObjects* = "inheritance only works with non-final objects"
  errXExpectsOneTypeParam* = "'$1' expects one type parameter"
  errArrayExpectsTwoTypeParams* = "array expects two type parameters"
  errInvalidVisibilityX* = "invalid visibility: '$1'"
  errInitHereNotAllowed* = "initialization not allowed here"
  errXCannotBeAssignedTo* = "'$1' cannot be assigned to"
  errIteratorNotAllowed = "iterators can only be defined at the module's top level"
  errXNeedsReturnType* = "$1 needs a return type"
  errNoReturnTypeDeclared* = "no return type declared"
  errTIsNotAConcreteType* = "'$1' is not a concrete type"
  errTypeExpected* = "type expected"
  errXOnlyAtModuleScope* = "'$1' is only allowed at top level"
  errDuplicateCaseLabel* = "duplicate case label"
  errMacroBodyDependsOnGenericTypes* = "the macro body cannot be compiled, " &
    "because the parameter '$1' has a generic type"
  errIllegalRecursionInTypeX* = "illegal recursion in type '$1'"
  errNoGenericParamsAllowedForX* = "no generic parameters allowed for $1"
  errInOutFlagNotExtern* = "the '$1' modifier can be used only with imported types"

proc endsInNoReturn*(n: PNode): bool =
  # check if expr ends in raise exception or call of noreturn proc
  var it = n
  while it.kind in {nkStmtList, nkStmtListExpr} and it.len > 0:
    it = it.lastSon
  result = it.kind in nkLastBlockStmts or
    it.kind in nkCallKinds and it[0].kind == nkSym and sfNoReturn in it[0].sym.flags

proc isSelf*(t: PType): bool {.inline.} =
  ## is this the magical 'Self' type?
  t.kind == tyTypeDesc and tfPacked in t.flags

proc makeTypeDesc*(c: PContext, typ: PType): PType =
  if typ.kind == tyTypeDesc and not isSelf(typ):
    result = typ
  else:
    result = newTypeS(tyTypeDesc, c)
    incl result.flags, tfCheckedForDestructor
    result.addSonSkipIntLit(typ, c.idgen)

proc symFromType*(c: PContext; t: PType, info: TLineInfo): PSym =
  if t.sym != nil: return t.sym
  result = newSym(skType, getIdent(c.cache, "AnonType"), nextSymId c.idgen, t.owner, info)
  result.flags.incl sfAnon
  result.typ = t

proc symNodeFromType*(c: PContext, t: PType, info: TLineInfo): PNode =
  result = newSymNode(symFromType(c, t, info), info)
  result.typ = makeTypeDesc(c, t)

proc changeType*(c: PContext; n: PNode, newType: PType, check: bool) =
  case n.kind
  of nkCurly, nkBracket:
    for i in 0..<n.len:
      changeType(c, n[i], elemType(newType), check)
  of nkPar, nkTupleConstr:
    let tup = newType.skipTypes({tyGenericInst, tyAlias, tySink, tyDistinct})
    if tup.kind != tyTuple:
      if tup.kind == tyObject: return
      globalError(c.config, n.info, "no tuple type for constructor")
    elif n.len > 0 and n[0].kind == nkExprColonExpr:
      # named tuple?
      for i in 0..<n.len:
        var m = n[i][0]
        if m.kind != nkSym:
          globalError(c.config, m.info, "invalid tuple constructor")
          return
        if tup.n != nil:
          var f = getSymFromList(tup.n, m.sym.name)
          if f == nil:
            globalError(c.config, m.info, "unknown identifier: " & m.sym.name.s)
            return
          changeType(c, n[i][1], f.typ, check)
        else:
          changeType(c, n[i][1], tup[i], check)
    else:
      for i in 0..<n.len:
        changeType(c, n[i], tup[i], check)
        when false:
          var m = n[i]
          var a = newNodeIT(nkExprColonExpr, m.info, newType[i])
          a.add newSymNode(newType.n[i].sym)
          a.add m
          changeType(m, tup[i], check)
  of nkCharLit..nkUInt64Lit:
    if check and n.kind != nkUInt64Lit and not sameType(n.typ, newType):
      let value = n.intVal
      if value < firstOrd(c.config, newType) or value > lastOrd(c.config, newType):
        localError(c.config, n.info, "cannot convert " & $value &
                                         " to " & typeToString(newType))
  of nkFloatLit..nkFloat64Lit:
    if check and not floatRangeCheck(n.floatVal, newType):
      localError(c.config, n.info, errFloatToString % [$n.floatVal, typeToString(newType)])
  else: discard
  n.typ = newType

template commonTypeBegin*(): PType = PType(kind: tyUntyped) # semexprs, semstmts

proc commonType*(c: PContext; x, y: PType): PType =
  # new type relation that is used for array constructors,
  # if expressions, etc.:
  if x == nil: return x
  if y == nil: return y
  var a = skipTypes(x, {tyGenericInst, tyAlias, tySink})
  var b = skipTypes(y, {tyGenericInst, tyAlias, tySink})
  result = x
  if a.kind in {tyUntyped, tyNil}: result = y
  elif b.kind in {tyUntyped, tyNil}: result = x
  elif a.kind == tyTyped: result = a
  elif b.kind == tyTyped: result = b
  elif a.kind == tyTypeDesc:
    # turn any concrete typedesc into the abstract typedesc type
    if a.len == 0: result = a
    else:
      result = newType(tyTypeDesc, nextTypeId(c.idgen), a.owner)
      rawAddSon(result, newType(tyNone, nextTypeId(c.idgen), a.owner))
  elif b.kind in {tyArray, tySet, tySequence} and
      a.kind == b.kind:
    # check for seq[empty] vs. seq[int]
    let idx = ord(b.kind == tyArray)
    if a[idx].kind == tyEmpty: return y
  elif a.kind == tyTuple and b.kind == tyTuple and a.len == b.len:
    var nt: PType
    for i in 0..<a.len:
      let aEmpty = isEmptyContainer(a[i])
      let bEmpty = isEmptyContainer(b[i])
      if aEmpty != bEmpty:
        if nt.isNil:
          nt = copyType(a, nextTypeId(c.idgen), a.owner)
          copyTypeProps(c.graph, c.idgen.module, nt, a)

        nt[i] = if aEmpty: b[i] else: a[i]
    if not nt.isNil: result = nt
    #elif b[idx].kind == tyEmpty: return x
  elif a.kind == tyRange and b.kind == tyRange:
    # consider:  (range[0..3], range[0..4]) here. We should make that
    # range[0..4]. But then why is (range[0..4], 6) not range[0..6]?
    # But then why is (2,4) not range[2..4]? But I think this would break
    # too much code. So ... it's the same range or the base type. This means
    #  typeof(if b: 0 else 1) == int and not range[0..1]. For now. In the long
    # run people expect ranges to work properly within a tuple.
    if not sameType(a, b):
      result = skipTypes(a, {tyRange}).skipIntLit(c.idgen)
    when false:
      if a.kind != tyRange and b.kind == tyRange:
        # XXX This really needs a better solution, but a proper fix now breaks
        # code.
        result = a #.skipIntLit
      elif a.kind == tyRange and b.kind != tyRange:
        result = b #.skipIntLit
      elif a.kind in IntegralTypes and a.n != nil:
        result = a #.skipIntLit
  else:
    var k = tyNone
    if a.kind in {tyRef, tyPtr}:
      k = a.kind
      if b.kind != a.kind: return x
      # bug #7601, array construction of ptr generic
      a = a.lastSon.skipTypes({tyGenericInst})
      b = b.lastSon.skipTypes({tyGenericInst})
    if a.kind == tyObject and b.kind == tyObject:
      result = commonSuperclass(a, b)
      # this will trigger an error later:
      if result.isNil or result == a: return x
      if result == b: return y
      # bug #7906, tyRef/tyPtr + tyGenericInst of ref/ptr object ->
      # ill-formed AST, no need for additional tyRef/tyPtr
      if k != tyNone and x.kind != tyGenericInst:
        let r = result
        result = newType(k, nextTypeId(c.idgen), r.owner)
        result.addSonSkipIntLit(r, c.idgen)

proc commonType*(c: PContext; x: PType, y: PNode): PType =
  # ignore exception raising branches in case/if expressions
  if endsInNoReturn(y): return x
  commonType(c, x, y.typ)

proc typeAllowedCheck*(c: PContext; info: TLineInfo; typ: PType; kind: TSymKind;
                      flags: TTypeAllowedFlags = {}) =
  let t = typeAllowed(typ, kind, c, flags)
  if t != nil:
    var err: string
    if t == typ:
      err = "invalid type: '$1' for $2" % [typeToString(typ), toHumanStr(kind)]
      if kind in {skVar, skLet, skConst} and taIsTemplateOrMacro in flags:
        err &= ". Did you mean to call the $1 with '()'?" % [toHumanStr(typ.owner.kind)]
    else:
      err = "invalid type: '$1' in this context: '$2' for $3" % [typeToString(t),
              typeToString(typ), toHumanStr(kind)]
    localError(c.config, info, err)

proc paramsTypeCheck*(c: PContext, typ: PType) {.inline.} =
  typeAllowedCheck(c, typ.n.info, typ, skProc)

