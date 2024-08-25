import Lean

open Lean Elab Meta PrettyPrinter Delaborator AppImplicitArg SubExpr Parser

/-!
This file defines utilities to delaborate Lean expressions in a way suitable for export to SMT solvers.
-/

/-- This elaborator allows function applications to be written in uncurried style
    (e.g., `Nat.add(1, 2)` instead of the usual `Nat.add 1 2`). -/
elab (name := uncurried) f:ident noWs "(" args:term,* ")" : term => do
  let args ← args.getElems.mapM (Term.elabTerm · none)
  mkAppM f.getId args

#eval Nat.add((1 : Nat), (2 : Nat))

def Syntax.mkUncurriedApp (fnStx : Term) (argsStx : Array Term) : Term :=
  if argsStx.isEmpty then
    fnStx
  else
    ⟨.node .none `uncurried #[
        fnStx.raw,
        .node .none `group #[],
        .atom .none "(",
        .node .none `null (mkSepArray argsStx (.atom .none ",")),
        .atom .none ")"
      ]⟩

section

/-!

The code in this section is a slight modification of code from `Lean/PrettyPrinter/Delaborator/Builtins.lean` in the Lean4 source.
This is essentially a re-implementation of `delabAppImplicitCore` using `Syntax.mkUncurriedApp` instead of `Syntax.mkApp`.

-/

#check delabAppImplicitCore

/-- Strips parent projections from `s`. Assumes that the current SubExpr is the same as the one used when delaborating `s`. -/
private partial def stripParentProjections (s : Term) : DelabM Term :=
  match s with
  | `($x.$f:ident) => do
    if let some field ← try parentProj? false (← getExpr) catch _ => pure none then
      if f.getId == field then
        withAppArg <| stripParentProjections x
      else
        return s
    else
      return s
  | _ => return s

/-- This is a modification of the implicit application delaborator defined in `Lean/PrettyPrinter/Delaborator/Builtins.lean`. -/
def delabAppImplicitCore (unexpand : Bool) (numArgs : Nat) (delabHead : Delab) (paramKinds : Array ParamKind) : Delab := do
  let unexpand ← pure unexpand
    <&&> withBoundedAppFn numArgs do pure (← getExpr).consumeMData.isConst <&&> not <$> withMDatasOptions (getPPOption getPPUniverses)
  let field? ←
    if ← pure unexpand <&&> getPPOption getPPFieldNotation <&&> not <$> getPPOption getPPAnalysisNoDot then
      appFieldNotationCandidate?
    else
      pure none
  let (fnStx, args) ←
    withBoundedAppFnArgs numArgs
      (do return ((← delabHead), Array.mkEmpty numArgs))
      (fun (fnStx, args) => do
        let idx := args.size
        let arg ← mkArg (numArgs - idx - 1) paramKinds[idx]!
        return (fnStx, args.push arg))

  -- App unexpanders
  if ← pure unexpand <&&> getPPOption getPPNotation then
    -- Try using an app unexpander for a prefix of the arguments.
    if let some stx ← (some <$> tryAppUnexpanders fnStx args) <|> pure none then
      return stx

  let stx := Syntax.mkUncurriedApp fnStx (args.filterMap (TSyntax.mk <$> ·.syntax?))

  -- -- Structure instance notation
  -- if ← pure (unexpand && args.all (·.canUnexpand)) <&&> getPPOption getPPStructureInstances then
  --   -- Try using the structure instance unexpander.
  --   if let some stx ← (some <$> unexpandStructureInstance stx) <|> pure none then
  --     return stx

  -- -- Field notation
  -- if let some (fieldIdx, field) := field? then
  --   if fieldIdx < args.size then
  --     let obj? : Option Term ← do
  --       let arg := args[fieldIdx]!
  --       if let .regular s := arg then
  --         withNaryArg fieldIdx <| some <$> stripParentProjections s
  --       else
  --         pure none
  --     if let some obj := obj? then
  --       let isFirst := args[0:fieldIdx].all (· matches .skip)
  --       -- Clear the `obj` argument from `args`.
  --       let args' := args.set! fieldIdx .skip
  --       let mut head : Term ← `($obj.$(mkIdent field))
  --       if isFirst then
  --         -- If the object is the first argument (after some implicit arguments),
  --         -- we can annotate `obj.field` with the prefix of the application
  --         -- that includes all the implicit arguments immediately before and after `obj`.
  --         let objArity := args'.findIdx? (fun a => !(a matches .skip)) |>.getD args'.size
  --         head ← withBoundedAppFn (numArgs - objArity) <| annotateTermInfo <| head
  --       return Syntax.mkUncurriedApp head (args'.filterMap (TSyntax.mk <$> ·.syntax?)) -- the syntax here is uncurried application instead of the usual curried syntax

  -- Normal application
  return stx
where
  mkNamedArg (name : Name) : DelabM AppImplicitArg :=
    return .named <| ← `(Parser.Term.namedArgument| ($(mkIdent name) := $(← delab)))
  /--
  Delaborates the current argument.
  The argument `remainingArgs` is the number of arguments in the application after this one.
  -/
  mkArg (remainingArgs : Nat) (param : ParamKind) : DelabM AppImplicitArg := do
    let arg ← getExpr
    if ← getPPOption getPPAnalysisSkip then return .skip
    else if ← getPPOption getPPAnalysisHole then return .regular (← `(_))
    else if ← getPPOption getPPAnalysisNamedArg then
      mkNamedArg param.name
    else if param.defVal.isSome && remainingArgs == 0 && param.defVal.get! == arg then
      -- Assumption: `useAppExplicit` has already detected whether it is ok to omit this argument
      return .skip
    else if param.bInfo.isExplicit then
      return .regular (← delab)
    else if ← pure (param.name == `motive) <&&> shouldShowMotive arg (← getOptions) then
      mkNamedArg param.name
    else
      return .skip
  /--
  Runs the given unexpanders, returning the resulting syntax if any are applicable, and otherwise fails.
  -/
  tryUnexpand (fs : List Unexpander) (stx : Syntax) : DelabM Syntax := do
    let ref ← getRef
    fs.firstM fun f =>
      match f stx |>.run ref |>.run () with
      | EStateM.Result.ok stx _ => return stx
      | _ => failure
  /--
  If the expression is a candidate for app unexpanders,
  try applying an app unexpander using some prefix of the arguments, longest prefix first.
  This function makes sure that the unexpanded syntax is annotated and given TermInfo so that it is hoverable in the InfoView.
  -/
  tryAppUnexpanders (fnStx : Term) (args : Array AppImplicitArg) : Delab := do
    let .const c _ := (← getExpr).getAppFn.consumeMData | unreachable!
    let fs := appUnexpanderAttribute.getValues (← getEnv) c
    if fs.isEmpty then failure
    let rec go (i : Nat) (implicitArgs : Nat) (argStxs : Array Syntax) : DelabM Term := do
      match i with
      | 0 =>
        let stx ← tryUnexpand fs fnStx
        return Syntax.mkUncurriedApp (← annotateTermInfo ⟨stx⟩) (args.filterMap (TSyntax.mk <$> ·.syntax?))
      | i' + 1 =>
        if args[i']!.syntax?.isSome then
          (do let stx ← tryUnexpand fs <| Syntax.mkUncurriedApp fnStx (argStxs.map TSyntax.mk)
              let argStxs' := args.extract i args.size |>.filterMap (TSyntax.mk <$> ·.syntax?)
              return Syntax.mkUncurriedApp (← annotateTermInfo ⟨stx⟩) argStxs')
          <|> withBoundedAppFn (implicitArgs + 1) (go i' 0 argStxs.pop)
        else
          go i' (implicitArgs + 1) argStxs
    let maxUnexpand := args.findIdx? (!·.canUnexpand) |>.getD args.size
    withBoundedAppFn (args.size - maxUnexpand) <|
      go maxUnexpand 0 (args.extract 0 maxUnexpand |>.filterMap (·.syntax?))

/--
Delaborates applications. Removes up to `maxArgs` arguments to form the "head" of the application.
* `delabHead` is a delaborator to use for the head of the expression.
  It is passed whether the result needs to have `@` inserted.
* If `unexpand` is true, then allow unexpanders and field notation.
  This should likely be set to `false` except in the main `delabApp` delaborator.

Propagates `pp.tagAppFns` into the head for `delabHead`.
-/
def delabAppCore (maxArgs : Nat) (delabHead : (insertExplicit : Bool) → Delab) (unexpand : Bool) : Delab := do
  let tagAppFn ← getPPOption getPPTagAppFns
  let delabHead' (insertExplicit : Bool) : Delab := withOptionAtCurrPos `pp.tagAppFns tagAppFn (delabHead insertExplicit)
  let e ← getExpr
  let fn := e.getBoundedAppFn maxArgs
  let args := e.getBoundedAppArgs maxArgs
  let paramKinds ← getParamKinds fn args
  _root_.delabAppImplicitCore (unexpand := unexpand) args.size (delabHead' false) paramKinds

register_option pp.uncurriedApp : Bool := {
  defValue := false
  descr := "If true, use uncurried function application syntax with parentheses and commas between arguments."
}

/--
Default delaborator for applications.
-/
@[delab app]
def delabApp : Delab := do
  if (← getBoolOption `pp.uncurriedApp) then
    let delabAppFn (insertExplicit : Bool) : Delab := do
      let stx ← if (← getExpr).consumeMData.isConst then withMDatasOptions delabConst else delab
      if insertExplicit && !stx.raw.isOfKind ``Lean.Parser.Term.explicit then `(@$stx) else pure stx
    _root_.delabAppCore (← getExpr).getAppNumArgs delabAppFn (unexpand := true)
  else
    failure

end

set_option pp.funBinderTypes true
set_option pp.tagAppFns true
set_option pp.analyze.typeAscriptions true
set_option pp.proofs.withType false
