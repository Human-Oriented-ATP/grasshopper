import Grasshopper.Theorems
import Grasshopper.UncurriedAppDelab
import Qq

section Auto

open Lean Elab Qq Meta Tactic

set_option linter.setOption false
set_option pp.funBinderTypes true
set_option pp.tagAppFns true
set_option pp.analyze.typeAscriptions true
set_option pp.proofs.withType false
set_option pp.sanitizeNames false

-- abbrev Qq.Quoted.render {α : Q(Type $u)} (e : Q($α)) : MetaM String := do
def Expr.render (e : Expr) : MetaM String :=
  let options : Options :=
    (.empty : Options)
    |>.insert `pp.funBinderTypes true
    |>.insert `pp.tagAppFns true
    |>.insert `pp.analyze.typeAscriptions true
    |>.insert `pp.proofs.withType false
    |>.insert `pp.sanitizeNames false
    |>.insert `pp.uncurriedApp true
  withOptions (options.mergeBy fun _ opt _ ↦ opt) <| do
    return toString (← ppExpr e) |>.splitOn (sep := "\n") |> String.join

partial def Expr.exportTheorem : Q(Prop) → TacticM String
  | ~q($P ∧ $Q) => return s!"AND({← exportTheorem P}, {← exportTheorem Q})"
  | ~q($P ∨ $Q) => return s!"OR({← exportTheorem P}, {← exportTheorem Q})"
  | ~q(¬$P) => return s!"NOT({← exportTheorem P})"
  | ~q((($P) : Prop) → $Q) => return s!"IMPLIES({← exportTheorem P}, {← exportTheorem Q})"
  | ~q(∃ (a : $α), $P a) =>
      withLocalDeclQ `a .default α fun var ↦ do
      return s!"EXISTS({"a"}, {← Expr.render α}, {← exportTheorem q($P $var)}"
  | e@(.forallE _ _ _ _) =>
    Meta.forallTelescope e fun args body ↦ do
      let proofArgs ← args.filterM fun arg ↦ do isProp (← inferType arg)
      let termArgs ← args.filterM fun arg ↦ do return !(← isProp (← inferType arg))
      let termArgs ← termArgs.mapM fun arg ↦ do return s!"{(← arg.fvarId!.getUserName)} : {← (Expr.exportTheorem <| ← inferType arg)}"
      let propBody ← mkForallFVars proofArgs body
      return s!"{termArgs |>.toList |>.intersperse "," |> String.join} :: {← Expr.exportTheorem propBody}"
  | ~q(@Eq ($α : Type) $x $y) => return s!"EQUALS({← Expr.render x}, {← Expr.render y})"
  | ~q(@LT.lt ($α : Type) (_ : LT $α) $a $b) => return s!"LT({← Expr.render a}, {← Expr.render b})"
  | ~q(@LE.le ($α : Type) (_ : LE $α) $a $b) => return s!"LE({← Expr.render a}, {← Expr.render b})"
  | e => Expr.render e

register_option grasshopper.add_theorems : Bool := {
  defValue := false
  descr := "Whether to add the universal theorems to the local context."
}

macro "push_neg" : tactic =>
  `(tactic| simp only [Classical.not_imp, not_and, not_forall, not_exists, not_not, not_true, not_false_iff, not_le, not_lt] at *)

elab "add_theorems" : tactic => withMainContext do
  if (← getOptions).getBool ``grasshopper.add_theorems then
    for thmName in universalTheoremExt.getState (← getEnv) do
      evalTactic =<< `(tactic| have $(mkIdent <| thmName ++ `local) := $(mkIdent thmName))

elab "substitute" : tactic => withMainContext do
  for decl in (← getLCtx) do
    try
      liftMetaTactic1 (subst · decl.fvarId)
    catch _ => continue

elab "generate_congruence_theorem" c:"checkTypes"? t:ident : tactic => withMainContext do
  let check? := c.isSome
  let guardExprType (e : Expr) : TacticM Unit := do
    if check? then
      guard <| e.constName ∈ [``Int, ``Nat, ``Bool]
  let fn ← Term.elabTerm t none
  let stmt ← inferType fn
  let (mvars, _, conclusion) ← forallMetaTelescope stmt
  guardExprType conclusion
  let (mvars', _, conclusion') ← forallMetaTelescope stmt
  guardExprType conclusion'
  let hyps ← Array.zip mvars mvars' |>.mapM fun (var, var') ↦ do
    guardExprType =<< inferType var
    guardExprType =<< inferType var'
    let eqn ← mkEq var var'
    mkFreshExprMVar eqn
  let congrThm ← mkForallFVars (mvars ++ mvars') <| ← mkForallFVars (binderInfoForMVars := .default) hyps (← mkEq (← mkAppM' fn mvars) (← mkAppM' fn mvars'))
  let congrThmStx ← PrettyPrinter.delab congrThm
  evalTactic =<< `(tactic| have $(mkIdent (t.getId ++ `congr)) : $congrThmStx := by intros; substitute; rfl)

section Congruence

def Lean.Expr.isBoolOrInt (e : Expr) : MetaM Bool := do
  let type ← inferType e
  return type.isConstOf `Bool || type.isConstOf `Int

partial def Lean.Expr.generateSkeleton (e : Expr) : StateT (Array Expr × Nat) MetaM Expr := do
  guard <| ← e.isBoolOrInt
  e.withApp fun f args => do
    let args' ← args.mapM fun arg ↦ do
      if ← arg.isBoolOrInt then
        modifyGet fun ⟨es, n⟩ ↦
          (.fvar ⟨.num `skeleton_var n⟩, ⟨es.push arg, n.succ⟩)
      else
        arg.generateSkeleton
    return mkAppN f args'

partial def Lean.Expr.collectBoolOrIntSubExprs (e : Expr) : StateT (Array Expr) MetaM Unit := do
  e.withApp fun _ args => do
    for arg in args do
      if ← arg.isBoolOrInt then
        modify (·.push arg)
      arg.collectBoolOrIntSubExprs

def Lean.Expr.generateSkeletonMap (e : Expr) : MetaM <| HashMap Expr (Array (Array Expr)) := do
  let e ← reduce <| ← instantiateMVars e
  let (_, subExprs) ← (collectBoolOrIntSubExprs e).run #[]
  subExprs.foldlM (init := {}) fun m e ↦ do
    let (skeleton, ⟨args, _⟩) ← generateSkeleton e |>.run (.empty, 0)
    match m.find? skeleton with
    | some exprs => return m.insert skeleton (exprs.push args)
    | none => return m.insert skeleton #[args]

partial def generateSkeletonMap : TacticM <| HashMap Expr (Array (Array Expr)) := withMainContext do
  (← getLCtx).foldlM (init := {}) fun m decl ↦ do
    let e := decl.type
    let m' ← e.generateSkeletonMap
    return m.mergeWith (fun _ ↦ Array.append) m'

def generateConguenceLemmas : TacticM Unit := withMainContext do
  (← generateSkeletonMap).forM generateConguenceLemmasAux
where
  generateConguenceLemmasAux (skeleton : Expr) (exprs : Array (Array Expr)) : TacticM Unit := withMainContext do
    let congrLemma ← generateConguenceLemma <| ← abstractSkeleton skeleton
    for args in exprs do
      for args' in exprs do
        unless args == args' do
          let congrLemmaInst ← mkAppM' congrLemma (args ++ args')
          let congrLemmaInstStx ← PrettyPrinter.delab congrLemmaInst
          evalTactic =<< `(tactic| have := $congrLemmaInstStx)
  abstractSkeleton (skeleton : Expr) : MetaM Expr := do
    let (_, ⟨_, _, fvarIds⟩) ← skeleton.collectFVars |>.run {}
    mkLambdaFVars (fvarIds.map .fvar) skeleton
  generateConguenceLemma (fn : Expr) : MetaM Expr := do
    let stmt ← inferType fn
    let (mvars, _, conclusion) ← forallMetaTelescope stmt
    guard <| ← conclusion.isBoolOrInt
    let (mvars', _, conclusion') ← forallMetaTelescope stmt
    guard <| ← conclusion'.isBoolOrInt
    let hyps ← Array.zip mvars mvars' |>.mapM fun (var, var') ↦ do
      guard <| ← var.isBoolOrInt
      guard <| ← var'.isBoolOrInt
      let eqn ← mkEq var var'
      mkFreshExprMVar eqn
    let congrThm ← mkForallFVars (mvars ++ mvars')
              <| ← mkForallFVars (binderInfoForMVars := .default) hyps (← mkEq (← mkAppM' fn mvars) (← mkAppM' fn mvars'))
    return congrThm

end Congruence

elab "congruence" : tactic => do generateConguenceLemmas

elab _stx:"auto" : tactic => do
  evalTactic =<< `(tactic| by_contra) -- negating the goal and adding it as a hypothesis
  evalTactic =<< `(tactic| push_neg)
  evalTactic =<< `(tactic| add_theorems)
  evalTactic =<< `(tactic| substitute)
  withMainContext do
    let forbidden := #[`_example, `grasshopper_ih]
    let localDecls := (← getLCtx).decls.toArray.filterMap id |>.filter fun decl ↦ !(decl.kind == .implDetail || forbidden.contains decl.userName.getRoot)
    let context : Array String ← localDecls.filterMapM fun decl ↦ do
      if ← isProp decl.type then
        return none
      else
        let nameComponents := decl.userName.componentsRev
        let varNameRoot := decl.userName.getRoot
        let varName := s!"{varNameRoot}{if nameComponents[1]? = some `_hyg then s!".{nameComponents[0]!}" else ""}"
        return s!"{varName} : {← Expr.render decl.type}"
    let hypotheses : Array String ← localDecls.filterMapM fun decl ↦ do
      if (← isProp decl.type) then
        Expr.exportTheorem <| ← instantiateMVars decl.type
      else return none
    let output : String := (context ++ #["\n---"] ++ hypotheses)
      |>.map (String.push · '\n') |>.foldl (init := "") String.append
    logInfo output
    -- let fileMap ← getFileMap
    -- let fileStem :=
    --   match stx.getHeadInfo.getPos? with
    --   | .some pos =>
    --     let ⟨line, char⟩ := fileMap.utf8PosToLspPos pos
    --     s!"auto-at-line-{line}-character-{char}"
    --   | none => toString output.length
    -- let fileName := s!"./{fileStem}.txt"
    unless (← System.FilePath.pathExists ("." / "check_exported_lean.py")) do
      throwError s!"Invalid file path to Python script."
    let child ← IO.Process.spawn {
      cmd := "./check_exported_lean.py",
      args := #["--instantiate", "--congruence", "--solver", "z3"],
      stdin := .piped,
      stdout := .piped,
      stderr := .piped
    }
    child.stdin.putStr (output ++ "---\n")
    child.stdin.flush
    -- child.stdin.truncate
    let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let result ← IO.ofExcept stdout.get
    if exitCode != 0 then
      throwError s!"process exited with code {exitCode} and error {stderr}"
    logInfo result
    guard <| result.trim == "Proven"
    evalTactic <| ← `(tactic| sorry)
    -- if False then
    --   IO.FS.writeFile fileName output

end Auto

section CaseSplitting

open Lean Elab Meta Parser Term Tactic

def caseSplitOn (mvarId : MVarId) : TacticM Unit := do
  let type ← mvarId.getType
  if ← liftM <| isProp type then do
    let prop ← liftM <| PrettyPrinter.delab type
    evalTactic =<< `(tactic| by_cases hypothesis:$prop)
  else
    throwError "Goal is not a proposition."

def Lean.MVarId.isSolvable? (mvarId : MVarId) : TacticM Bool := withoutModifyingState do
  setGoals [mvarId]
  evalTactic =<< `(tactic| try auto)
  return (← getUnsolvedGoals).isEmpty

elab "extract" pat:rcasesPatMed ":=" value:term : tactic => withMainContext do
  let constrThm ← inferType <| ← Term.elabTerm value none
  let (mvars, _, _) ← forallMetaTelescope constrThm
  for mvar in mvars do
    let mvarId := mvar.mvarId!
    if ← mvarId.isSolvable? then
      continue
    else
      logWarning m!"Splitting on {mvarId}..."
      caseSplitOn mvarId
  let valueWithAuto ← mvars.foldlM (init := value) fun stx _ ↦
    `(term| $stx (by auto))
  evalTactic =<< `(tactic| obtain $pat := $valueWithAuto)

end CaseSplitting
