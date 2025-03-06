import Lean
import Mathlib.Order.Defs
import Mathlib.Util.AtomM

namespace Mathlib.Tactic.Partiarith
open Lean Meta Qq
open AtomM PrettyPrinter
initialize registerTraceClass `Meta.Tactic.partiarith

-- def parseContext (only: Bool) (hyps: Array Expr) (tgt: Expr) : Expr × Expr × List Expr × List Expr
-- takes in local hypotheses as well as the target expression
-- should return start vertex, end vertex, and the set of our relevant hypotheses (our edges)
-- vertex set is recorded by AtomM

-- TODO: test that this LE recognizer works
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``LE

/-- The possible hypothesis sources for a proof. -/
inductive Source where
  /-- `input n` refers to the `n`'th input `ai` in `polyrith [a1, ..., an]`. -/
  | input : Nat → Source
  /-- `fvar h` refers to hypothesis `h` from the local context. -/
  | fvar : FVarId → Source

def parseContext (only: Bool) (hyps: Array Expr) (tgt: Expr) :
    AtomM (Expr × Expr × Array (Expr × Expr)) := do
    let fail {α} : AtomM α := throwError "bad"
    let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars tgt).le? | fail
    let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
    let some v := u.dec | throwError "not a type{indentExpr α}"
    have α : Q(Type v) := α
    have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
    -- TODO: probably use this at some point
    -- let sα ← synthInstanceQ (q(PartialOrder $α) : Q(Type v))
    let rec
    /-- Parses a hypothesis and adds it to the `out` list. -/
    processHyp ty (out: Array (Expr × Expr)) := do
      if let some (β, e₁, e₂) := (← instantiateMVars ty).le? then
        -- TODO: transparency issues? look at polyrith
        -- Check for less-than-equal
        if ← withTransparency (← read).red <| isDefEq α β then
            -- TODO: does this work?
            -- the "atoms" here will eventually be our vertex set
            -- let _ := addAtom e₁
            -- let _ := addAtom e₂
            return out.push ((← addAtom e₁).2, (← addAtom e₂).2)

      -- Check for equalities
      if let some (β, e₁, e₂) := (← instantiateMVars ty).eq? then
        if ← withTransparency (← read).red <| isDefEq α β then
            -- return (out.push (e₁, e₂)).push (e₂, e₁)
          return (out.push ((← addAtom e₁).2, (← addAtom e₂).2)).push (e₂, e₁ )
      pure out
    let mut out := #[]
    if !only then
        for ldecl in ← getLCtx do
        out ← processHyp ldecl.type out
    for hyp in hyps do
        out ← processHyp (← inferType hyp) out
    pure (e₁, e₂, out)


structure dfs_data where
  path_so_far : Array (Expr × Expr)
  discovered : Array (Expr)

def dfs_outer (v₁ : Expr) (v₂ : Expr) (edges : Array (Expr × Expr))
    : StateT dfs_data MetaM (Option Unit) := do

  let rec
  getNeighbors (tgt: Expr) := do
    let mut out := #[]
    for edge in edges do
      if ← isDefEq edge.1 tgt then
          -- logInfo f!"{← delab edge.1}"
          -- logInfo f!"{← delab edge.2}"
        return out.push edge
    return out

  let rec
  dfs_loop (node : Expr) := do
    let neighbors ← getNeighbors node
    let st ← get
    let updated_discovered ← pure {st with discovered := st.discovered.push node}
    if neighbors.size == 0 then
      let updated_path_so_far ← pure {st with path_so_far:= st.path_so_far.extract 0 (st.path_so_far.size - 1)}



    for neighbor in neighbors do

  dfs_loop v₁
#check Meta.State

def partiarith (g : MVarId) (only : Bool) (hyps : Array Expr)
    (traceOnly := false) : MetaM (Except MVarId (Unit)) := do
    g.withContext <| AtomM.run .reducible do
    let (v₁, v₂, edges) ← parseContext only hyps (← g.getType)
    let relevant_edges ← dfs_outer v₁ v₂ edges
    -- logInfo f!"{← delab v₁}"
    -- logInfo f!"{← delab v₂}"
    -- for edge in edges do
    --   logInfo f!"{← delab edge.1}"
    --   logInfo f!"{← delab edge.2}"

    pure (.ok .unit)




syntax "partiarith" (&" only")? (" [" term,* "]")? : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| partiarith%$tk $[only%$onlyTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.partiarith
    match ← partiarith (← getMainGoal) onlyTk.isSome hyps traceMe with
    | .ok .unit =>
      replaceMainGoal []
      -- TODO replace this with finishing the goal using an appropriate proof term
      --if !traceMe then Lean.Elab.Tactic.closeMainGoal `partiarith proof
    | .error g => replaceMainGoal [g]

end Mathlib.Tactic.Partiarith

-- NEXT STEP
-- look at what polyrith does
-- syntax, elaborator
-- def mainBody

-- recognizer for GE (similar to eq in Lean.Util.Recognizers)

-- def dfs



-- parseContext first steps should look pretty similar to polyrith
