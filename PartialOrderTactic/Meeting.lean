import Lean
import Mathlib.Order.Defs
import Mathlib.Util.AtomM

namespace Mathlib.Tactic.CoolTactic
open Lean Meta Qq
open AtomM

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
        if ← isDefEq α β then
            -- TODO: does this work?
            -- the "atoms" here will eventually be our vertex set
            let _ := addAtom e₁
            let _ := addAtom e₂
            return out.push (e₁, e₂)

      -- Check for equalities
      if let some (β, e₁, e₂) := (← instantiateMVars ty).eq? then
        if ← isDefEq α β then
            return (out.push (e₁, e₂)).push (e₂, e₁)
        --   return out.push ((← addAtom e₁).2, (← addAtom e₂).2)
      pure out
    let mut out := #[]
    if !only then
        for ldecl in ← getLCtx do
        out ← processHyp ldecl.type out
    for hyp in hyps do
        out ← processHyp (← inferType hyp) out
    pure (e₁, e₂, out)



-- NEXT STEP
-- look at what polyrith does
-- syntax, elaborator
-- def mainBody

-- recognizer for GE (similar to eq in Lean.Util.Recognizers)

-- def dfs



-- parseContext first steps should look pretty similar to polyrith
