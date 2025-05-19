/-
Copyright (c) 2025 Joseph Qian and Dhruv Ashok. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Cool
-/
import Lean
import Mathlib.Order.Defs
import Mathlib.Util.AtomM

/-
  TODO: Notes
-/

namespace Mathlib.Tactic.Partiarith
open Lean Meta
open Qq AtomM PrettyPrinter
initialize registerTraceClass `Meta.Tactic.partiarith


@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``LE

/-- Parses local context and hypotheses (provided by client).
 --  > Params
 --     > only : if true, parseContext ignores local context and only parses hypotheses
 --     > hyps : list of hypotheses provided by client
 --     > tgt : target inequality (a ≤ b)
 --
 --  > Returns
 --     > (e₁, e₂, out, nodes) : e₁ = a, e₂ = b, out is an array of Expr × Expr × Expr,
 --       where each element represents a hypothesis a ≤ b, and nodes is an array of
 --       all distinct variables, e.g. a, b.
 -/
def parseContext (only: Bool) (hyps: Array Expr) (tgt: Expr) :
    AtomM (Expr × Expr × Array (Expr × (Expr × Expr)) × Array Expr) := do
    let fail {α} : AtomM α := throwError "bad"
    let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars tgt).le? | fail
    let .sort u ← instantiateMVars (← whnf (← inferType α)) | unreachable!
    let some v := u.dec | throwError "not a type{indentExpr α}"
    have α : Q(Type v) := α
    have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
    let rec
    /-- Parses a hypothesis and adds it to the `out` list.
     --  > Params
     --     > ty : an Expr representing a hypothesis.
     --     > out : the Array of edges, which will be updated by processHyp.
     --
     --  > Returns
     --     > out : an updated Array of edges.
     -/
    processHyp (ty : Expr) (out: Array (Expr × (Expr × Expr))) := do
      if let some (β, e₁, e₂) := (← instantiateMVars (← inferType ty)).le? then
        -- Check for less-than-equal
        if ← withTransparency (← read).red <| isDefEq α β then
            -- the "atoms" here will eventually be our vertex set
            return out.push (ty, (← addAtom e₁).2, (← addAtom e₂).2)

      -- Check for equalities
      else if let some (β, e₁, e₂) := (← instantiateMVars (← inferType ty)).eq? then
        if ← withTransparency (← read).red <| isDefEq α β then
          let h₁₂ ← mkAppM `le_of_eq #[ty]
          let h₂₁ ← mkAppM `le_of_eq #[(← mkAppM `Eq.symm #[ty])]
          return (out.push (h₁₂, (← addAtom e₁).2, (← addAtom e₂).2)).push (h₂₁, e₂, e₁)
      pure out

    let mut out := #[]
    if !only then
        for ldecl in ← getLCtx do
          out ← processHyp ldecl.toExpr out
    for hyp in hyps do
        out ← processHyp hyp out

    let nodes := (← get).atoms
    pure (e₁, e₂, out, nodes)


structure DfsData where
  pathSoFar : Array (Expr × (Expr × Expr))
  toDiscover : Array (Expr)

/-- Performs a depth-first search over a directed graph representing the local context
 -- and user-defined hypotheses. The nodes of the graph are elements of the poset and
 -- the edges represent the ≤ relation, pointing from the smaller element to the larger
 -- element. In the case of equality, we use a bidirectional edge.
 --  > Params
 --     > v₁ : the starting node.
 --     > v₂ : the target node.
 --     > edges : an Array containing every edge in the graph.
 -      > nodes : an Array containing every node in the graph.
 --    Note: the parameters of dfs_outer are the outputs of parseContext.
 --
 --  > Returns
 --     > pathSoFar : an Array (Expr × (Expr × Expr)) representing a path from v₁ to
 --       v₂, or none if no path was found.
 -/
def dfsOuter (v₁ : Expr) (v₂ : Expr) (edges : Array (Expr × (Expr × Expr))) (nodes : Array Expr)
    (trace := false) : MetaM (Option (Array (Expr × (Expr × Expr)))) := do
  let mut nodes := nodes
  let rec
  /-- Returns an Array containing the outgoing edges of a node `tgt` -/
  getNeighbors (tgt: Expr) : MetaM (Array (Expr × (Expr × Expr))) := do
    let mut out := #[]
    for edge in edges do
      if ← isDefEq edge.2.1 tgt then
        out := out.push edge
    return out

  let rec
  /-- Recursively performs depth-first search on the directed graph.
   --  > Params
   --     > node : the next node to be explored by the DFS algorithm
   --     > currentData : a dfs_data structure representing the current state of the
            DFS.
   --
   --  > Returns
   --     > pathSoFar : an Array (Expr × (Expr × Expr)) representing a path from v₁ to
   --       v₂, or none if no path was found.
   -/
  dfsLoop (node : Expr) (currentData : DfsData) :
    MetaM (Option (Array (Expr × (Expr × Expr)))) :=
  do
    let neighbors ← getNeighbors node
    for neighbor in neighbors do
    -- only look at undiscovered neighbors
      match currentData.toDiscover.indexOf? neighbor.2.2 with
      | none => continue
      | some i =>
        let currentData := {currentData with toDiscover := currentData.toDiscover.feraseIdx i}
        let addToPath := {currentData with pathSoFar := currentData.pathSoFar.push neighbor}
        if ← isDefEq v₂ neighbor.2.2 then
          -- destination reached
          return (some addToPath.pathSoFar)
        if let some finalData ← dfsLoop neighbor.2.2 addToPath then
          return some finalData -- destination reached at a later step
    -- no neighbors worked: this step is a dead end
    return none
  termination_by currentData.toDiscover.size
  decreasing_by {
    rw [Array.size_feraseIdx]
    apply Nat.sub_one_lt
    apply Nat.ne_of_gt
    apply Fin.size_pos;
    exact i
    }

  -- Begin depth-first search.
  let path ← dfsLoop v₁ {pathSoFar := #[], toDiscover := (nodes.erase v₁)}
  -- if trace then logInfo traceString
  return path


def proofFromPath (path : Array (Expr × Expr × Expr)) : Option (MetaM Expr) := do
  let proofs := path.map (fun x => x.1)
  match proofs[0]? with
    | none => none
    | some firstProof =>
    return Array.foldlM (fun a b : Expr => (mkAppM `le_trans #[a, b]))
      firstProof (proofs.erase firstProof)




/-- Polyrith for posets.
 --  > Params
 --     > g : the goal; partiarith will attempt to build and return a proof of `g`.
 --     > only : if true, partiarith will only use the user-defined hypotheses `hyps`.
 --       Otherwise, partiarith will use hyps and the local context.
 --     > hyps : an Array of user-defined hypotheses.
 --     > traceOnly : if true, debugging messages will be printed.
 --
 --  > Returns
 --     > newGoal : a proof of `g`, or none if `g` cannot be proved.
 -/
def partiarith (g : MVarId) (only : Bool) (hyps : Array Expr)
    (traceOnly := false) : MetaM (Except MVarId (Expr)) := do
    g.withContext <| AtomM.run .reducible do
    let (v₁, v₂, edges, nodes) ← parseContext only hyps (← g.getType)
    match ← dfsOuter v₁ v₂ edges nodes traceOnly with
    | some pathToDest => match (proofFromPath pathToDest) with
      | none => return (.error g)
      | some proofProgram =>
      return (.ok (← proofProgram))
    | none => return (Except.error g)

syntax "partiarith" (&" only")? (" [" term,* "]")? : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| partiarith $[only%$onlyTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.partiarith
    let g ← getMainGoal
    match ← partiarith g onlyTk.isSome hyps traceMe with
    | .ok newGoal =>
      if traceMe then logInfo f!"{← delab newGoal}"
      Lean.Elab.Tactic.closeMainGoal `partiarith newGoal
    | .error g => replaceMainGoal [g]

end Mathlib.Tactic.Partiarith
