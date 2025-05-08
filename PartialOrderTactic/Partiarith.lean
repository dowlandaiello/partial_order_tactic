import Lean
import Mathlib.Order.Defs
import Mathlib.Util.AtomM

namespace Mathlib.Tactic.Partiarith
open Lean Meta Qq
open AtomM PrettyPrinter
initialize registerTraceClass `Meta.Tactic.partiarith

-- TODO: test that this LE recognizer works
@[inline] def le? (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3? ``LE

/-- The possible hypothesis sources for a proof. -/
inductive Source where
  /-- `input n` refers to the `n`'th input `ai` in `polyrith [a1, ..., an]`. -/
  | input : Nat → Source
  /-- `fvar h` refers to hypothesis `h` from the local context. -/
  | fvar : FVarId → Source

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

    -- TODO: probably use this at some point
    -- let sα ← synthInstanceQ (q(PartialOrder $α) : Q(Type v))
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
        -- TODO: transparency issues? look at polyrith
        -- Check for less-than-equal
        if ← withTransparency (← read).red <| isDefEq α β then
            -- the "atoms" here will eventually be our vertex set
            return out.push (ty, (← addAtom e₁).2, (← addAtom e₂).2)

      -- Check for equalities
      else if let some (β, e₁, e₂) := (← instantiateMVars (← inferType ty)).eq? then
        if ← withTransparency (← read).red <| isDefEq α β then
          return (out.push (ty, (← addAtom e₁).2, (← addAtom e₂).2)).push (ty, e₂, e₁)
      pure out

    let mut out := #[]
    if !only then
        for ldecl in ← getLCtx do
          out ← processHyp ldecl.toExpr out
    for hyp in hyps do
        out ← processHyp hyp out

    let nodes := (← get).atoms
    for edge in out do
      logInfo f!"{← delab edge.1}"
    pure (e₁, e₂, out, nodes)


structure dfs_data where
  path_so_far : Array (Expr × (Expr × Expr))
  to_discover : Array (Expr)

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
 --     > path_so_far : an Array (Expr × (Expr × Expr)) representing a path from v₁ to
 --       v₂, or none if no path was found.
 -/
def dfs_outer (v₁ : Expr) (v₂ : Expr) (edges : Array (Expr × (Expr × Expr))) (nodes : Array Expr)
    : MetaM (Option (Array (Expr × (Expr × Expr)))) := do
  let mut nodes := nodes
  let rec
  /-- Returns an Array containing the outgoing edges of a node `tgt` -/
  getNeighbors (tgt: Expr) : MetaM (Array (Expr × (Expr × Expr))) := do
    let mut out := #[]
    for edge in edges do
      if ← isDefEq edge.2.1 tgt then
          -- logInfo f!"{← delab edge.1}"
          -- logInfo f!"{← delab edge.2}"
        return out.push edge
    return out

  let rec
  /-- Recursively performs depth-first search on the directed graph.
   --  > Params
   --     > node : the next node to be explored by the DFS algorithm
   --     > current_data : a dfs_data structure representing the current state of the
            DFS.
   --
   --  > Returns
   --     > path_so_far : an Array (Expr × (Expr × Expr)) representing a path from v₁ to
   --       v₂, or none if no path was found.
   -/
  dfs_loop (node : Expr) (current_data : dfs_data) : MetaM (Option (Array (Expr × (Expr × Expr)))) := do
    let neighbors ← getNeighbors node
    for neighbor in neighbors do
    -- only look at undiscovered neighbors
      match current_data.to_discover.indexOf? neighbor.2.2 with
      | none => return none
      | some i =>
        let mut current_data := {current_data with to_discover := current_data.to_discover.feraseIdx i}
        current_data := {current_data with path_so_far := current_data.path_so_far.push neighbor}
        if ← isDefEq v₂ neighbor.2.2 then
          -- destination reached
          return (some current_data.path_so_far)
        else match ← dfs_loop neighbor.2.2 current_data with
          | some final_data => return some final_data -- destination reached at a later step
          | none => -- next step is a dead end: need to backtrack
            current_data := {current_data with path_so_far := current_data.path_so_far.pop}
    -- no neighbors worked: this step is a dead end
    return none
  termination_by current_data.to_discover.size
  decreasing_by
    {rw [Array.size_feraseIdx]; apply Nat.sub_one_lt; apply Nat.ne_of_gt; apply Fin.size_pos; exact i;}

  -- Begin depth-first search.
  return ← dfs_loop v₁ {path_so_far := #[], to_discover := (nodes.erase v₁)}

/-- Polyrith for posets.
 --  > Params
 --     > g : the goal; partiarith will attempt to build and return a proof of `g`.
 --     > only : if true, partiarith will only use the user-defined hypotheses `hyps`.
 --       Otherwise, partiarith will use hyps and the local context.
 --     > hyps : an Array of user-defined hypotheses.
 --     > traceOnly : if true, debugging messages will be printed.
 --
 --  > Returns
 --     > new_goal : a proof of `g`, or none if `g` cannot be proved.
 -/
def partiarith (g : MVarId) (only : Bool) (hyps : Array Expr)
    (traceOnly := false) : MetaM (Except MVarId (Expr)) := do
    g.withContext <| AtomM.run .reducible do
    let (v₁, v₂, edges, nodes) ← parseContext only hyps (← g.getType)
    match ← dfs_outer v₁ v₂ edges nodes with
    | some path_to_dest =>
      for hyp in path_to_dest do
        logInfo f!"{← delab hyp.1}"
      let mut new_goal ← mkAppM ``LE.le #[v₁, v₁] -- new_goal = v₁ ≤ v₁
      -- logInfo f!"{← delab new_goal}"
      for edge in path_to_dest do
        -- logInfo f!"{← delab edge.1}"
        if let some (_, _, _) := (edge.1).le? then
          new_goal := ← mkAppM ``le_trans #[new_goal, edge.1] -- transitivity
        else if let some (_,_,_) := (edge.1).eq? then
          new_goal := ← mkAppM ``Eq.subst #[new_goal, edge.1] -- substitute equality into prev ineq
      -- logInfo f!"{← delab new_goal}"
      -- logInfo f!"{← delab edge.2.2}"
      pure (.ok new_goal)
    | none => return (Except.error g)


syntax "partiarith" (&" only")? (" [" term,* "]")? : tactic

open Elab Tactic
elab_rules : tactic
  | `(tactic| partiarith $[only%$onlyTk]? $[[$hyps,*]]?) => do
    let hyps ← hyps.map (·.getElems) |>.getD #[] |>.mapM (elabTerm · none)
    let traceMe ← Lean.isTracingEnabledFor `Meta.Tactic.partiarith
    let g ← getMainGoal
    match ← partiarith g onlyTk.isSome hyps traceMe with
    | .ok new_goal =>
      Lean.Elab.Tactic.closeMainGoal `partiarith new_goal
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
