import Lean
import Mathlib.Order.Defs

open Lean Meta

elab "partiarith" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- let goalType ← Lean.Elab.Tactic.getMainTarget
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type
      let declExpr ← whnf declType -- TODO: figure out how to mess with this more
      -- dbg_trace f!"- local expr: {declName} {declExpr}"
      match declExpr with
      | (.app func val) => do
        -- i want to make PartialOrder applied to a type, and then match against that
        -- ((Preorder.toLT.{0} _uniq.2071 (PartialOrder.toPreorder.{0} _uniq.2071 _uniq.2072)).1)
        -- let a ← mkFreshExprMVar (some (Sort 1))
        -- let i ← PartialOrder a
        dbg_trace f!"{declName}: {func} APPLIED TO {val}"
      | _ => dbg_trace f!"{declName}: bad {decl.toExpr}"
    --   let declInfo ← Lean.MVarId.getDecl

-- def get_decls (ctx : LocalContext) : List Expr := do

-- want to use this to create adj graph
def match_le (e: Expr) :
  MetaM <| Option (Expr × Expr) := do
    let nat := mkConst ``Nat
    let a ← mkFreshExprMVar nat
    let b ← mkFreshExprMVar nat
    let ineq ← mkAppM ``Nat.le #[a, b] -- look at the comment here!
    if ← isDefEq ineq e then
      return some (a, b)
    else
      return none

example [PartialOrder α] (x y z : α) (h : x < y) (h2 : y ≤ z) : x < z := by
  partiarith
