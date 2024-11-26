import Mathlib.Order.Defs

elab "partiarith" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- let goalType ← Lean.Elab.Tactic.getMainTarget
    let goals ← Lean.Elab.Tactic.getGoals
    goals.forM $ fun goal => do
        let goalType ← goal.getType
        dbg_trace f!"+ goal: {goal.name} {goalType}"
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      let declType ← Lean.Meta.inferType declExpr -- Find the type.
    --   let declInfo ← Lean.MVarId.getDecl
      dbg_trace f!"+ local decl: name: {declName} {declExpr} {declType}"

example {α : Type} [PartialOrder α] (x y z : α) (h : x < y) (h2 : y ≤ z) : x < z := by
partiarith
