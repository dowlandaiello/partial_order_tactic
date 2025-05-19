--import Mathlib.Tactic.Partiarith
import PartialOrderTactic.Partiarith
import Lean.Expr

lemma first (a b c: α) [PartialOrder α] (hab : a ≤ b) (hbc : c = b) : a ≤ c := by partiarith


example (a b c d e: α) [PartialOrder α] (hab : a ≤ b) (hac : a ≤ c) (hbc : c = b) (hbd : b ≤ d) (hce : c ≤ e) : a ≤ e := by partiarith

#check OptionT
#check Lean.logInfo
