import Mathlib.Tactic.Partiarith

example (a b c : α) [PartialOrder α] (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
by partiarith
