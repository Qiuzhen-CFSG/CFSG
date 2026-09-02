module
import Mathlib
universe u
structure X : Prop where
  p n : ℕ
  hp : Nat.Prime p
  h : p ^ n = p ^ n
