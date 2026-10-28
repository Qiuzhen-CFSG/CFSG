module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.DeriveFintype

/-!
# The Fano plane in binary coordinates

Points are nonzero vectors in F₂³, and lines are tagged nonzero covectors.
Incidence is the vanishing of their dot product. Tags keep the natural and
contragredient group actions on different types. Over F₂ no scalar quotient
is necessary: the only nonzero scalar is one.

The seven-point model is small enough that its incidence counts and unique
joins and meets are checked by kernel reduction. These are the elementary
plane facts used in Aschbacher–Smith, *The Classification of Quasithin
Groups*, I.5.4 and I.5.9, printed pp. 420–422.
-/

@[expose] public section

namespace Matrix.PSL3Two.Fano

abbrev Vector := Fin 3 → ZMod 2
abbrev Point := {v : Vector // v ≠ 0}
structure Line where
  normal : Point
  deriving DecidableEq, Fintype

def Incident (p : Point) (l : Line) : Prop := dotProduct p.val l.normal.val = 0
instance (p : Point) (l : Line) : Decidable (Incident p l) := inferInstanceAs (Decidable (_ = _))

theorem card_point : Fintype.card Point = 7 := by decide
theorem card_line : Fintype.card Line = 7 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem points_on_line : ∀ l : Line, Fintype.card {p : Point // Incident p l} = 3 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem lines_through_point : ∀ p : Point, Fintype.card {l : Line // Incident p l} = 3 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem unique_line : ∀ p q : Point, p ≠ q → ∃! l : Line, Incident p l ∧ Incident q l := by
  unfold ExistsUnique
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem unique_point : ∀ l m : Line, l ≠ m → ∃! p : Point, Incident p l ∧ Incident p m := by
  unfold ExistsUnique
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem card_flags : Fintype.card {pl : Point × Line // Incident pl.1 pl.2} = 21 := by
  decide +kernel

/-- Point-line duality on the chosen coordinates. -/
def duality : Point ≃ Line where
  toFun := Line.mk
  invFun := Line.normal
  left_inv _ := rfl
  right_inv _ := rfl

theorem incident_duality (p q : Point) : Incident p (duality q) ↔ Incident q (duality p) := by
  change dotProduct p.val q.val = 0 ↔ dotProduct q.val p.val = 0
  rw [dotProduct_comm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem points_off_line : ∀ l : Line, Fintype.card {p : Point // ¬ Incident p l} = 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem lines_missing_point : ∀ p : Point, Fintype.card {l : Line // ¬ Incident p l} = 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem other_points_on_line : ∀ p : Point, ∀ l : Line, Incident p l →
    Fintype.card {q : Point // Incident q l ∧ q ≠ p} = 2 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem other_lines_through_point : ∀ p : Point, ∀ l : Line, Incident p l →
    Fintype.card {m : Line // Incident p m ∧ m ≠ l} = 2 := by decide +kernel

end Matrix.PSL3Two.Fano
