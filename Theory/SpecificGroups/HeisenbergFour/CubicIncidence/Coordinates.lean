module

public import Theory.SpecificGroups.HeisenbergFour.CubicExtension
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Executable coordinates for the Heisenberg-four cubic extension

The field F₂[ω], with ω² = ω + 1, supplies finite coordinates. The field
isomorphism with GF(4) induces an isomorphism of the literal Heisenberg
semidirect products, including the diagonal action and central cross term.
The sixteen conjugates below will parametrize the cubic subgroups.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and 47.6(1).
-/

@[expose] public section
namespace HeisenbergFour.CubicIncidence

abbrev Four := QuadraticAlgebra (ZMod 2) 1 1
instance noRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩
instance fourFintype : Fintype Four :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm

abbrev CoordinateModel := Heisenberg Four ⋊[Heisenberg.action] Fourˣ
instance heisFintype : Fintype (Heisenberg Four) :=
  Fintype.ofEquiv (Four × Four × Four) Heisenberg.coordinates.symm
instance coordinateFintype : Fintype CoordinateModel :=
  Fintype.ofEquiv (Heisenberg Four × Fourˣ) SemidirectProduct.equivProd.symm

/-- Field transport preserves the Heisenberg cross term. -/
def heisenbergCongr {F K : Type*} [CommRing F] [CommRing K]
    (e : F ≃+* K) : Heisenberg F ≃* Heisenberg K where
  toFun s := ⟨e s.a, e s.b, e s.c⟩
  invFun s := ⟨e.symm s.a, e.symm s.b, e.symm s.c⟩
  left_inv s := by ext <;> simp
  right_inv s := by ext <;> simp
  map_mul' s t := by
    apply Heisenberg.ext
    · exact map_add e _ _
    · exact map_add e _ _
    · change e (s.c + t.c + s.a * t.b) = e s.c + e t.c + e s.a * e t.b
      simp only [map_add, map_mul]

/-- Transport both factors with the literal diagonal action. -/
def extensionCongr {F K : Type*} [CommRing F] [CommRing K]
    (e : F ≃+* K) :
    (Heisenberg F ⋊[Heisenberg.action] Fˣ) ≃*
      (Heisenberg K ⋊[Heisenberg.action] Kˣ) :=
  SemidirectProduct.congr (heisenbergCongr e) (Units.mapEquiv e.toMulEquiv) (by
    intro u
    ext s <;> simp [heisenbergCongr, Heisenberg.action_apply]
    rw [← map_inv]
    rfl)

noncomputable def fieldEquiv : Four ≃+* Field := by
  letI := Fintype.ofFinite Field
  apply FiniteField.ringEquivOfCardEq
  rw [show Fintype.card Four = 4 by decide +kernel,
    ← Nat.card_eq_fintype_card, field_card]

/-- Actual group equivalence with the published GF(4) semidirect product. -/
noncomputable def modelEquiv : CoordinateModel ≃* Model := extensionCongr fieldEquiv

def omega : Four := ⟨0, 1⟩
def unit : Fourˣ := ⟨omega, omega ^ 2, by decide +kernel, by decide +kernel⟩
def base : CoordinateModel := SemidirectProduct.inr unit
def shift (i : Four × Four) : CoordinateModel := SemidirectProduct.inl ⟨i.1, i.2, 0⟩
def gen (i : Four × Four) : CoordinateModel := shift i * base * (shift i)⁻¹
def C (i : Four × Four) : Subgroup CoordinateModel := Subgroup.zpowers (gen i)

end HeisenbergFour.CubicIncidence
