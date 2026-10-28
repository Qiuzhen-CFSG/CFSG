module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.Commutator

universe u

set_option linter.style.haveILetI false

open scoped commutatorElement

/-! Nilpotency bounds from a terminating relative-root filtration. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A terminal relative-root layer bounds the nilpotency class of the first
layer. -/
public theorem relativeRootSeries_nilpotencyClass_le_of_terminal
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) (e : D.Root ≃ ι)
    (coeff : ι → ι → ℤ) (hCoeff : HasSimpleRootExpansion P base coeff)
    (J : Set D.Root) (U : Subgroup (Variety.Point K))
    (hOne : RelativeRootSeries D e base.support coeff J 1 = U)
    (C : ChevalleyData K D)
    (hC : IsChevalleySystem D C P e base)
    (a : ℕ)
    (hTerminal : RelativeRootSeries D e base.support coeff J (a + 1) = ⊥) :
    Group.nilpotencyClass U ≤ a := by
  letI := Fintype.ofFinite D.Root
  letI := Fintype.ofFinite ι
  have hComm : ∀ i,
      ⁅RelativeRootSeries D e base.support coeff J (i + 1), U⁆ ≤
        RelativeRootSeries D e base.support coeff J (i + 2) := by
    intro i
    rw [← hOne]
    exact relativeRootSeries_commutator_series_le (D := D) (C := C)
      (P := P) (e := e) (base := base) (coeff := coeff)
      (hCoeff := hCoeff) (hC := hC) (J := J) (i := i + 1) (by omega)
  exact nilpotencyClass_le_of_subgroupSeries U
    (RelativeRootSeries D e base.support coeff J) a hOne hComm hTerminal

end Theory.AlgebraicGroup
