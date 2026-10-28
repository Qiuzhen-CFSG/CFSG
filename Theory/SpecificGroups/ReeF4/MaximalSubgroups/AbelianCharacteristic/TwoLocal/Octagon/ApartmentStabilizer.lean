module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Setup
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.ApartmentStabilizer.Opposition

/-!
# Oddness of the actual standard-apartment fixer

The standard apartment consists of the normalizer translates of both standard
full-parabolic cosets. An element fixing these vertices lies in the Borel and
in its conjugate by the concrete opposition word. The matrix/root calculation
in `ApartmentStabilizer.Opposition` bounds this intersection by the fixed torus,
whose order is odd. No assertion about apartment cycles or the abstract Weyl
quotient is needed.

Source: the BN-pair apartments of GLS3 2.3.4–5 and §2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open Subgroup LargeLocalSeeds Parabolics SectionGeometry.BNPair ApartmentStabilizer

/-- Every normalizer translate of the base chamber is fixed pointwise, so
conjugating an apartment fixer by a normalizer word puts it in the Borel. -/
theorem standardApartment_fixer_conjugate_mem_borel (m : ℕ) (hm : 1 ≤ m) {x n : Model m}
    (hx : x ∈ fixingSubgroup (Model m) (standardApartment m))
    (hn : n ∈ normalizerWords m) : n⁻¹ * x * n ∈ borel m := by
  have hs (s : Side) : n⁻¹ * x * n ∈ ConverseParabolics.parabolic m s := by
    rw [← CosetGeometry.stabilizer_base (ConverseParabolics.parabolic m) s]
    apply MulAction.mem_stabilizer_iff.mpr
    have hfix := (mem_fixingSubgroup_iff _).mp hx _
      (show n • CosetGeometry.base (ConverseParabolics.parabolic m) s ∈ standardApartment m from
        ⟨n, hn, s, rfl⟩)
    simpa only [mul_smul, inv_smul_smul] using congrArg (n⁻¹ • ·) hfix
  rw [← parabolic_inf_eq_borel m hm]
  exact ⟨hs _, hs _⟩

/-- Fixing the base and opposite chambers puts the actual apartment fixer
in the fixed torus, by the concrete opposite-Borel intersection. -/
theorem standardApartment_fixer_le_fixedTorus (m : ℕ) (hm : 1 ≤ m) :
    fixingSubgroup (Model m) (standardApartment m) ≤ fixedTorus m := by
  intro x hx
  exact borel_opposition_intersection m (standardApartment_fixer_le_borel m hm hx)
    (standardApartment_fixer_conjugate_mem_borel m hm hx (opposition_mem_normalizerWords m))

/-- The pointwise stabilizer of the actual normalizer apartment has odd order. -/
theorem standardApartment_fixer_odd (m : ℕ) (hm : 1 ≤ m) :
    Odd (Nat.card (fixingSubgroup (Model m) (standardApartment m))) :=
  standardApartment_fixer_odd_of_le_fixedTorus m (standardApartment_fixer_le_fixedTorus m hm)
end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
