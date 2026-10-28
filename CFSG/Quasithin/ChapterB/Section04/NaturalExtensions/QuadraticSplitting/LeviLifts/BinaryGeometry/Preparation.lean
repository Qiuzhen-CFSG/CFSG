module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LeviLifts.Reduction

/-!
# Matrix geometry for the binary Levi step

The three-transvection exchange sends a root in the quotient axis group into
its literal Levi intersection. The explicit root calculation uses every
characteristic-two defining field and does not assume a splitting or fixed
lift. The standard binary block and the transport from the original natural
submodule are kept separate, so their coordinate constructions can be proved
independently and then composed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.92–93.
-/

@[expose] public section
open Representation Representation.BinaryOffender
open Representation.OneCohomology.SLHigherNatural Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
open QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ} (m : QuotientCoordinates d)
  {i j k : Fin n} (hij : i ≠ j)

include hij in
/-- A root whose two indices avoid j belongs to the literal Levi. -/
theorem elementary_mem_Levi (hki : k ≠ i) (hkj : k ≠ j) (a : F.Carrier) :
    m.action.groupEquiv.symm (transvection hki a) ∈ m.K j := by
  have hfix (z : V ⧸ d.space.toSubmodule) :
      m.action.linearEquiv (d.space.quotientRepresentation
        (m.action.groupEquiv.symm (transvection hki a)) z) =
        m.action.linearEquiv z + Pi.single k (a * m.action.linearEquiv z i) := by
    rw [m.action.intertwines, MulEquiv.apply_symm_apply]
    exact action_transvection hki a _
  constructor
  · intro z
    change (m.action.linearEquiv
      (d.space.quotientRepresentation _ z)) j = 0 ↔ (m.action.linearEquiv z) j = 0
    rw [hfix]
    simp [Pi.single_eq_of_ne hkj.symm]
  · refine ⟨Subgroup.mem_top _, ?_⟩
    intro z hz
    apply m.action.linearEquiv.injective
    rw [hfix]
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hz
    have hzi : m.action.linearEquiv z i = 0 := by
      change b • Pi.single j 1 = m.action.linearEquiv z at hb
      rw [← hb]
      simp [Pi.single_eq_of_ne hij]
    rw [hzi, mul_zero, Pi.single_zero, add_zero]

/-- The exchange word carries a column-j root to a column-i root. -/
theorem exchange_root_relation (hki : k ≠ i) (hkj : k ≠ j) (a : F.Carrier) :
    (transvection hij (1 : F.Carrier) * transvection hij.symm 1 * transvection hij 1) *
      transvection hkj a =
      transvection hki a *
        (transvection hij 1 * transvection hij.symm 1 * transvection hij 1) := by
  apply toLin'_injective
  ext v r
  change specialLinearNatural n (_ * _) v r = specialLinearNatural n (_ * _) v r
  simp only [map_mul, Module.End.mul_apply, action_transvection, Pi.add_apply]
  have he (x y : F.Carrier) : x + y + (y + (x + y)) = y := by
    calc
      _ = (x + x) + (y + y) + y := by abel
      _ = y := by simp [CharTwo.add_self_eq_zero]
  by_cases hrk : r = k
  · subst r
    simp [*]
  · by_cases hri : r = i
    · subst r
      simp [*]
    · by_cases hrj : r = j
      · subst r
        simp [*]
      · simp [*]

/-- An actual root in the source subgroup P = K ∩ Qᵍ. -/
theorem elementary_mem_seed (hki : k ≠ i) (hkj : k ≠ j) (a : F.Carrier) :
    m.action.groupEquiv.symm (transvection hki a) ∈ seedGroup m hij := by
  refine ⟨elementary_mem_Levi m hij hki hkj a, ?_⟩
  refine ⟨m.action.groupEquiv.symm (transvection hkj a), elementary_mem_Q m hkj a, ?_⟩
  apply m.action.groupEquiv.injective
  change m.action.groupEquiv (exchangeActor m hij * _ * (exchangeActor m hij)⁻¹) = _
  simp only [map_mul, map_inv, exchangeActor, MulEquiv.apply_symm_apply]
  rw [exchange_root_relation hij hki hkj a, mul_assoc, mul_inv_cancel, mul_one]
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviLifts
