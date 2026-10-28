module

public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.SpecificGroups.Suzuki.EightOuterTori
public import Theory.SpecificGroups.Suzuki.FieldAutomorphism
public import Theory.GroupTheory.NormalizerFullAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Exact field actors for a Rudvalis Suzuki component

The normalizer action has inner preimage I C(I), so its index divides the
proved outer index three. A normalizer element outside this preimage makes
the action surjective. If C(I) has exponent two, the fourth power of a lift
of Frobenius has order three and induces Frobenius itself. This retains the
precise automorphism and the original matrix equivalence.

Source: GLS3, Table 5.3r; Aschbacher–Smith I.2.2(7a), printed p.412.
The ambient component-centralizer and fusion inputs are separate model facts.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.CubicExtension
open Subgroup BenderSuzuki.MatrixGroups

public theorem component_outer_index (I : Subgroup Model) (e : I ≃* SuzukiMatrixGroup 1) :
    (MulAut.conj : I →* MulAut I).range.index = 3 := by
  change (MulAut.innerSubgroup I).index = 3
  rw [← index_map_equiv _ (MulAut.congr e)]
  change ((MulAut.innerSubgroup I).map (MulAut.congr e).toMonoidHom).index = 3
  rw [MulAut.map_innerSubgroup_congr]
  exact suzuki_eight_outer_index

/-- The only possible indices are one and three; no ambient order calculation
or normalizer table is used. -/
public theorem normalizer_index_dvd_three (I : Subgroup Model) (e : I ≃* SuzukiMatrixGroup 1) :
    (I ⊔ centralizer (I : Set Model)).relIndex (normalizer (I : Set Model)) ∣ 3 := by
  have hle : (MulAut.conj : I →* MulAut I).range ≤ I.normalizerMonoidHom.range := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨x, I.le_normalizer x.property⟩, ?_⟩
    ext y
    rfl
  rw [relIndex, ← normalizerMonoidHom_comap_conj_range, index_comap]
  exact (relIndex_dvd_index_of_le hle).trans (by rw [component_outer_index I e])

public theorem normalizer_index_three_of_outside (I : Subgroup Model)
    (e : I ≃* SuzukiMatrixGroup 1)
    (hout : ∃ g ∈ normalizer (I : Set Model), g ∉ I ⊔ centralizer (I : Set Model)) :
    (I ⊔ centralizer (I : Set Model)).relIndex (normalizer (I : Set Model)) = 3 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (normalizer_index_dvd_three I e) with h | h
  · obtain ⟨g, hg, hnot⟩ := hout
    exact (hnot (relIndex_eq_one.mp h hg)).elim
  · exact h

/-- Full outer index and an elementary kernel produce the exact cubic field
automorphism, rather than merely a faithful cyclic outer action. -/
public theorem exists_exact_field_actor (I : Subgroup Model) (e : I ≃* SuzukiMatrixGroup 1)
    (hindex : (I ⊔ centralizer (I : Set Model)).relIndex (normalizer (I : Set Model)) = 3)
    (hkernel : ∀ x ∈ centralizer (I : Set Model), x ^ 2 = 1) :
    ∃ y : normalizer (I : Set Model), orderOf (y : Model) = 3 ∧
      I.normalizerMonoidHom y = MulAut.congr e.symm (suzukiFieldAutomorphism 1) := by
  let φ := MulAut.congr e.symm (suzukiFieldAutomorphism 1)
  have hφ3 : φ ^ 3 = 1 := by
    change (MulAut.congr e.symm (suzukiFieldAutomorphism 1)) ^ 3 = 1
    rw [← map_pow, suzukiFieldAutomorphism_one_cube, map_one]
  have hφne : φ ≠ 1 := by
    intro he
    apply suzukiFieldAutomorphism_one_ne_one
    exact (MulAut.congr e.symm).injective (he.trans (map_one _).symm)
  have hsurj := normalizerMonoidHom_surjective_of_outer_index I
    (hindex.trans (component_outer_index I e).symm)
  obtain ⟨x, hx⟩ := hsurj φ
  have hker : x ^ 3 ∈ I.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx, hφ3]
  rw [normalizerMonoidHom_ker] at hker
  have hx6 : x ^ 6 = 1 := by
    apply Subtype.ext
    change (x : Model) ^ 6 = 1
    calc
      (x : Model) ^ 6 = ((x : Model) ^ 3) ^ 2 := pow_mul _ 3 2
      _ = 1 := hkernel ((x : Model) ^ 3) hker
  have hy3 : (x ^ 4) ^ 3 = 1 := by
    calc
      (x ^ 4) ^ 3 = (x ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [hx6, one_pow]
  have hyφ : I.normalizerMonoidHom (x ^ 4) = φ := by
    rw [map_pow, hx]
    calc
      φ ^ 4 = φ ^ 3 * φ := pow_succ φ 3
      _ = φ := by rw [hφ3, one_mul]
  have hyne : x ^ 4 ≠ 1 := by
    intro he
    exact hφne (hyφ.symm.trans (he ▸ I.normalizerMonoidHom.map_one))
  refine ⟨x ^ 4, ?_, hyφ⟩
  exact (orderOf_injective (normalizer (I : Set Model)).subtype
    (normalizer (I : Set Model)).subtype_injective (x ^ 4)).trans
      (orderOf_eq_prime hy3 hyne)

end Rudvalis.CoveringIncidence.NormalizerGeometry.CubicExtension
