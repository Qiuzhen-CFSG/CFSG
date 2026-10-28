module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections.Model
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity

/-!
# Odd index of the literal radical–SU₃ subgroup

The radical–Levi subgroup has order `2^20 * 975`. To bound the ambient
two-part, place the normalizer of a nontrivial Sylow two-subgroup in an
isotropic stabilizer using its fixed radical. Isotropic transitivity moves
that stabilizer to one of the two marked parabolics. Their proved orders,
including the scalar factor five before projectivization, both have
two-part `2^20`. Thus `2^21` does not divide the ambient order and the
radical–Levi subgroup has odd index. No ambient order formula is required.

Source: the unitary parabolic geometry supporting Aschbacher–Smith
I.1.4(4), printed p.408, and F.1.12(7), printed pp.263–264.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
open LineCore LineCore.Parabolic IsotropicGeometry

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections

variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 5 F)

/-- The actual SU subgroup has the full defining-characteristic part. -/
theorem card_blockSubgroup (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    Nat.card (blockSubgroup J hJ) = 2 ^ 20 * 975 := by
  obtain ⟨c, hc⟩ := BenderSuzuki.External.huppert_II_10_4_trace_surjective J 4
    hcard (fixed_card_four J hcard hconj) 1 (map_one _)
  rw [← Nat.card_congr (blockEquiv J hJ).toEquiv, SemidirectProduct.card,
    Coord.card c hc, hcard, fixed_card_four J hcard hconj,
    card_identity_su3_four (middleForm J) hcard hconj rfl]
  norm_num

private theorem not_dvd_sylow_card (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (T : Sylow 2 J.specialSubgroup) : ¬ 2 ^ 21 ∣ Nat.card T := by
  by_cases hT : (T : Subgroup J.specialSubgroup) = ⊥
  · have ht : Nat.card T = 1 := by
      rw [hT]
      exact Nat.card_unique
    rw [ht]
    norm_num
  obtain ⟨W, hn, hi, _, hNW⟩ := twoLocal_stabilizes_isotropic J hJ
    (normalizer (T : Set J.specialSubgroup)) ⟨T, hT, T.isPGroup', rfl⟩
  obtain ⟨b, g, hg⟩ := IsotropicTransitivity.transitive J hcard hconj hJ W hn hi
  have hTW : (T : Subgroup J.specialSubgroup) ≤ specialStabilizer J W :=
    le_trans le_normalizer hNW
  have hdiv := Subgroup.card_dvd_of_le hTW
  have he : Nat.card (specialStabilizer J W) =
      Nat.card (specialStabilizer J (if b then plane F else line F)) := by
    rw [hg, specialStabilizer_map_action]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  rw [he, card_specialStabilizer J hconj hcard] at hdiv
  intro hd
  have hd' := hd.trans hdiv
  cases b
  · change 2 ^ 21 ∣ 5 * Nat.card (lineParabolic J) at hd'
    rw [card_lineParabolic_four J hcard hconj hJ] at hd'
    norm_num at hd'
  · change 2 ^ 21 ∣ 5 * Nat.card (planeParabolic J) at hd'
    rw [card_planeParabolic_four J hcard hconj hJ] at hd'
    norm_num at hd'

/-- Isotropic placement bounds only the needed two-part of the ambient order. -/
theorem not_dvd_special_card (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    ¬ 2 ^ 21 ∣ Nat.card J.specialSubgroup := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Sylow 2 J.specialSubgroup := Classical.choice inferInstance
  have hcop : Nat.Coprime (2 ^ 21) (T : Subgroup J.specialSubgroup).index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr T.not_dvd_index).pow_left 21
  intro hd
  apply not_dvd_sylow_card J hcard hconj hJ T
  apply hcop.dvd_mul_right.mp
  rwa [(T : Subgroup J.specialSubgroup).card_mul_index]

/-- The index required by central transfer is odd in SU₅ itself. -/
theorem blockSubgroup_index_odd (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1) :
    ¬ 2 ∣ (blockSubgroup J hJ).index := by
  intro hi
  apply not_dvd_special_card J hcard hconj hJ
  have hc : 2 ^ 20 ∣ Nat.card (blockSubgroup J hJ) := by
    rw [card_blockSubgroup J hcard hconj hJ]
    exact dvd_mul_right _ _
  have h := Nat.mul_dvd_mul hc hi
  rwa [(blockSubgroup J hJ).card_mul_index, ← pow_succ] at h

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections
