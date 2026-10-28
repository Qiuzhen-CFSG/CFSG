module
public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementaryComparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality
/-!
# Normalizers of Sylow-invariant elementary sixteen-groups in Rudvalis

Conjugate the full Sylow to its native representative and apply the six-row
normal elementary subgroup catalogue. The first row has order two; the last
contains seventeen distinct explicit words, separated by their images at two
points. Every other row has normalizer in the specified maximal subgroup of
order 344064, which is prime to five.

This supplies the actual marked elementary-layer obstruction used by the
deleted-five case of Aschbacher–Smith A.3.14 and 10.2.1. The local catalogue
and maximal subgroup markings follow GLS3, Table 5.3r.
-/

public section
open Subgroup Theory.GroupTheory
namespace Rudvalis.SylowElementarySixteen
open SylowOvergroups RadicalCoverage.LocalCover CatalogueCertificate

private def seventeenWords : Fin 17 → Model :=
  ![1,
    elementaryGenerator 0,
    elementaryGenerator 1,
    elementaryGenerator 0 * elementaryGenerator 1,
    elementaryGenerator 2,
    elementaryGenerator 0 * elementaryGenerator 2,
    elementaryGenerator 1 * elementaryGenerator 2,
    elementaryGenerator 0 * elementaryGenerator 1 * elementaryGenerator 2,
    elementaryGenerator 3,
    elementaryGenerator 0 * elementaryGenerator 3,
    elementaryGenerator 1 * elementaryGenerator 3,
    elementaryGenerator 0 * elementaryGenerator 1 * elementaryGenerator 3,
    elementaryGenerator 2 * elementaryGenerator 3,
    elementaryGenerator 0 * elementaryGenerator 2 * elementaryGenerator 3,
    elementaryGenerator 1 * elementaryGenerator 2 * elementaryGenerator 3,
    elementaryGenerator 0 * elementaryGenerator 1 * elementaryGenerator 2 * elementaryGenerator 3,
    elementaryGenerator 5]
private def seventeenPerms : Fin 17 → Equiv.Perm (Fin 4060) :=
  ![1,
    elementaryPermutation 0,
    elementaryPermutation 1,
    elementaryPermutation 0 * elementaryPermutation 1,
    elementaryPermutation 2,
    elementaryPermutation 0 * elementaryPermutation 2,
    elementaryPermutation 1 * elementaryPermutation 2,
    elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2,
    elementaryPermutation 3,
    elementaryPermutation 0 * elementaryPermutation 3,
    elementaryPermutation 1 * elementaryPermutation 3,
    elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 3,
    elementaryPermutation 2 * elementaryPermutation 3,
    elementaryPermutation 0 * elementaryPermutation 2 * elementaryPermutation 3,
    elementaryPermutation 1 * elementaryPermutation 2 * elementaryPermutation 3,
    elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2 * elementaryPermutation 3,
    elementaryPermutation 5]

private theorem seventeen_eq (i : Fin 17) :
    seventeenPerms i = modelSubgroup.subtype (seventeenWords i) := by
  fin_cases i <;> simp only [seventeenPerms,seventeenWords,elementaryPermutation_eq] <;> rfl

private theorem seventeen_mem (i : Fin 17) : seventeenWords i ∈ elementary 5 := by
  have h0 : elementaryGenerator 0 ∈ elementary 5 := subset_closure (by simp)
  have h1 : elementaryGenerator 1 ∈ elementary 5 := subset_closure (by simp)
  have h2 : elementaryGenerator 2 ∈ elementary 5 := subset_closure (by simp)
  have h3 : elementaryGenerator 3 ∈ elementary 5 := subset_closure (by simp)
  have h5 : elementaryGenerator 5 ∈ elementary 5 := subset_closure (by simp)
  fin_cases i
  · exact (elementary 5).one_mem
  · exact h0
  · exact h1
  · exact ((elementary 5).mul_mem h0 h1)
  · exact h2
  · exact ((elementary 5).mul_mem h0 h2)
  · exact ((elementary 5).mul_mem h1 h2)
  · exact ((elementary 5).mul_mem ((elementary 5).mul_mem h0 h1) h2)
  · exact h3
  · exact ((elementary 5).mul_mem h0 h3)
  · exact ((elementary 5).mul_mem h1 h3)
  · exact ((elementary 5).mul_mem ((elementary 5).mul_mem h0 h1) h3)
  · exact ((elementary 5).mul_mem h2 h3)
  · exact ((elementary 5).mul_mem ((elementary 5).mul_mem h0 h2) h3)
  · exact ((elementary 5).mul_mem ((elementary 5).mul_mem h1 h2) h3)
  · exact ((elementary 5).mul_mem ((elementary 5).mul_mem ((elementary 5).mul_mem h0 h1) h2) h3)
  · exact h5

private theorem seventeen_separated :
    Function.Injective (fun i => (seventeenPerms i 0,seventeenPerms i 1)) := by
  decide +kernel

private theorem seventeen_le_card_elementary_five : 17 ≤ Nat.card (elementary 5) := by
  let f : Fin 17 → elementary 5 := fun i => ⟨seventeenWords i,seventeen_mem i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply seventeen_separated
    simpa only [seventeen_eq] using congrArg
      (fun z : elementary 5 => (modelSubgroup.subtype z.val 0,modelSubgroup.subtype z.val 1)) h
  simpa using Nat.card_le_card_of_injective f hf

private theorem zero_card_le_two : Nat.card (elementary 0) ≤ 2 := by
  change Nat.card (closure {elementaryGenerator 0}) ≤ 2
  rw [← zpowers_eq_closure,Nat.card_zpowers,Max6Certificate.elementary_zero_order]

/-- An elementary sixteen-group normalized by a full Sylow has a five-free normalizer. -/
theorem normalizer_sixteen_not_five (S : Sylow 2 Model)
    (U : Subgroup Model) (he : IsElementaryAbelian 2 U) (hc : Nat.card U = 16)
    (hn : (S : Subgroup Model) ≤ normalizer (U : Set Model)) :
    ¬ 5 ∣ Nat.card (normalizer (U : Set Model)) := by
  let := he
  have hUS : U ≤ S := by
    have hh := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right'
      (IsElementaryAbelian.isPGroup 2 U) hn) le_sup_left
    exact sup_eq_left.mp hh
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S SylowInvariantPair.sylow
  let e := MulAut.conj g
  let V := U.map e.toMonoidHom
  have hVP : V ≤ localP := by
    have hh := map_mono (f := e.toMonoidHom) hUS
    change U.map e.toMonoidHom ≤ (g • S : Sylow 2 Model) at hh
    rw [hg] at hh
    exact hh
  have hPN : localP ≤ normalizer (V : Set Model) := by
    have hh := (map_mono (f := e.toMonoidHom) hn).trans (le_normalizer_map e.toMonoidHom)
    change ((g • S : Sylow 2 Model) : Subgroup Model) ≤ _ at hh
    rw [hg] at hh
    exact hh
  have hVc : Nat.card V = 16 := (card_map_of_injective e.injective).trans hc
  have hVne : V ≠ ⊥ := by intro hh; rw [hh,card_bot] at hVc; omega
  obtain ⟨i,hi⟩ := elementaryCatalogue V hVne hVP hPN (IsElementaryAbelian.map e.toMonoidHom)
  have hi0 : i ≠ 0 := by
    intro hh
    rw [hi,hh] at hVc
    have := zero_card_le_two
    omega
  have hi5 : i ≠ 5 := by
    intro hh
    rw [hi,hh] at hVc
    have := seventeen_le_card_elementary_five
    omega
  have hNV : normalizer (V : Set Model) ≤ max4 := hi ▸ max4NormalizerBounds i hi0 hi5
  intro hd
  have hNcard : Nat.card (normalizer (V : Set Model)) = Nat.card (normalizer (U : Set Model)) := by
    rw [show V=U.map e.toMonoidHom from rfl,←map_equiv_normalizer_eq,card_map_of_injective e.injective]
  have hb : 5 ∣ Nat.card max4 := (hNcard ▸ hd).trans (card_dvd_of_le hNV)
  rw [max4_card] at hb
  norm_num at hb
end Rudvalis.SylowElementarySixteen
