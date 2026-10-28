module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative

/-!
# Normal elementary sixteen-subgroups in Held

Every elementary subgroup of order sixteen normalized by a full Sylow
two-subgroup has normalizer of order prime to five. Conjugating the Sylow
to the certified representative gives one of rows9–17 of the existing
22-row table. Six rows have normalizers inside the known max5 conjugate;
two preserve a reconstructed four-group, whose automorphism group has
order dividing24 and whose centralizer is contained in that same local.
The remaining row has normalizer order9216 by existing matching bounds.

The argument reuses the literal subgroup words and their checked member
lists; no new permutation enumeration or model-recognition premise enters.
This is the Held input to the deleted-five local-block exclusion in
Aschbacher–Smith A.3.14 and10.2.1, printed pp.49–50,743;
the underlying local calculations are GLS3 Table5.3p.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held
open LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
open TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment

private theorem entry_card (j : Fin 22) :
    Nat.card (entry j) = (members (some j)).toFinset.card := by
  classical
  have hinj : Function.Injective normalForm := by
    apply (normalForm_surjective.bijective_of_nat_card_le ?_).1
    simpa only [Nat.card_fin] using
      InnerNormalizer.representative_card_ge_of_orbit_labels
        InnerNormalizer.orbitSizeLabel_eq_card_orbit
  let f : (members (some j)).toFinset → entry j := fun m =>
    ⟨normalForm m, (certified_members (some j) _).mpr ⟨m, List.mem_toFinset.mp m.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · intro x
      obtain ⟨m, hm, he⟩ := (certified_members (some j) x).mp x.property
      exact ⟨⟨m, List.mem_toFinset.mpr hm⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_finsetCard]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem entry_card_sixteen (j : Fin 22) (hc : Nat.card (entry j) = 16) :
    j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by
  rw [entry_card] at hc
  have h : ∀ j : Fin 22, (members (some j)).toFinset.card = 16 →
      j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by
    decide +kernel
  exact h j hc

private theorem small_row_card (j : Fin 22) (hj : j = 1 ∨ j = 3) :
    Nat.card (ambient j) = 4 := by
  rw [ambient,card_map_of_injective representative.subtype_injective,entry_card]
  rcases hj with rfl | rfl <;> decide +kernel

private theorem not_five_dvd_common_centralizer :
    ¬ 5 ∣ Nat.card (centralizer ({centralWord} : Set He)) := by
  intro h
  have hd := h.trans (card_dvd_of_le (centralWord_centralizer_le representative_isPGroup))
  change 5 ∣ Nat.card CentralizerCertificates.UpperBounds.overgroup at hd
  rw [CentralizerCertificates.UpperBounds.overgroup_card] at hd
  norm_num at hd

private theorem not_five_dvd_row_centralizer (j : Fin 22) :
    ¬ 5 ∣ Nat.card (centralizer (ambient j : Set He)) := by
  intro h
  exact not_five_dvd_common_centralizer (h.trans (card_dvd_of_le
    (CentralizerCertificates.ambient_centralizer_le_common j)))

private theorem not_five_dvd_small_normalizer (j : Fin 22) (hj : j = 1 ∨ j = 3) :
    ¬ 5 ∣ Nat.card (normalizer (ambient j : Set He)) := by
  let f := (ambient j).normalizerMonoidHom
  have hAut : Nat.card (MulAut (ambient j)) ∣ 24 := by
    have hd := card_dvd_of_injective (MulAut.toPerm (ambient j)) MulEquiv.toEquiv_injective
    simpa only [Nat.card_perm,small_row_card j hj,show Nat.factorial 4 = 24 by decide] using hd
  have hrange : Nat.card f.range ∣ 24 := f.range.card_subgroup_dvd_card.trans hAut
  have hker : Nat.card f.ker = Nat.card (centralizer (ambient j : Set He)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (ambient j : Set He))).toEquiv]
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  intro hd
  rw [← hprod] at hd
  rcases (show Nat.Prime 5 by decide).dvd_mul.mp hd with hk | hi
  · exact not_five_dvd_row_centralizer j (hker ▸ hk)
  · have hh := hi.trans hrange
    norm_num at hh

private theorem not_five_dvd_normalizer_zero :
    ¬ 5 ∣ Nat.card (normalizer (ambient 0 : Set He)) := by
  rw [normalizer_ambient_zero_eq_centralizer]
  exact not_five_dvd_common_centralizer

private theorem not_five_dvd_normalizer_twelve :
    ¬ 5 ∣ Nat.card (normalizer (ambient 12 : Set He)) := by
  have hl := Row12.wordSubgroup_card_ge.trans
    (Nat.card_le_card_of_injective (inclusion Row12.wordSubgroup_le_normalizer12)
      (inclusion_injective Row12.wordSubgroup_le_normalizer12))
  have he := Nat.le_antisymm Row12.normalizer_card_le hl
  rw [he]
  decide

private theorem not_five_dvd_sixteen_row_normalizer (j : Fin 22)
    (hc : Nat.card (entry j) = 16) :
    ¬ 5 ∣ Nat.card (normalizer (ambient j : Set He)) := by
  have hmax (k : Fin 5) (hk : k.val < 3) :
      ¬ 5 ∣ Nat.card (normalizer (ambient (distinguished k) : Set He)) := by
    intro h
    exact not_five_dvd_common_centralizer (h.trans (card_dvd_of_le
      (rankFour_normalizer_le_centralizer k hk)))
  have hcentral (j : Fin 22) (hj : ∀ k : Fin 5, j ≠ distinguished k)
      (hzero : container j = 0) : ¬ 5 ∣ Nat.card (normalizer (ambient j : Set He)) := by
    intro h
    apply not_five_dvd_normalizer_zero
    exact h.trans (card_dvd_of_le (hzero ▸ normalizer_le_container_normalizer j hj))
  rcases entry_card_sixteen j hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hmax 1 (by decide)
  · intro h
    apply not_five_dvd_small_normalizer 1 (Or.inl rfl)
    exact h.trans (card_dvd_of_le (fixedPointSpan_ambient10_eq_ambient1 ▸
      normalizer_le_fixedPointSpan (ambient 10) 42))
  · exact hmax 2 (by decide)
  · exact not_five_dvd_normalizer_twelve
  · exact hcentral 13 (by decide +kernel) rfl
  · exact hcentral 14 (by decide +kernel) rfl
  · exact hcentral 15 (by decide +kernel) rfl
  · intro h
    apply not_five_dvd_small_normalizer 3 (Or.inr rfl)
    exact h.trans (card_dvd_of_le (fixedPointSpan_ambient16_eq_ambient3 ▸
      normalizer_le_fixedPointSpan (ambient 16) 42))
  · exact hcentral 17 (by decide +kernel) rfl

/-- An elementary sixteen-subgroup normalized by a full Sylow of Held has
normalizer order prime to five. Normality is relative to the marked Sylow. -/
theorem sylow_normal_sixteen_normalizer_not_five
    (T : Sylow 2 He) (W : Subgroup He)
    (hWT : W ≤ (T : Subgroup He)) (hWE : IsElementaryAbelian 2 W)
    (hWc : Nat.card W = 16) (hTN : (T : Subgroup He) ≤ normalizer (W : Set He)) :
    ¬ 5 ∣ Nat.card (normalizer (W : Set He)) := by
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup
    InnerNormalizer.normalizer_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq He T P
  have hTP : (T : Subgroup He).map (MulAut.conj g).toMonoidHom = representative := by
    change ((g • T : Sylow 2 He) : Subgroup He) = representative
    rw [hg, hP]
  let U := W.map (MulAut.conj g).toMonoidHom
  have hUP : U ≤ representative := by
    rw [← hTP]
    exact map_mono hWT
  have hPN : representative ≤ normalizer (U : Set He) := by
    rw [← hTP, ← map_equiv_normalizer_eq W (MulAut.conj g)]
    exact map_mono hTN
  let R := U.subgroupOf representative
  let : IsElementaryAbelian 2 W := hWE
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hRE : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hUP
  have hRn : R.Normal := (normal_subgroupOf_iff_le_normalizer hUP).mpr hPN
  have hRc : Nat.card R = 16 := by
    calc
      Nat.card R = Nat.card U := Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv
      _ = Nat.card W := card_map_of_injective (MulAut.conj g).injective
      _ = 16 := hWc
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hRc
    omega
  obtain ⟨j, hj⟩ := intrinsicEnumeration representative_isPGroup R hRne hRn hRE
  have he : U = ambient j := by
    change U = (entry j).map representative.subtype
    rw [← hj]
    exact (map_subgroupOf_eq_of_le hUP).symm
  have hnot := not_five_dvd_sixteen_row_normalizer j (hj ▸ hRc)
  rw [← he, ← map_equiv_normalizer_eq W (MulAut.conj g),
    card_map_of_injective (MulAut.conj g).injective] at hnot
  exact hnot

end Held
