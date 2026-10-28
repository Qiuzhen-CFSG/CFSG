module
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Kernel
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.TrioTranslations
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.Coverage
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IndexNormal
/-!
# Normal eight-groups in M₂₄ Sylow overgroups of index 63

An overgroup of a Sylow two-subgroup with relative index 63 has order 64512.
The checked elementary catalogue reduces its possible normal eight-groups to
five literal rows. Four rows have their full normalizers in an octad stabilizer.
Such a stabilizer has no subgroup of order 64512: its A₈ quotient would have
an index-five subgroup, contrary to the faithful coset-action bound.
The fifth row has normalizer in a trio stabilizer of order 64512, and a
certified element of that stabilizer fails to normalize the row. Sylow
conjugacy transports the exclusion to every actual Sylow subgroup of M₂₄.

All finite checks use the existing native permutation enumeration and the Lean
kernel. No GAP normalizer order or unproved maximal-overgroup coverage is used.
The source consumer is Chapter12/Section05/NaturalSource/Local/PointCore/MathieuComponent.
Source: Aschbacher--Smith, 12.5.3 and 12.5.8(1), printed pp.818, 820;
GLS3, Table 5.3e, for the native octad and trio geometry.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.EightNormalizers
open LinearFourCore EvenCatalogue EvenCatalogue.NormalizerOvergroupsProof

private theorem simple_no_index_five {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hc : 120 < Nat.card G) (H : Subgroup G) (hi : H.index = 5) : False := by
  rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with hn | hn
  · have hd : H.normalCore.index ∣ H.index.factorial := by
      rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
      exact card_subgroup_dvd_card _
    rw [hn, index_bot, hi] at hd
    have hh := Nat.le_of_dvd (by decide : 0 < Nat.factorial 5) hd
    norm_num at hh
    omega
  · have he : H = ⊤ := top_unique (hn ▸ H.normalCore_le)
    simp [he] at hi

private theorem seed_no_order (H : Subgroup (octadStabilizer seedOctad))
    (hc : Nat.card H = 64512) : False := by
  let f := alternatingAction
  have hf : Function.Surjective f := alternatingAction_surjective
  have hA : Nat.card (alternatingGroup seedOctad.val) = 20160 := by
    rw [← action_range, action_range_card]
  have hi : H.index = 5 := by
    have hh := H.card_mul_index
    rw [hc, octadStabilizer_card] at hh
    omega
  have hm : (H.map f).index = 1 ∨ (H.map f).index = 5 :=
    (Nat.dvd_prime (by decide)).mp (hi ▸ H.index_map_dvd hf)
  rcases hm with hm | hm
  · have hd := H.card_map_dvd f
    rw [index_eq_one.mp hm, card_top, hA, hc] at hd
    norm_num at hd
  · let : IsSimpleGroup (alternatingGroup seedOctad.val) :=
      alternatingGroup.isSimpleGroup (by rw [seed_card]; decide)
    exact simple_no_index_five (by rw [hA]; decide) _ hm

/-- No native octad stabilizer has a subgroup of order 64512. -/
theorem octad_no_subgroup_order64512 (O : Octad) (H : Subgroup (octadStabilizer O))
    (hc : Nat.card H = 64512) : False := by
  obtain ⟨g,hg⟩ := exists_smul_octad_eq seedOctad O
  let e : octadStabilizer O ≃* octadStabilizer seedOctad :=
    (MulAction.stabilizerEquivStabilizer hg.symm).symm
  apply seed_no_order (H.map e.toMonoidHom)
  rw [card_map_of_injective e.injective, hc]

private def codes (i : Fin 22) : Finset (Fin 144) := Finset.univ.image (rowCode i)
private def encoded (i : Fin 22) (c : codes i) : subgroup i :=
  ⟨native c, by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp c.property
    exact hj ▸ row_mem i j⟩
private theorem encoded_bijective (i : Fin 22) : Function.Bijective (encoded i) := by
  constructor
  · intro c d he
    exact Subtype.ext (native_injective (congrArg Subtype.val he))
  · rintro ⟨a,ha⟩
    obtain ⟨j,rfl⟩ := (mem_subgroup_iff i a).mp ha
    exact ⟨⟨rowCode i j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩, rfl⟩
private theorem row_card (i : Fin 22) : Nat.card (subgroup i) = (codes i).card := by
  rw [← Nat.card_congr (Equiv.ofBijective (encoded i) (encoded_bijective i)),
    Nat.card_eq_fintype_card, Fintype.card_coe]
private theorem row_eight (i : Fin 22) (hc : Nat.card (subgroup i) = 8) :
    i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
  rw [row_card] at hc
  exact (show ∀ i : Fin 22, (codes i).card = 8 →
    i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by decide +kernel) i hc

private theorem trio_witness : FourNormalizers.certificateElement 2 ∉ localGroup 7 := by
  intro hn
  have hm := (mem_set_normalizer_iff.mp hn (rowElement 7 1)).mp (rowElement_mem 7 1)
  obtain ⟨j,hj⟩ := (mem_ambient_iff 7 _).mp hm
  have hh : ∀ j : Fin 64, ∃ x : Fin 24,
      FourNormalizers.certificatePerm 2 (point (rowCode 7 1)
        ((FourNormalizers.certificatePerm 2).symm x)) ≠ point (rowCode 7 j) x := by
    decide +kernel
  obtain ⟨x,hx⟩ := hh j
  apply hx
  have he := congrArg (fun a : M24 => a.val x) hj
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply,
    rowElement_apply, FourNormalizers.certificateElement, Equiv.Perm.inv_def] using he.symm

open PairOvergroups MathieuCode.TrioCalculation

private theorem trio_card : Nat.card trioGroup = 64512 := by
  have hq : Nat.card (trioStabilizer standardTrio ⧸ pCore 2 (trioStabilizer standardTrio)) = 1008 := by
    rw [Nat.card_congr standardQuotientEquiv.toEquiv]
    change Nat.card (Equiv.Perm (Fin 3) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = _
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Atlas.Comparisons.Exceptional.sl3Two_card]
    rfl
  have hh := (pCore 2 (trioStabilizer standardTrio)).card_mul_index
  rw [index_eq_card, hq, M24ChapterHStabilizers.TrioAction.core_card] at hh
  exact (Nat.card_congr FourNormalizers.trioEquiv.toEquiv).trans hh.symm

private theorem fixed_no_eight (A B : Subgroup M24)
    (hCA : SylowNormalizer.candidate ≤ A) (hBC : B ≤ SylowNormalizer.candidate)
    (hn : A ≤ normalizer (B : Set M24)) (hB : IsElementaryAbelian 2 B)
    (hcB : Nat.card B = 8) (hcA : Nat.card A = 64512) : False := by
  let R := B.subgroupOf SylowNormalizer.candidate
  have hnR : R.Normal := normal_subgroupOf_of_le_normalizer (hCA.trans hn)
  have hcard : Nat.card R = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv).trans hcB
  have hne : R ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcard
    omega
  let := hB
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hBC
  obtain ⟨i,hi⟩ := EvenCatalogue.Coverage.catalogue_of_normal_exponent_two R hne hnR
    (fun x hx => by simpa only [pow_two] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx)
  have he : B = ambient i := by
    have hh := congrArg (map SylowNormalizer.candidate.subtype) hi
    rw [map_subgroupOf_eq_of_le hBC] at hh
    exact hh
  have hnorm : A ≤ localGroup i := by
    change A ≤ normalizer (ambient i : Set M24)
    rwa [← he]
  have rows := row_eight i (hi ▸ hcard)
  have hoct (hAo : A ≤ octadStabilizer commonOctad) : False :=
    octad_no_subgroup_order64512 commonOctad (A.subgroupOf _) ((Nat.card_congr
      (subgroupOfEquivOfLe hAo).toEquiv).trans hcA)
  rcases rows with rfl | rfl | rfl | rfl | rfl
  · exact hoct (hnorm.trans (octadRow_le_octad 3))
  · exact hoct (hnorm.trans (octadRow_le_octad 4))
  · exact hoct (hnorm.trans (octadRow_le_octad 5))
  · have hAt : A ≤ trioGroup := hnorm.trans (trioRow_le_trio 1)
    have heq : A = trioGroup := eq_of_le_of_card_ge hAt (by rw [hcA, trio_card])
    exact trio_witness (hnorm (heq.symm ▸ FourNormalizers.trio_witness_mem))
  · exact hoct (hnorm.trans (octadRow_le_octad 6))

/-- An index-63 Sylow overgroup cannot normalize an elementary eight in its Sylow. -/
theorem no_eight_of_sylow_index (S : Sylow 2 M24) (A B : Subgroup M24)
    (hSA : (S : Subgroup M24) ≤ A) (hBS : B ≤ S)
    (hn : A ≤ normalizer (B : Set M24)) (hB : IsElementaryAbelian 2 B)
    (hcB : Nat.card B = 8) (hi : (S : Subgroup M24).relIndex A = 63) : False := by
  have hS : Nat.card S = 1024 := by
    rw [S.card_eq_multiplicity, m24_order]
    decide +kernel
  have hcA : Nat.card A = 64512 := by
    have hh := ((S : Subgroup M24).subgroupOf A).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hSA).toEquiv, hS] at hh
    change 1024 * (S : Subgroup M24).relIndex A = Nat.card A at hh
    rw [hi] at hh
    exact hh.symm
  let P : Sylow 2 M24 := Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card, m24_order]; decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S P
  let e := MulAut.conj g
  have hmap : (S : Subgroup M24).map e.toMonoidHom = SylowNormalizer.candidate :=
    congrArg Sylow.toSubgroup hg
  let := hB
  apply fixed_no_eight (A.map e.toMonoidHom) (B.map e.toMonoidHom)
  · rw [← hmap]; exact map_mono hSA
  · rw [← hmap]; exact map_mono hBS
  · exact (map_mono hn).trans (B.le_normalizer_map _)
  · exact IsElementaryAbelian.map _
  · rw [card_map_of_injective e.injective, hcB]
  · rw [card_map_of_injective e.injective, hcA]

/-- No normal elementary eight occurs in an index-63 Sylow overgroup of native M₂₄. -/
theorem no_normal_eight_of_sylow_index (S : Sylow 2 M24) (A : Subgroup M24)
    (hSA : (S : Subgroup M24) ≤ A) (hi : (S : Subgroup M24).relIndex A = 63)
    (B : Subgroup A) [B.Normal] (hB : IsElementaryAbelian 2 B)
    (hcB : Nat.card B = 8) : False := by
  let := hB
  let E := B.map A.subtype
  have hBS : B ≤ (S.subtype hSA : Subgroup A) :=
    (IsElementaryAbelian.isPGroup 2 B).le_sylow_of_normal _
  have hES : E ≤ S := by
    have hh := map_mono (f := A.subtype) hBS
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hSA] at hh
  have hn : A ≤ normalizer (E : Set M24) := by
    apply le_trans ?_ (B.le_normalizer_map A.subtype)
    intro a ha
    refine ⟨⟨a,ha⟩, ?_, rfl⟩
    rw [normalizer_eq_top]
    exact mem_top _
  exact no_eight_of_sylow_index S A E hSA hES hn (IsElementaryAbelian.map _) (by
    rw [card_map_of_injective A.subtype_injective, hcB]) hi

end Sporadic.Mathieu.M24LocalGeometry.EightNormalizers
