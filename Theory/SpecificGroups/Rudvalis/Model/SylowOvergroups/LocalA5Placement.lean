module
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action

/-!
# Placement of the local A₅ section in Rudvalis

A local subnormal subgroup of order 2¹¹·60 with two-core of order 2¹¹ embeds
as an index-two subgroup of the actual max6 word subgroup. Its nontrivial
radical lies in the radical of its Sylow supplement. The certified elementary
normalizer catalogue places that supplement in max4 or max6; divisibility
excludes max4. This retains the actual ambient map, not just the carrier name.

Source application: Aschbacher–Smith A.3.14 and 10.2.9, printed pp.48–49
and 750–751, respectively.
-/

public section
open Subgroup Theory.GroupTheory
namespace Rudvalis.SylowOvergroups
open RadicalCoverage.LocalCover

private theorem localP_odd_index : ¬ 2 ∣ localP.index := by
  intro h
  apply RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
  rw [←localP.card_mul_index,IntrinsicSylow.localP_card]
  exact Nat.mul_dvd_mul_left 16384 h
private noncomputable def fixedSylow : Sylow 2 Model :=
  IntrinsicSylow.localP_isPGroup.toSylow localP_odd_index

private theorem fixed_twoLocal_cover (M : Subgroup Model) (hM : IsTwoLocal M)
    (hPM : localP ≤ M) :
    (∃ e : Model ≃* Model, M.map e.toMonoidHom ≤ max4) ∨
    (∃ e : Model ≃* Model, M.map e.toMonoidHom ≤ max6) := by
  obtain ⟨U,hU,hp,rfl⟩ := hM
  have hUP : U ≤ localP :=
    sup_eq_left.mp (fixedSylow.is_maximal'
      (fixedSylow.isPGroup'.to_sup_of_normal_right' hp hPM) le_sup_left)
  obtain ⟨E,hE,hEU,he,hNE⟩ := exists_nontrivial_elementary_with_normalizer_le U hp hU
  obtain ⟨i,hi⟩ := elementaryCatalogue E hE (hEU.trans hUP) (hPM.trans hNE) he
  rw [hi] at hNE
  have hc := elementaryNormalizerCover_of_bounds max4NormalizerBounds max6NormalizerBounds i
  have transport (K : Subgroup Model) (g : Model)
      (hg : normalizer (E : Set Model) ≤ K.map (MulAut.conj g).toMonoidHom) :
      (normalizer (U : Set Model)).map (MulAut.conj g).symm.toMonoidHom ≤ K := by
    have hh := map_mono (f := (MulAut.conj g).symm.toMonoidHom)
      ((by simpa only [hi] using hNE : normalizer (U : Set Model) ≤ normalizer (E : Set Model)).trans hg)
    rw [map_map] at hh
    have hid : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id Model := by
      ext x
      exact (MulAut.conj g).symm_apply_apply x
    rwa [hid,map_id] at hh
  rcases hc with ⟨g,hg⟩ | ⟨g,hg⟩
  · exact Or.inl ⟨(MulAut.conj g).symm,transport max4 g (hi ▸ hg)⟩
  · exact Or.inr ⟨(MulAut.conj g).symm,transport max6 g (hi ▸ hg)⟩

/-- Every Sylow-containing two-local lies in one of the two marked word subgroups,
after transport by an actual ambient automorphism. -/
theorem twoLocal_cover (P : Sylow 2 Model) (M : Subgroup Model)
    (hM : IsTwoLocal M) (hPM : (P : Subgroup Model) ≤ M) :
    (∃ e : Model ≃* Model, M.map e.toMonoidHom ≤ max4) ∨
    (∃ e : Model ≃* Model, M.map e.toMonoidHom ≤ max6) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model P fixedSylow
  have hle : localP ≤ M.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hPM
    change ((g • P : Sylow 2 Model) : Subgroup Model) ≤ _ at hh
    rw [hg] at hh
    exact hh
  rcases fixed_twoLocal_cover _ (Theory.Quasithin.isTwoLocal_map (MulAut.conj g) hM) hle with
    ⟨e,he⟩ | ⟨e,he⟩
  · refine Or.inl ⟨(MulAut.conj g).trans e,?_⟩
    rw [map_map] at he
    have hcomp : ((MulAut.conj g).trans e).toMonoidHom =
        e.toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      rfl
    rwa [hcomp]
  · refine Or.inr ⟨(MulAut.conj g).trans e,?_⟩
    rw [map_map] at he
    have hcomp : ((MulAut.conj g).trans e).toMonoidHom =
        e.toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      rfl
    rwa [hcomp]

/-- A subnormal local subgroup with the source Ru A5 order has a marked embedding
as an index-two subgroup of the actual max6 carrier. -/
theorem local_a5_max6_placement (P : Sylow 2 Model) (B : Subgroup Model)
    (hB : (B.subgroupOf (B ⊔ (P : Subgroup Model))).IsSubnormal)
    (hcard : Nat.card B = 122880) (hcore : Nat.card (pCore 2 B) = 2048) :
    ∃ C : Subgroup max6, C.Normal ∧ Nonempty (B ≃* C) := by
  let H := B ⊔ (P : Subgroup Model)
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro hzero
    have hle := map_mono (f := H.subtype) (pCoreIn_le_of_subnormal 2 hB)
    rw [pCoreIn_subgroupOf 2 B H le_sup_left,map_subgroupOf_eq_of_le
      ((B.pCoreIn_le 2).trans le_sup_left)] at hle
    change B.pCoreIn 2 ≤ H.pCoreIn 2 at hle
    rw [hzero] at hle
    have hb := congrArg (fun K : Subgroup Model => Nat.card K) (le_bot_iff.mp hle)
    rw [pCoreIn,card_map_of_injective B.subtype_injective,hcore,card_bot] at hb
    omega
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set Model) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hlocal : IsTwoLocal (normalizer (H.pCoreIn 2 : Set Model)) :=
    ⟨_,hQ,isPGroup_pCoreIn 2 H,rfl⟩
  rcases twoLocal_cover P _ hlocal (le_sup_right.trans hHN) with ⟨e,he⟩ | ⟨e,he⟩
  · have hd := card_dvd_of_le ((map_mono (le_sup_left.trans hHN)).trans he)
    rw [card_map_of_injective e.injective,hcard,max4_card] at hd
    norm_num at hd
  · have hle : B.map e.toMonoidHom ≤ max6 :=
      (map_mono (le_sup_left.trans hHN)).trans he
    let C := (B.map e.toMonoidHom).subgroupOf max6
    let ec : B ≃* C :=
      (B.equivMapOfInjective e.toMonoidHom e.injective).trans (subgroupOfEquivOfLe hle).symm
    have hc : Nat.card C = 122880 := (Nat.card_congr ec.toEquiv).symm.trans hcard
    have hi : C.index = 2 := by
      have hh := C.card_mul_index
      rw [hc,max6_card] at hh
      omega
    exact ⟨C,normal_of_index_eq_two hi,⟨ec⟩⟩

/-- The source-sized local subgroup has the actual max6 two-core. -/
theorem local_a5_core_equiv (P : Sylow 2 Model) (B : Subgroup Model)
    (hB : (B.subgroupOf (B ⊔ (P : Subgroup Model))).IsSubnormal)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hcore : Nat.card (pCore 2 B) = 2048) :
    Nonempty (pCore 2 B ≃* pCore 2 max6) := by
  have hindex : (pCore 2 B).index = 60 := by
    change Nat.card (B ⧸ pCore 2 B) = 60
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hcard : Nat.card B = 122880 := by
    have hh := (pCore 2 B).card_mul_index
    rw [hcore,hindex] at hh
    omega
  obtain ⟨C,hC,⟨f⟩⟩ := local_a5_max6_placement P B hB hcard hcore
  let := hC
  let g := (f.subgroupMap (pCore 2 B)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 f))
  have hc : Nat.card (pCore 2 C) = 2048 := (Nat.card_congr g.toEquiv).symm.trans hcore
  have hle := pCoreIn_le_of_subnormal 2 hC.isSubnormal
  have he : C.pCoreIn 2 = pCore 2 max6 := by
    apply eq_of_le_of_card_ge hle
    rw [pCoreIn,card_map_of_injective C.subtype_injective,hc,
      ←CoreQuotients.max6FiveAction_ker,CoreQuotients.max6FiveAction_kernel_card]
  exact ⟨g.trans (((pCore 2 C).equivMapOfInjective C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr he))⟩


end Rudvalis.SylowOvergroups
