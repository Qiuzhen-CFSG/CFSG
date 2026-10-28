module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreAction
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Component

/-!
# The original eight-field component is normal in its partner

The full source H is perfect and its literal quotient is PSL₂(8). Equality
of the original cores identifies its quotient Sylow with the full partner
quotient Sylow of order eight. The existing C-component non-enlargement
argument therefore identifies the normal containing component with H itself.
This gives N_G(H)=Mc and the original overlap factorization, with no marked
triality realization.

Source: Aschbacher--Smith A.3.12 and 14.2.18, printed pp.48,987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceNormal
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterA.Section03.SourceEmbeddings.EightSylow
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

private theorem first_quotient_quasisimple :
    IsQuasisimple (H ⧸ pCore 2 H) := by
  let := SourcePerfect.first_perfect hG T hempty hM hu hmany hcard e H hH eR
  let f := (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 3 (by decide)]; decide)⟩
  exact IsQuasisimple.of_mulEquiv f.symm

/-- Every Sylow in the literal quotient is elementary of order eight. -/
private theorem first_quotient_sylow
    (S : Sylow 2 (H ⧸ pCore 2 H)) : IsElementaryAbelian 2 S ∧ Nat.card S = 8 := by
  let f := sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR
  let S' := S.mapSurjective (f := f.toMonoidHom) f.surjective
  let d : S ≃* S' := (S : Subgroup (H ⧸ pCore 2 H)).equivMapOfInjective
    f.toMonoidHom f.injective
  have he := Theory.PSL2.OrdinaryBorel.sylow_elementary S'
  let := he
  refine ⟨IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective, ?_⟩
  rw [Nat.card_congr d.toEquiv, Theory.PSL2.OrdinaryBorel.sylow_card]
  exact GaloisField.card 2 3 (by decide)


private theorem first_mem_local_family :
    H ∈ Chapter1.LIn Mc (T : Subgroup G) := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  let := SourcePerfect.first_perfect hG T hempty hM hu hmany hcard e H hH eR
  let := first_quotient_quasisimple hG T hempty hM hu hmany hcard e H hH eR
  refine Chapter1.mem_LIn_of_normalized_perfect
    (H := Mc) (S := (T : Subgroup G)) ?_ hHM (hH.1.1.2.trans H.le_normalizer) ?_
  · refine ⟨T.subtype (hH.1.1.2.trans hHM), ?_⟩
    exact map_subgroupOf_eq_of_le (hH.1.1.2.trans hHM)
  · intro he
    have hc := (source_core_orders hG T hempty hM hu hmany hcard e H hH eR).1
    rw [he, card_bot] at hc
    norm_num at hc

/-- Original 1.2.4 supplies a unique normal containing component in Mc.
The remaining non-enlargement argument must still identify it with H. -/
private theorem first_normal_containing_component :
    ∃! C : Subgroup Mc, C.IsCComponent ∧ H.subgroupOf Mc ≤ C ∧ C.Normal := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  have hL : H.subgroupOf Mc ∈ Chapter1.L Mc S :=
    (Chapter1.mem_LIn_iff_subgroupOf hTM hHM).mp
      (first_mem_local_family hG T hempty hM hu hmany hcard e H hH eR)
  have hn : (S : Subgroup Mc) ≤ normalizer (H.subgroupOf Mc : Set Mc) := by
    rw [← subgroupOf_normalizer_eq hHM]
    exact comap_mono (hH.1.1.2.trans H.le_normalizer)
  have hmem : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  exact Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (ChapterE.Structure.sqtk_two_quotient (hG.twoLocal_sqtk hmem.1.1)
      (pCore 2 Mc) pCore_isPGroup) S hL hn


/-- Equality of the original embedded cores identifies the kernel of the
inclusion followed by the partner quotient. -/
private theorem first_core_comap :
    (pCore 2 Mc).comap (inclusion
      (source_first_le_partner hG hempty hM hu hmany hcard e hH)) = pCore 2 H := by
  rw [← SourceCoreAction.partner_action_kernel hG T hempty hM hu hmany hcard e H hH eR]
  exact SourceCoreAction.first_action_kernel hG T hempty hM hu hmany hcard e H hH eR

/-- The literal first-quotient inclusion in the original partner quotient. -/
private def firstQuotientMap :
    (H ⧸ pCore 2 H) →* (Mc ⧸ pCore 2 Mc) :=
  QuotientGroup.map _ _ (inclusion
    (source_first_le_partner hG hempty hM hu hmany hcard e hH))
      (first_core_comap hG T hempty hM hu hmany hcard e H hH eR).ge

private theorem firstQuotientMap_mk (x : H) :
    firstQuotientMap hG T hempty hM hu hmany hcard e H hH eR
      (QuotientGroup.mk' (pCore 2 H) x) =
        QuotientGroup.mk' (pCore 2 Mc) (inclusion
          (source_first_le_partner hG hempty hM hu hmany hcard e hH) x) := rfl

private theorem firstQuotientMap_injective :
    Function.Injective (firstQuotientMap hG T hempty hM hu hmany hcard e H hH eR) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
  apply (QuotientGroup.eq_one_iff y).mpr
  rw [← first_core_comap hG T hempty hM hu hmany hcard e H hH eR]
  change inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) y ∈ pCore 2 Mc
  apply (QuotientGroup.eq_one_iff _).mp
  exact hx

omit eR in
/-- The original Sylow in Mc, with its actual image modulo O₂(Mc). -/
private def partnerQuotientSylow : Sylow 2 (Mc ⧸ pCore 2 Mc) :=
  (T.subtype (hH.1.1.2.trans
    (source_first_le_partner hG hempty hM hu hmany hcard e hH))).mapSurjective
      (QuotientGroup.mk'_surjective (pCore 2 Mc))

/-- The first quotient inclusion carries the source Sylow onto the whole
partner quotient Sylow, not merely into it. -/
private theorem first_quotient_sylow_map :
    (((T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)) :
      Sylow 2 (H ⧸ pCore 2 H)) : Subgroup (H ⧸ pCore 2 H)).map
        (firstQuotientMap hG T hempty hM hu hmany hcard e H hH eR) =
      (partnerQuotientSylow hG T hempty hM hu hmany hcard e H hH :
        Subgroup (Mc ⧸ pCore 2 Mc)) := by
  change (((T : Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).map _ =
    ((T : Subgroup G).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) z,hz,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    let z : H := ⟨y,hH.1.1.2 hy⟩
    exact ⟨QuotientGroup.mk' (pCore 2 H) z,⟨z,hy,rfl⟩,rfl⟩

/-- The exact E₈ Sylow in Mc/O₂(Mc) required by source 14.2.18. -/
private theorem partner_quotient_sylow :
    IsElementaryAbelian 2 (partnerQuotientSylow hG T hempty hM hu hmany hcard e H hH) ∧
      Nat.card (partnerQuotientSylow hG T hempty hM hu hmany hcard e H hH) = 8 := by
  let S := (T.subtype hH.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  let f := firstQuotientMap hG T hempty hM hu hmany hcard e H hH eR
  let d := ((S : Subgroup (H ⧸ pCore 2 H)).equivMapOfInjective f
    (firstQuotientMap_injective hG T hempty hM hu hmany hcard e H hH eR)).trans
      (MulEquiv.subgroupCongr
        (first_quotient_sylow_map hG T hempty hM hu hmany hcard e H hH eR))
  have hs := first_quotient_sylow hG T hempty hM hu hmany hcard e H hH eR S
  let := hs.1
  exact ⟨IsElementaryAbelian.of_surjective d.toMonoidHom d.surjective,
    (Nat.card_congr d.toEquiv).symm.trans hs.2⟩


/-- Original 14.2.18: the first endpoint is the containing C-component,
and is normal in Mc. This is relative normality in the centralizer. -/
theorem first_normal_component :
    (H.subgroupOf Mc).IsCComponent ∧ (H.subgroupOf Mc).Normal := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  let B := H.subgroupOf Mc
  have hB : B ∈ Chapter1.L Mc S :=
    (Chapter1.mem_LIn_iff_subgroupOf hTM hHM).mp
      (first_mem_local_family hG T hempty hM hu hmany hcard e H hH eR)
  obtain ⟨C,⟨hC,hBC,hCN⟩,_⟩ :=
    first_normal_containing_component hG T hempty hM hu hmany hcard e H hH eR
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let f := q.comp (inclusion hHM)
  have hfker : f.ker = pCore 2 H := by
    change (QuotientGroup.mk' (pCore 2 Mc)).ker.comap (inclusion hHM) = _
    rw [QuotientGroup.ker_mk']
    exact first_core_comap hG T hempty hM hu hmany hcard e H hH eR
  have hfrange : f.range = B.map q := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨inclusion hHM y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  let a : B.map q ≃* Theory.PSL2.BinaryGroup 3 :=
    (MulEquiv.subgroupCongr hfrange.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hfker).trans (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)))
  have huMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hQ := ChapterE.Structure.sqtk_two_quotient (hG.twoLocal_sqtk huMc.1.1)
    (pCore 2 Mc) pCore_isPGroup
  have hSm : Nat.card (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))) ≤ 8 :=
    (partner_quotient_sylow hG T hempty hM hu hmany hcard e H hH eR).2.le
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isNilpotent
  have himg : B.map q = C.map q :=
    containing_eq_of_eight_section hQ (pCore_quotient_pCore_eq_bot 2)
      (S.mapSurjective (QuotientGroup.mk'_surjective _)) hSm
      (Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hB)
      (hC.map_quotient _) (map_mono hBC) a
  have he : B = C := local_cComponent_eq_of_map_eq hB.1 hC hBC q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S) himg
  change B.IsCComponent ∧ B.Normal
  rw [he]
  exact ⟨hC,hCN⟩

/-- The original partner normalizes the original first subgroup. -/
theorem partner_le_first_normalizer :
    Mc ≤ normalizer (H : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)).mp
      (first_normal_component hG T hempty hM hu hmany hcard e H hH eR).2




/-- The source partner is the full ambient normalizer of the first component. -/
theorem first_normalizer_eq :
    normalizer (H : Set G) = Mc := by
  apply le_antisymm ?_ (partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR)
  exact (normalizer_le_normalizer_characteristic_image H (pCore 2 H)).trans
    (SourcePartnerCore.first_core_normalizer_eq hG T hempty hM hu hmany hcard e H hH eR).le

/-- Frattini's argument puts every possible extension of the first component
in the original overlap with M. The full odd Borel factor is retained. -/
theorem partner_factorization :
    Mc = H ⊔ (M ⊓ Mc) := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  let B := H.subgroupOf Mc
  let : B.Normal := (first_normal_component hG T hempty hM hu hmany hcard e H hH eR).2
  have hSB : (S : Subgroup Mc) ≤ B := comap_mono hH.1.1.2
  have ht := S.normalizer_sup_eq_top' hSB
  have hN : normalizer (S : Set Mc) ≤ (M ⊓ Mc).subgroupOf Mc := by
    intro x hx
    have hx' : (x : G) ∈ normalizer (T : Set G) := by
      change x ∈ normalizer ((T : Subgroup G).subgroupOf Mc : Set Mc) at hx
      rw [← subgroupOf_normalizer_eq hTM] at hx
      exact hx
    exact source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e hx'
  apply le_antisymm ?_ (sup_le hHM inf_le_right)
  have hh : (⊤ : Subgroup Mc) ≤ (H ⊔ (M ⊓ Mc)).subgroupOf Mc := by
    rw [←ht]
    exact sup_le (hN.trans (comap_mono le_sup_right)) (comap_mono le_sup_left)
  intro x hx
  exact hh (show (⟨x,hx⟩ : Mc) ∈ (⊤ : Subgroup Mc) from mem_top _)


end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceNormal
