module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceNormal
public import Theory.GroupTheory.PCoreNormalizerAction.SylowKernel
public import Theory.SpecificGroups.PSL2.EightAutomorphismOvergroups

/-!
# Exact original partner rank-one and field actions

The original partner normalizes full H, so conjugation acts on H/O₂(H).
The actual extraspecial module has trivial first-image centralizer, forcing
this rank-one action's kernel to be exactly O₂(Mc). Thus the partner quotient
is PSL₂(8) or its full automorphism group, and the coefficient-field kernel
is precisely the original H. No marked triality or action callback is used.

Source: Aschbacher--Smith 14.2.18, printed p.987.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRankOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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

/-- Conjugation by the original partner, in the literal full-H quotient coordinates. -/
def rankOneAction : Mc →* MulAut (Theory.PSL2.BinaryGroup 3) :=
  (MulAut.congr ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR))).toMonoidHom.comp
    ((pCoreNormalizerAction 2 H).comp (inclusion
      (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR)))

/-- The genuine coefficient-field projection of the original partner action. -/
def fieldAction :
    Mc →* (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
  (Theory.PSL2.fieldProjection (Theory.PSL2.BinaryField 3)).comp
    (rankOneAction hG T hempty hM hu hmany hcard e H hH eR)

include hG hempty hM hu hmany hcard e hH eR

/-- Restriction to the original H is exactly the inner action. -/
theorem rankOneAction_on_first (j : H) :
    rankOneAction hG T hempty hM hu hmany hcard e H hH eR
      (inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) j) =
      MulAut.conj ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR) (QuotientGroup.mk' (pCore 2 H) j)) := by
  change MulAut.congr ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR))
    (pCoreNormalizerAction 2 H ⟨j,H.le_normalizer j.property⟩) = _
  rw [pCoreNormalizerAction_on_component,MulAut.congr_conj]

/-- The action follows the original conjugation square on every quotient representative. -/
theorem rankOneAction_mk (x : Mc) (j : H) :
    rankOneAction hG T hempty hM hu hmany hcard e H hH eR x
      ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR) (QuotientGroup.mk' (pCore 2 H) j)) =
    (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR) (QuotientGroup.mk' (pCore 2 H)
      (H.normalizerMonoidHom (inclusion
        (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR) x) j)) := by
  change (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR) (pCoreNormalizerAction 2 H _
    (((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)).symm ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR) _))) = _
  rw [MulEquiv.symm_apply_apply,pCoreNormalizerAction_mk]

/-- The whole inner automorphism group is the image of the original first endpoint. -/
theorem first_image :
    (H.subgroupOf Mc).map (rankOneAction hG T hempty hM hu hmany hcard e H hH eR) =
      Theory.PSL2.inner (Theory.PSL2.BinaryField 3) := by
  apply le_antisymm
  · rintro a ⟨x,hx,rfl⟩
    let j : H := ⟨x,hx⟩
    have he : inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) j = x :=
      Subtype.ext rfl
    rw [←he,rankOneAction_on_first]
    exact ⟨_,rfl⟩
  · rintro a ⟨x,rfl⟩
    obtain ⟨q,rfl⟩ := ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)).surjective x
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) q
    exact ⟨inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) j,
      j.property,rankOneAction_on_first hG T hempty hM hu hmany hcard e H hH eR j⟩

private theorem kernel_map :
    (rankOneAction hG T hempty hM hu hmany hcard e H hH eR).ker.map Mc.subtype =
      pCoreActionKernelIn 2 H Mc := by
  rw [pCoreActionKernelIn_eq_map_ker _ _ _
    (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR)]
  congr 1
  ext x
  change MulAut.congr ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)) _ = 1 ↔ _ = 1
  rw [← map_one (MulAut.congr ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR))),
    (MulAut.congr ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR))).injective.eq_iff]

private theorem kernel_inf_first :
    pCoreActionKernelIn 2 H Mc ⊓ H = H.pCoreIn 2 := by
  apply pCoreActionKernelIn_inf_eq_core H Mc
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)
  apply map_injective (f := ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)).toMonoidHom) ((sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR)).injective
  rw [center_map_equiv,Subgroup.map_bot,Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]

private theorem field_kernel_sup :
    (fieldAction hG T hempty hM hu hmany hcard e H hH eR).ker = H.subgroupOf Mc ⊔
      (rankOneAction hG T hempty hM hu hmany hcard e H hH eR).ker := by
  change (Theory.PSL2.fieldProjection (Theory.PSL2.BinaryField 3)).ker.comap _ = _
  rw [Theory.PSL2.fieldProjection_ker,
    ← first_image hG T hempty hM hu hmany hcard e H hH eR,comap_map_eq]

private theorem field_range :
    (fieldAction hG T hempty hM hu hmany hcard e H hH eR).range = ⊥ ∨
      (fieldAction hG T hempty hM hu hmany hcard e H hH eR).range = ⊤ := by
  let : Fact (Nat.card (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3)).Prime :=
    ⟨by rw [GaloisField.card_ringAut 2 3 (by decide)]; decide⟩
  exact (fieldAction hG T hempty hM hu hmany hcard e H hH eR).range.eq_bot_or_eq_top_of_prime_card

private theorem action_quotient :
    Nonempty ((Mc ⧸ (rankOneAction hG T hempty hM hu hmany hcard e H hH eR).ker) ≃*
      Theory.PSL2.BinaryGroup 3) ∨
    Nonempty ((Mc ⧸ (rankOneAction hG T hempty hM hu hmany hcard e H hH eR).ker) ≃*
      MulAut (Theory.PSL2.BinaryGroup 3)) := by
  apply Theory.PSL2.eight_action_quotient (rankOneAction hG T hempty hM hu hmany hcard e H hH eR)
  rw [←first_image hG T hempty hM hu hmany hcard e H hH eR]
  rintro x ⟨y,_,rfl⟩
  exact ⟨y,rfl⟩

/-- The actual rank-one action has no kernel beyond the original partner two-core. -/
theorem action_kernel :
    (rankOneAction hG T hempty hM hu hmany hcard e H hH eR).ker = pCore 2 Mc := by
  let a := rankOneAction hG T hempty hM hu hmany hcard e H hH eR
  let ρ := partnerCoreAction Mc
  let B := H.subgroupOf Mc
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hi : a.ker ⊓ B = pCore 2 Mc := by
    apply map_injective Mc.subtype_injective
    rw [map_inf _ _ _ Mc.subtype_injective,map_subgroupOf_eq_of_le hHM]
    change (rankOneAction hG T hempty hM hu hmany hcard e H hH eR).ker.map Mc.subtype ⊓ H =
      Mc.pCoreIn 2
    rw [kernel_map hG T hempty hM hu hmany hcard e H hH eR,
      kernel_inf_first hG T hempty hM hu hmany hcard e H hH eR,
      SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR]
  have hcomm : ⁅B,a.ker⁆ ≤ ρ.ker := by
    rw [SourceCoreAction.partner_action_kernel hG T hempty hM hu hmany hcard e H hH eR]
    have hm : (⁅B,a.ker⁆).map Mc.subtype ≤ (pCore 2 Mc).map Mc.subtype := by
      rw [map_commutator,map_subgroupOf_eq_of_le hHM,
        kernel_map hG T hempty hM hu hmany hcard e H hH eR]
      change ⁅H,pCoreActionKernelIn 2 H Mc⁆ ≤ Mc.pCoreIn 2
      rw [SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR]
      exact pCoreActionKernelIn_commutator 2 H Mc
    intro x hx
    obtain ⟨y,hy,he⟩ := hm (mem_map_of_mem Mc.subtype hx)
    exact Mc.subtype_injective he ▸ hy
  have hzero : ⁅B.map ρ,a.ker.map ρ⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff]
    exact hcomm
  have hBimage : B.map ρ = (firstCoreAction hG hempty hM hu hmany hcard e hH).range := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    · rintro ⟨y,rfl⟩
      exact ⟨inclusion hHM y,y.property,rfl⟩
  have hker : a.ker.map ρ ≤ centralizer ((firstCoreAction hG hempty hM hu hmany hcard e hH).range :
      Set (MulAut (PartnerCoreModule Mc))) := by
    rw [←hBimage]
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  rw [SourceCoreAction.first_action_centralizer_eq_bot hG T hempty hM hu hmany hcard e H hH eR] at hker
  have hle : a.ker ≤ ρ.ker := by
    have hb : a.ker.map ρ = ⊥ := bot_unique hker
    rwa [Subgroup.map_eq_bot_iff] at hb
  rw [SourceCoreAction.partner_action_kernel hG T hempty hM hu hmany hcard e H hH eR] at hle
  exact le_antisymm hle (hi ▸ inf_le_left)

/-- The original partner modulo its own two-core has the exact rank-one alternatives. -/
theorem partner_quotient :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* Theory.PSL2.BinaryGroup 3) ∨
      Nonempty ((Mc ⧸ pCore 2 Mc) ≃* MulAut (Theory.PSL2.BinaryGroup 3)) := by
  have h := action_quotient hG T hempty hM hu hmany hcard e H hH eR
  let f := QuotientGroup.quotientMulEquivOfEq
    (action_kernel
      hG T hempty hM hu hmany hcard e H hH eR).symm
  rcases h with h | h
  · obtain ⟨b⟩ := h
    exact Or.inl ⟨f.trans b⟩
  · obtain ⟨b⟩ := h
    exact Or.inr ⟨f.trans b⟩

/-- The field action has precisely the full original first endpoint as kernel. -/
theorem field_kernel :
    (fieldAction hG T hempty hM hu hmany hcard e H hH eR).ker = H.subgroupOf Mc := by
  rw [field_kernel_sup,action_kernel]
  apply sup_eq_left.mpr
  intro q hq
  apply pCoreIn_le 2 H
  rw [←SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR]
  exact ⟨q,hq,rfl⟩

/-- Every proper partner realizes the full cubic coefficient group. -/
theorem field_range_eq_top (hne : Mc ≠ H) :
    (fieldAction hG T hempty hM hu hmany hcard e H hH eR).range = ⊤ := by
  rcases field_range hG T hempty hM hu hmany hcard e H hH eR with hz | ht
  · exfalso
    apply hne
    apply le_antisymm ?_ (source_first_le_partner hG hempty hM hu hmany hcard e hH)
    intro x hx
    have hk : (⟨x,hx⟩ : Mc) ∈ (fieldAction hG T hempty hM hu hmany hcard e H hH eR).ker := by
      have hh : fieldAction hG T hempty hM hu hmany hcard e H hH eR ⟨x,hx⟩ ∈
          (fieldAction hG T hempty hM hu hmany hcard e H hH eR).range := ⟨_,rfl⟩
      rw [hz, mem_bot] at hh
      exact hh
    rw [field_kernel] at hk
    exact hk
  · exact ht

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRankOne
