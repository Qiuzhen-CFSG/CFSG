module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Component
public import Theory.GroupTheory.PCoreNormalizerAction.SylowKernel
public import Theory.SpecificGroups.PSL2.EightAutomorphismOvergroups

/-!
# The original triality partner's rank-one and field actions

Conjugate the literal action of Mc on H/O₂(H) through the quotient
isomorphism supplied by the marked triality amalgam. The image contains
all inner automorphisms, hence is PSL₂(8) or its full automorphism group.
The kernel D meets H in exactly O₂(H), normalizes the original Sylow T,
and therefore lies in the original M intersect Mc. The field projection
has kernel H D, with the full odd Borel factor retained.

These statements identify Mc/D, not Mc/O₂(Mc): eliminating the possible
odd group D/O₂(Mc) still requires the source's linear-centralizer argument.
The trivial-centralizer identity for the actual first action on the core
quotient implies equality of these kernels; this identity remains unproved.
No equality of these two kernels is assumed. The original 14.2.18--19
assembly and this remaining proof stay with qt-e-14315-eight-borel-exclusion.
Source: Aschbacher--Smith 14.2.18, printed p.987. The literal terminal
application is `TerminalSolvable/EightBorelFieldAction.lean`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)

/-- The actual quotient action, with the marked PSL₂(8) coordinates. -/
def sourceRankOneAction (r : MarkedTriality T M Mc H) : Mc →* MulAut (Theory.PSL2.BinaryGroup 3) :=
  (MulAut.congr (firstQuotientEquiv r)).toMonoidHom.comp
    ((pCoreNormalizerAction 2 H).comp (inclusion
      (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r)))

/-- The coefficient-field part of that same actual action. -/
def sourceFieldAction (r : MarkedTriality T M Mc H) :
    Mc →* (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
  (Theory.PSL2.fieldProjection (Theory.PSL2.BinaryField 3)).comp
    (sourceRankOneAction hG hempty hM hu hmany hcard e hH r)

include hG hempty hM hu hmany hcard e hH

/-- Compatibility with the original inclusion and quotient map. -/
theorem source_rankOneAction_on_first (r : MarkedTriality T M Mc H) (j : H) :
    sourceRankOneAction hG hempty hM hu hmany hcard e hH r
      (inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) j) =
      MulAut.conj (firstQuotientEquiv r (QuotientGroup.mk' (pCore 2 H) j)) := by
  change MulAut.congr (firstQuotientEquiv r)
    (pCoreNormalizerAction 2 H ⟨j,H.le_normalizer j.property⟩) = _
  rw [pCoreNormalizerAction_on_component,MulAut.congr_conj]

/-- Every actor follows the original conjugation square on quotient representatives. -/
theorem source_rankOneAction_mk (r : MarkedTriality T M Mc H) (x : Mc) (j : H) :
    sourceRankOneAction hG hempty hM hu hmany hcard e hH r x
      (firstQuotientEquiv r (QuotientGroup.mk' (pCore 2 H) j)) =
    firstQuotientEquiv r (QuotientGroup.mk' (pCore 2 H)
      (H.normalizerMonoidHom (inclusion
        (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r) x) j)) := by
  change firstQuotientEquiv r (pCoreNormalizerAction 2 H _
    ((firstQuotientEquiv r).symm (firstQuotientEquiv r _))) = _
  rw [MulEquiv.symm_apply_apply,pCoreNormalizerAction_mk]

/-- The first subgroup maps onto the entire inner automorphism group. -/
theorem source_rankOneAction_first_image (r : MarkedTriality T M Mc H) :
    (H.subgroupOf Mc).map (sourceRankOneAction hG hempty hM hu hmany hcard e hH r) =
      Theory.PSL2.inner (Theory.PSL2.BinaryField 3) := by
  apply le_antisymm
  · rintro a ⟨x,hx,rfl⟩
    let j : H := ⟨x,hx⟩
    have he : inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) j = x :=
      Subtype.ext rfl
    rw [←he,source_rankOneAction_on_first]
    exact ⟨_,rfl⟩
  · rintro a ⟨x,rfl⟩
    obtain ⟨q,rfl⟩ := (firstQuotientEquiv r).surjective x
    obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) q
    exact ⟨inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) j,
      j.property,source_rankOneAction_on_first hG hempty hM hu hmany hcard e hH r j⟩

/-- The ambient kernel is exactly the published quotient-action kernel,
with no replacement of quotient centralization by ordinary centralization. -/
theorem source_rankOneAction_kernel_map (r : MarkedTriality T M Mc H) :
    (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker.map Mc.subtype =
      pCoreActionKernelIn 2 H Mc := by
  rw [pCoreActionKernelIn_eq_map_ker _ _ _
    (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r)]
  congr 1
  ext x
  change MulAut.congr (firstQuotientEquiv r) _ = 1 ↔ _ = 1
  rw [← map_one (MulAut.congr (firstQuotientEquiv r)),
    (MulAut.congr (firstQuotientEquiv r)).injective.eq_iff]

/-- Kernel placement in the original ambient normalizer and overlap. -/
theorem source_rankOneAction_kernel_placement :
    pCoreActionKernelIn 2 H Mc ≤ normalizer (T : Set G) ∧
      pCoreActionKernelIn 2 H Mc ≤ M ⊓ Mc := by
  have hn := pCoreActionKernelIn_le_sylow_normalizer H Mc T hH.1.1.2
  exact ⟨hn,hn.trans (source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e)⟩

/-- Only the actual core lies in both the kernel and the first subgroup. -/
theorem source_rankOneAction_kernel_inf_first (r : MarkedTriality T M Mc H) :
    pCoreActionKernelIn 2 H Mc ⊓ H = H.pCoreIn 2 := by
  apply pCoreActionKernelIn_inf_eq_core H Mc
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)
  apply map_injective (f := (firstQuotientEquiv r).toMonoidHom) (firstQuotientEquiv r).injective
  rw [center_map_equiv,Subgroup.map_bot,Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot]

/-- The field-action kernel is H times the actual rank-one action kernel. -/
theorem source_fieldAction_kernel (r : MarkedTriality T M Mc H) :
    (sourceFieldAction hG hempty hM hu hmany hcard e hH r).ker = H.subgroupOf Mc ⊔
      (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker := by
  change (Theory.PSL2.fieldProjection (Theory.PSL2.BinaryField 3)).ker.comap _ = _
  rw [Theory.PSL2.fieldProjection_ker,
    ← source_rankOneAction_first_image hG hempty hM hu hmany hcard e hH r,comap_map_eq]

/-- The field image is trivial or the genuine full cubic coefficient group. -/
theorem source_fieldAction_range (r : MarkedTriality T M Mc H) :
    (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range = ⊥ ∨
      (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range = ⊤ := by
  let : Fact (Nat.card (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3)).Prime :=
    ⟨by rw [GaloisField.card_ringAut 2 3 (by decide)]; decide⟩
  exact (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range.eq_bot_or_eq_top_of_prime_card

/-- These are actual quotient isomorphisms, before the remaining kernel
comparison needed by source 14.2.18. -/
theorem source_rankOneAction_quotient (r : MarkedTriality T M Mc H) :
    Nonempty ((Mc ⧸ (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker) ≃*
      Theory.PSL2.BinaryGroup 3) ∨
    Nonempty ((Mc ⧸ (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker) ≃*
      MulAut (Theory.PSL2.BinaryGroup 3)) := by
  apply Theory.PSL2.eight_action_quotient (sourceRankOneAction hG hempty hM hu hmany hcard e hH r)
  rw [←source_rankOneAction_first_image hG hempty hM hu hmany hcard e hH r]
  rintro x ⟨y,_,rfl⟩
  exact ⟨y,rfl⟩

/-- The ambient field kernel retains the full original first endpoint. -/
theorem source_fieldAction_kernel_map (r : MarkedTriality T M Mc H) :
    (sourceFieldAction hG hempty hM hu hmany hcard e hH r).ker.map Mc.subtype =
      H ⊔ pCoreActionKernelIn 2 H Mc := by
  rw [source_fieldAction_kernel,Subgroup.map_sup,
    map_subgroupOf_eq_of_le (source_first_le_partner hG hempty hM hu hmany hcard e hH),
    source_rankOneAction_kernel_map]

/-- A nontrivial field image gives a genuine cubic field automorphism on
H/O₂(H). Its preimage's order is not asserted before the kernel comparison. -/
theorem source_rankOneAction_field_witness (r : MarkedTriality T M Mc H)
    (hn : (sourceFieldAction hG hempty hM hu hmany hcard e hH r).range ≠ ⊥) :
    ∃ (σ : Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) (x : Mc),
      orderOf σ = 3 ∧
      sourceRankOneAction hG hempty hM hu hmany hcard e hH r x = Theory.PSL2.fieldAut σ ∧
      orderOf (sourceRankOneAction hG hempty hM hu hmany hcard e hH r x) = 3 := by
  have hc : Nat.card (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) = 3 :=
    GaloisField.card_ringAut 2 3 (by decide)
  let : IsCyclic (Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3) :=
    isCyclic_of_prime_card hc
  obtain ⟨σ,hσ⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := Theory.PSL2.BinaryField 3 ≃+* Theory.PSL2.BinaryField 3)
  rw [hc] at hσ
  have hi : Theory.PSL2.inner (Theory.PSL2.BinaryField 3) ≤
      (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).range := by
    rw [←source_rankOneAction_first_image hG hempty hM hu hmany hcard e hH r]
    exact Subgroup.map_le_range _ _
  obtain ⟨x,hx⟩ := Theory.PSL2.eight_action_field_lift _ hi hn σ
  exact ⟨σ,x,hσ,hx,by rw [hx,Theory.PSL2.orderOf_fieldAut,hσ]⟩


/-- The possible extra kernel is odd modulo the actual partner core. In
particular this does not silently assume the missing kernel equality. -/
theorem source_rankOneAction_kernel_core_and_odd (r : MarkedTriality T M Mc H) :
    let D := (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker
    pCore 2 D = (pCore 2 Mc).subgroupOf D ∧
      Odd (Nat.card (D ⧸ (pCore 2 Mc).subgroupOf D)) := by
  let a := sourceRankOneAction hG hempty hM hu hmany hcard e hH r
  let D := a.ker
  let Q := pCore 2 Mc
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  let S := T.subtype (hH.1.1.2.trans hHM)
  have hi : D ⊓ H.subgroupOf Mc = Q := by
    apply map_injective Mc.subtype_injective
    rw [map_inf _ _ _ Mc.subtype_injective,map_subgroupOf_eq_of_le hHM]
    change (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker.map Mc.subtype ⊓ H =
      Mc.pCoreIn 2
    rw [source_rankOneAction_kernel_map hG hempty hM hu hmany hcard e hH r,
      source_rankOneAction_kernel_inf_first hG hempty hM hu hmany hcard e hH r,
      source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
  have hQD : Q ≤ D := hi ▸ inf_le_left
  have hQS : Q ≤ (S : Subgroup Mc) := pCore_isPGroup.le_sylow_of_normal S
  have hDS : D ⊓ (S : Subgroup Mc) = Q := by
    apply le_antisymm ?_ (le_inf hQD hQS)
    rw [←hi]
    exact inf_le_inf_left D (comap_mono hH.1.1.2)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal D
  have hPQ : (P : Subgroup D) = Q.subgroupOf D := by
    rw [hP]
    ext x
    change (x : Mc) ∈ S ↔ (x : Mc) ∈ Q
    constructor
    · intro hx
      exact hDS ▸ (show (x : Mc) ∈ D ⊓ (S : Subgroup Mc) from ⟨x.property,hx⟩)
    · exact fun hx => hQS hx
  constructor
  · apply le_antisymm
    · rw [←hPQ]
      exact pCore_isPGroup.le_sylow_of_normal P
    · exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective D.subtype D.subtype_injective⟩
  · rw [←index_eq_card,←hPQ,←Nat.not_even_iff_odd,even_iff_two_dvd]
    exact P.not_dvd_index


/-- The exact linear-centralizer premise remaining in source 14.2.18 suffices
to eliminate the odd kernel. It concerns the already constructed actual
PSL₂(8) image on the actual elementary core quotient of order 256. -/
theorem source_rankOneAction_kernel_eq_of_core_centralizer
    (r : MarkedTriality T M Mc H)
    (hc : centralizer ((firstCoreAction hG hempty hM hu hmany hcard e hH).range :
      Set (MulAut (PartnerCoreModule Mc))) = ⊥) :
    (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker = pCore 2 Mc := by
  let a := sourceRankOneAction hG hempty hM hu hmany hcard e hH r
  let ρ := partnerCoreAction Mc
  let B := H.subgroupOf Mc
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hi : a.ker ⊓ B = pCore 2 Mc := by
    apply map_injective Mc.subtype_injective
    rw [map_inf _ _ _ Mc.subtype_injective,map_subgroupOf_eq_of_le hHM]
    change (sourceRankOneAction hG hempty hM hu hmany hcard e hH r).ker.map Mc.subtype ⊓ H =
      Mc.pCoreIn 2
    rw [source_rankOneAction_kernel_map hG hempty hM hu hmany hcard e hH r,
      source_rankOneAction_kernel_inf_first hG hempty hM hu hmany hcard e hH r,
      source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
  have hcomm : ⁅B,a.ker⁆ ≤ ρ.ker := by
    rw [source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r]
    have hm : (⁅B,a.ker⁆).map Mc.subtype ≤ (pCore 2 Mc).map Mc.subtype := by
      rw [map_commutator,map_subgroupOf_eq_of_le hHM,
        source_rankOneAction_kernel_map hG hempty hM hu hmany hcard e hH r]
      change ⁅H,pCoreActionKernelIn 2 H Mc⁆ ≤ Mc.pCoreIn 2
      rw [source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
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
  rw [hc] at hker
  have hle : a.ker ≤ ρ.ker := by
    have hb : a.ker.map ρ = ⊥ := bot_unique hker
    rwa [Subgroup.map_eq_bot_iff] at hb
  rw [source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r] at hle
  exact le_antisymm hle (hi ▸ inf_le_left)

/-- The same linear-centralizer premise gives the exact original quotient
alternatives, rather than quotienting by a larger unspecified odd kernel. -/
theorem source_partner_quotient_of_core_centralizer
    (r : MarkedTriality T M Mc H)
    (hc : centralizer ((firstCoreAction hG hempty hM hu hmany hcard e hH).range :
      Set (MulAut (PartnerCoreModule Mc))) = ⊥) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* Theory.PSL2.BinaryGroup 3) ∨
      Nonempty ((Mc ⧸ pCore 2 Mc) ≃* MulAut (Theory.PSL2.BinaryGroup 3)) := by
  have h := source_rankOneAction_quotient hG hempty hM hu hmany hcard e hH r
  let f := QuotientGroup.quotientMulEquivOfEq
    (source_rankOneAction_kernel_eq_of_core_centralizer
      hG hempty hM hu hmany hcard e hH r hc).symm
  rcases h with h | h
  · obtain ⟨b⟩ := h
    exact Or.inl ⟨f.trans b⟩
  · obtain ⟨b⟩ := h
    exact Or.inr ⟨f.trans b⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
