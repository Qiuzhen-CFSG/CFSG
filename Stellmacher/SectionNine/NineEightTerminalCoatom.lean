module
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineNextQuotientFixedGeneration
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionThree.PSetQuadraticFixedHyperplane
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import Theory.GroupAction.ActorSubtypeCommutator

/-!
# The fixed terminal coatom from (1.2) in Stellmacher (9.8)

If the first-step center is not contained in the terminal module, an
actual first-step module element outside the terminal core centralizes
an index-two subgroup of the terminal module.

Use the literal first-step quotient V/Z and its proved fixed-generation
property for a Sylow containing the terminal module. Mutual normalization
of the first and terminal modules, together with terminal abelianness,
makes that terminal actor subgroup quadratic. The hereditary form of (1.2)
gives an actor subgroup of index at most two and a fixed quotient vector
whose lift escapes the terminal core. Its lifted commutator lies both
in the terminal module and in the first-step center line; the assumed
noncontainment makes their intersection trivial. Index one would make
the chosen element centralize the full terminal module, contradicting
the faithful quotient kernel. Hence the index is exactly two.

Source: Stellmacher (9.8), printed p.55/PDF p.45, the application of (1.2)
in the case Zfirst is not contained in Vterminal.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem nine_eight_terminal_coatom_fixed_actor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ (fixed : Subgroup G) (actor : G), fixed ≤ VAt ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (VAt ctx.Γ ctx.criticalPath.a') fixed 2 ∧
      actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      fixed ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Y := VAt Γ cp.a'
  let Q := QAt Γ cp.a'
  have hYP : Y ≤ P := (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hVPterminal : V ≤ GAt Γ cp.a' := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hZaV : ZAt Γ cp.a ≤ V := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hVnotQ : ¬ V ≤ Q := fun hle => cp.critical.2 (hZaV.trans hle)
  have hbLocal : 1 < cp.length := hb
  have htail : Γ.distance cp.firstStep cp.a' < cp.length := by
    have hh := path_distance_le Γ cp 1 cp.length (by omega) le_rfl
    rw [cp.path_first,cp.path_end] at hh
    omega
  have hZQ : Z ≤ Q := critical_minimality Γ cp htail
  let _ : IsElementaryAbelian 2 Y :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hYPgroup : IsPGroup 2 (Y.subgroupOf P) :=
    (IsElementaryAbelian.isPGroup 2 Y).of_equiv (Subgroup.subgroupOfEquivOfLe hYP).symm
  obtain ⟨sylow,hYsylow⟩ := hYPgroup.exists_le_sylow
  obtain ⟨hN,hW,action,haction,hkernel⟩ :=
    nine_next_quotient_conjugation_action ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let q : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let R : Subgroup W := (Q.subgroupOf V).map q
  have hR : R ≠ ⊤ := by
    intro htop
    apply hVnotQ
    intro vector hvector
    have hmem : q ⟨vector,hvector⟩ ∈ R := htop ▸ Subgroup.mem_top _
    obtain ⟨point,hpoint,heq⟩ := hmem
    have hd := QuotientGroup.eq_iff_div_mem.mp heq
    have hv := Q.mul_mem (Q.inv_mem (hZQ hd)) hpoint
    change ((point : G) / vector)⁻¹ * (point : G) ∈ Q at hv
    simpa [div_eq_mul_inv,mul_assoc] using hv
  have hquadAmbient : ⁅⁅V,Y⁆,Y⁆ ≤ Z := by
    have hcommY : ⁅V,Y⁆ ≤ Y := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hVPterminal.trans (stabilizer_le_normalizer_v Γ cp.a'))
    exact (Subgroup.commutator_mono hcommY le_rfl).trans
      ((Subgroup.commutator_self_eq_bot_iff.mpr inferInstance).le.trans bot_le)
  have hquad : IsQuadraticAction ((Y.subgroupOf P).map action.rangeRestrict) W := by
    have hh := Subgroup.quotient_conjugation_quadratic_of_double_commutator_le
      P V Z Y (stabilizer_le_normalizer_v Γ cp.firstStep) hYP hN hquadAmbient action haction
    change commutatorAction₂ ((Y.subgroupOf P).map action.rangeRestrict) W = ⊥
    rw [← commutatorAction₂_map_actor_subtype action.range ((Y.subgroupOf P).map action.rangeRestrict),
      Subgroup.map_map]
    exact hh
  have hgen := nine_next_quotient_sylow_fixed_generation ctx hb hN action haction sylow
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).2
  obtain ⟨fixedNative,hfixedNative,hcardNative,hescape⟩ :=
    SectionThree.pSet_quadratic_fixed_hyperplane_lift T P (sectionThreeHypotheses ctx.sectionSeven)
      ((pFamily_iff_pSet _ _ _).mp hlocal.1) hlocal.2 action hkernel.symm.le sylow
      hgen (Y.subgroupOf P) hYsylow hquad R hR
  obtain ⟨point,hpoint,hpointNot⟩ := SetLike.not_le_iff_exists.mp hescape
  obtain ⟨vector,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf V) point
  have hvectorNot : (vector : G) ∉ Q := fun hv => hpointNot (Subgroup.mem_map_of_mem q hv)
  let fixed := fixedNative.map P.subtype
  have hfixed : fixed ≤ Y :=
    (Subgroup.map_mono hfixedNative).trans_eq (Subgroup.map_subgroupOf_eq_of_le hYP)
  have hbound : Nat.card Y ≤ 2 * Nat.card fixed := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYP).toEquiv] at hcardNative
    change Nat.card Y ≤ 2 * Nat.card (fixedNative.map P.subtype)
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hcardNative
  have hZcard := (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).1
  have hZY : Z ⊓ Y = ⊥ := by
    by_contra hnonzero
    have hpositive := (Subgroup.one_lt_card_iff_ne_bot _).mpr hnonzero
    have heq : Z ⊓ Y = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by
      change Nat.card Z = 2 at hZcard
      omega)
    exact hnot (heq.ge.trans inf_le_right)
  have hfixedVector (element : G) (helement : element ∈ fixed) : ⁅element,(vector : G)⁆ = 1 := by
    have hmemZ : ⁅element,(vector : G)⁆ ∈ Z := by
      obtain ⟨native,hnative,rfl⟩ := helement
      have hh := hpoint ⟨action.rangeRestrict native,
        Subgroup.mem_map_of_mem action.rangeRestrict hnative⟩
      change action native (q vector) = q vector at hh
      rw [haction] at hh
      have hd := QuotientGroup.eq_iff_div_mem.mp hh
      change (native : G) * (vector : G) * (native : G)⁻¹ / (vector : G) ∈ Z at hd
      change ⁅(native : G),(vector : G)⁆ ∈ Z
      simpa only [commutatorElement_def,div_eq_mul_inv] using hd
    have hmemY : ⁅element,(vector : G)⁆ ∈ Y := by
      have hc := (Subgroup.mem_normalizer_iff.mp
        (stabilizer_le_normalizer_v Γ cp.a' (hVPterminal vector.property)) element⁻¹).mp
        (Y.inv_mem (hfixed helement))
      simpa only [commutatorElement_def,mul_assoc] using Y.mul_mem (hfixed helement) hc
    exact hZY.le (show ⁅element,(vector : G)⁆ ∈ Z ⊓ Y from ⟨hmemZ,hmemY⟩)
  have hcentral : fixed ≤ Subgroup.centralizer (Subgroup.zpowers (vector : G) : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_centralizer_iff]
    intro element helement
    exact commutatorElement_eq_one_iff_mul_comm.mp (hfixedVector element helement)
  have hproper : ¬ Y ≤ fixed := by
    intro hle
    obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    have hkernelY := (nine_next_center_commutator_and_kernel ctx hb cp.a'
      ⟨alignment,halignment⟩).2.2 vector (hVPterminal vector.property)
    apply hvectorNot
    apply hkernelY.mp
    have hzero : ⁅Y,Subgroup.zpowers (vector : G)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hcentral)
    exact hzero.le.trans bot_le
  have hmul := (fixed.subgroupOf Y).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfixed).toEquiv] at hmul
  change fixed.relIndex Y * Nat.card fixed = Nat.card Y at hmul
  have hpositive : 0 < Nat.card fixed := Nat.card_pos
  have hYpositive : 0 < Nat.card Y := Nat.card_pos
  have hnotOne : fixed.relIndex Y ≠ 1 := fun heq => hproper (Subgroup.relIndex_eq_one.mp heq)
  have hnotZero : fixed.relIndex Y ≠ 0 := by intro heq; rw [heq,zero_mul] at hmul; omega
  have hindexTwo : fixed.relIndex Y = 2 := by
    have hupper : fixed.relIndex Y ≤ 2 := by nlinarith
    omega
  refine ⟨fixed,vector,hfixed,?_,vector.property,hvectorNot,hcentral⟩
  change Nat.card Y = 2 * Nat.card fixed
  simpa only [hindexTwo] using hmul.symm

end Stellmacher.SectionNine
