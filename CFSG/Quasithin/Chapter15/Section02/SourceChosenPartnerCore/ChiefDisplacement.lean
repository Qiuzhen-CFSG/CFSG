module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore
public import Theory.Representation.BinaryConjugationSection.DisplacementBound
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.Representation.BinaryOffender.QuasisimpleImage
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.PlaneProjection

/-!
# Displacement and saturation on the actual partner chief action

Conjugation by V displaces Qc only into Vc = V intersect Qc. The source
index bound |Vc:Z| <= 4 therefore bounds displacement on every actual binary
section above Z and below Qc. Passing to the literal action image preserves
this bound, makes the action faithful, and retains irreducibility and the
specified nonidentity involution; its quadratic ratio is at most two.
The chief specialization uses the original normal endpoints and quotient.

If some actor has displacement at least two on that section, both index
bounds saturate. Thus |Z|=|V:Vc|=2, Vc lies in the upper endpoint, and its
intersection with the section kernel is exactly Z. The distinguished plane
lies in Vc by PlaneProjection, so it has a nonzero image in this SAME section.
The model-parabolic consumer then gives the noncore contradiction with no
assumed vector, fixedness, moving parabolic, or endpoint placement.

The source-specific existence and recognition of a rank-two chief action
remain with qt-e-152-critical-pair. The faithful image constructed here is
not asserted to be L/O2(L); that identification still needs proof. In
particular no version of B.4.5 is assumed or inferred merely from q <= 2.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136), before the B.4.5 recognition step.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The chosen module and the partner core mutually normalize one another. -/
theorem source_chosen_partner_core_commutator_le
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) :
    ⁅V,twoCoreIn Mc⁆ ≤ V ⊓ twoCoreIn Mc := by
  have hTMc : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hQT : twoCoreIn Mc ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc,pCoreIn,twoCoreIn] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hV : V ≤ Mc := (h.prepared.inside_core H hg.outside).trans
    ((twoCore_le H).trans hg.in_partner)
  have hN : Mc ≤ normalizer (twoCoreIn Mc : Set G) := by
    simpa only [twoCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 Mc).le_normalizer_map Mc.subtype
  refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp (hV.trans hN))
  rw [commutator_comm]
  exact le_normalizer_iff_commutator_le_right.mp
    (hQT.trans (h.maximal.1.2.trans h.prepared.normalized))

/-- The original commutator bound passes to any literal section above the seed. -/
theorem source_chosen_partner_section_displacement_le_two
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} (d : BinaryConjugationSection L U B ρ)
    (hU : U ≤ twoCoreIn Mc) (hB : centralInvolutions T ≤ B)
    (a : L) (ha : (a : G) ∈ V) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 := by
  apply d.displacement_rank_le_of_commutator_bound V (V ⊓ twoCoreIn Mc)
    (centralInvolutions T) hB
    ((commutator_mono le_rfl hU).trans (source_chosen_partner_core_commutator_le h hg))
    2 _ a ha
  exact (source_chosen_noncore_section_bound h hg hMc hZ hn).1

/-- Preserve the marked involution and displacement on the faithful irreducible image. -/
theorem source_chosen_partner_section_image_involution
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} (d : BinaryConjugationSection L U B ρ)
    (hU : U ≤ twoCoreIn Mc) (hB : centralInvolutions T ≤ B)
    (hi : IsIrreducible ρ) (a : L) (ha : (a : G) ∈ V) (hm : ρ a ≠ 1) :
    let σ := BinaryOffender.imageRepresentation ρ
    let t := BinaryOffender.actionHom ρ a
    Function.Injective σ ∧ IsIrreducible σ ∧ orderOf t = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 2 ∧
      BinaryOffender.quadraticRatio σ ≤ 2 := by
  let := h.prepared.elementary
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  let σ := BinaryOffender.imageRepresentation ρ
  let t := BinaryOffender.actionHom ρ a
  have ha2 : a^2=1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) (a : G) ha)
  have ht2 : t^2=1 := by change (BinaryOffender.actionHom ρ a)^2=1; rw [←map_pow,ha2,map_one]
  have ht1 : t ≠ 1 := by
    intro he
    apply hm
    simpa only [σ,t,BinaryOffender.imageRepresentation_actionHom,map_one] using congrArg σ he
  have ht : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hd : Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 2 :=
    source_chosen_partner_section_displacement_le_two h hg hMc hZ hn d hU hB a ha
  refine ⟨BinaryOffender.imageRepresentation_injective ρ,
    BinaryOffender.imageRepresentation_irreducible ρ hi,ht,hd,?_⟩
  obtain ⟨hA,hr,hq,_⟩ := BinaryOffender.involution_actor_rank_and_fixedCodim σ t ht
  apply (BinaryOffender.quadraticRatio_le_two_iff σ).mpr
  refine ⟨zpowers t,hA,hq,?_⟩
  rw [hr,Nat.mul_one,BinaryOffender.fixedCodim_zpowers_eq_displacement_rank]
  exact hd

/-- Specialization to the literal quotient of an ambient-normal chief interval. -/
theorem source_chosen_partner_chief_image_involution
    {T : Sylow 2 G} {M Mc V H ZS L : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    (A B : NoncentralChiefRefinement.NormalNode L) (hc : A ⋖ B)
    (hB : B.val.map L.subtype ≤ twoCoreIn Mc)
    (hA : centralInvolutions T ≤ A.val.map L.subtype)
    (a : L) (ha : (a : G) ∈ V) :
    let hp : IsPGroup 2 B.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
      (map_le_iff_le_comap.mp hB)
    letI := NoncentralChiefRefinement.chief_elementary A B hc hp
    let ρ : Representation (ZMod 2) L (Additive (NoncentralChiefRefinement.Section A B)) :=
      NoncentralChiefRefinement.binarySectionRepresentation A B
    let σ : Representation (ZMod 2) (BinaryOffender.actionImage ρ)
        (Additive (NoncentralChiefRefinement.Section A B)) := BinaryOffender.imageRepresentation ρ
    let t : BinaryOffender.actionImage ρ := BinaryOffender.actionHom ρ a
    ρ a ≠ 1 → Function.Injective σ ∧ Representation.IsIrreducible σ ∧ orderOf t = 2 ∧
      Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) ≤ 2 ∧
      BinaryOffender.quadraticRatio σ ≤ 2 := by
  let hp : IsPGroup 2 B.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hB)
  let := NoncentralChiefRefinement.chief_elementary A B hc hp
  dsimp only
  intro hm
  exact source_chosen_partner_section_image_involution h hg hMc hZ hn
    (NoncentralChiefRefinement.ambientBinarySection L A B hc.le) hB hA
    (NoncentralChiefRefinement.binarySection_irreducible A B hc) a ha hm

/-- Rank two on the actual section exhausts the numerical bound. In particular,
it proves that the source plane lies in this upper endpoint and survives. -/
theorem source_chosen_partner_rank_two_saturates
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) L W} (d : BinaryConjugationSection L U B ρ)
    (hU : U ≤ twoCoreIn Mc) (hB : centralInvolutions T ≤ B)
    (a : L) (ha : (a : G) ∈ V)
    (hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1))) :
    Nat.card (centralInvolutions T) = 2 ∧ (V ⊓ twoCoreIn Mc).relIndex V = 2 ∧
      V ⊓ twoCoreIn Mc ≤ U ∧ (V ⊓ twoCoreIn Mc) ⊓ B = centralInvolutions T ∧
      ZS ≤ U ∧ ¬ ZS ≤ B := by
  obtain ⟨hCU,hker,hi⟩ := d.endpoints_of_displacement_saturation V (V ⊓ twoCoreIn Mc)
    (centralInvolutions T) (source_chosen_seed_le_partner_core h hg hMc hZ) hB
    ((commutator_mono le_rfl hU).trans (source_chosen_partner_core_commutator_le h hg))
    2 (source_chosen_noncore_section_bound h hg hMc hZ hn).1 a ha hr
  obtain ⟨hcZ,hiV⟩ := (source_chosen_noncore_section_bound h hg hMc hZ hn).2 hi
  have hPC : ZS ≤ V ⊓ twoCoreIn Mc := le_inf hg.plane_le
    (source_chosen_plane_le_partner_core h hg hMc hZ)
  refine ⟨hcZ,hiV,hCU,hker,hPC.trans hCU,?_⟩
  intro hPB
  have hh := card_le_of_le ((le_inf hPC hPB).trans_eq hker)
  rw [hg.plane_card,hcZ] at hh
  omega

/-- A recognized model with rank-two displacement on a literal partner section
contradicts the source geometry; no vector or projection premise remains. -/
theorem source_chosen_false_of_partner_model_displacement
    {T : Sylow 2 G} {M Mc V H ZS U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∀ (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
      (_d : BinaryConjugationSection L U B (ρ.comp q)),
      U ≤ twoCoreIn Mc → centralInvolutions T ≤ B →
      (∃ a : L, (a : G) ∈ V ∧
        2 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1))) →
      Representation.SmallDisplacementParabolics.ActionModel ρ → False := by
  dsimp only
  intro ρ d hU hB ⟨a,ha,hr⟩ hmodel
  obtain ⟨_,_,_,_,hPU,hPB⟩ := source_chosen_partner_rank_two_saturates h hg hMc hZ hn
    d hU hB a ha hr
  exact source_chosen_false_of_partner_model_section h hg hMc hZ hplane ρ d hPU hB hPB hmodel

end CFSG.Quasithin.Chapter15.Section02
