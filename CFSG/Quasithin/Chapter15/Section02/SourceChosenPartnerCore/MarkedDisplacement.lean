module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefFaithfulness.Marked
public import Theory.Representation.SmallDisplacementParabolics.MarkedDisplacement

/-!
# Central displacement on the marked partner chief quotient

The original V-image is a nontrivial elementary subgroup normalized by
the original image Sylow. Its central involution lifts through the literal
map L → L/O₂(L), and the section commutator bound gives displacement
between one and two. The constructed-chief specialization has no model
hypothesis and retains the same endpoints, faithful action, and marking.

If this chief action is recognized as one of the concrete partner models,
the central-involution calculation forces rank two. Saturation and the
existing moving-parabolic argument then give the noncore contradiction,
without a separate displacement or projected-vector premise.

Recognition and the pre-recognition common-center exclusion remain with
qt-e-152-critical-pair; this module does not assert 15.2.27(2). The source
wrappers retain the exact preceding 15.2.8--14 quotient, residual, seed,
and structural conclusions, whose external producers are the residual
and plane geometry branches. Final source assembly remains with the
critical-pair owner and its chosen-action-contradiction parent.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119
(refs/quasithin.pdf p.1136).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Extract a central involution of the actual marked quotient, with the section bound. -/
theorem source_chosen_partner_marked_central_displacement
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (d : BinaryConjugationSection L U B (ρ.comp (QuotientGroup.mk' (pCore 2 L))))
    (hU : U ≤ twoCoreIn Mc) (hB : centralInvolutions T ≤ B)
    (hp : PartnerChiefQuotientProperties T V L ρ) :
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
      (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) ∧
      1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1)) ≤ 2 := by
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  let q := QuotientGroup.mk' (pCore 2 L)
  let A := (V.subgroupOf L).map q
  obtain ⟨hf,_,hA,hne,_,S,hS,hAS,hnS,_⟩ := hp
  have hd : ∀ a ∈ A, Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 := by
    rintro a ⟨b,hb,rfl⟩
    exact source_chosen_partner_section_displacement_le_two h hg hMc hZ hn d hU hB b hb
  obtain ⟨a,ha,ho,hc,hlo,hhi⟩ := BinaryOffender.exists_sylow_central_displacement
    ρ hf A S hA hne hAS hnS hd
  obtain ⟨b,hb,rfl⟩ := ha
  refine ⟨b,hb,ho,?_,hlo,hhi⟩
  intro t ht
  apply hc
  rw [hS]
  exact mem_map_of_mem q ht

/-- Once recognized, the original V-image supplies a rank-two central involution. -/
theorem source_chosen_partner_rank_two_of_marked_model
    {T : Sylow 2 G} {M Mc V H ZS L U B : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS) (hn : ¬ V ≤ twoCoreIn Mc)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) W)
    (d : BinaryConjugationSection L U B (ρ.comp (QuotientGroup.mk' (pCore 2 L))))
    (hU : U ≤ twoCoreIn Mc) (hB : centralInvolutions T ≤ B)
    (hp : PartnerChiefQuotientProperties T V L ρ)
    (hm : SmallDisplacementParabolics.ActionModel ρ) :
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
      (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (ρ (q a) - 1)) = 2 := by
  let : Finite W := Finite.of_surjective (fun u : U => (d.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  let q := QuotientGroup.mk' (pCore 2 L)
  let A := (V.subgroupOf L).map q
  obtain ⟨hf,_,hA,hne,_,S,hS,hAS,hnS,_⟩ := hp
  have hd : ∀ a ∈ A, Module.finrank (ZMod 2) (LinearMap.range (ρ a - 1)) ≤ 2 := by
    rintro a ⟨b,hb,rfl⟩
    exact source_chosen_partner_section_displacement_le_two h hg hMc hZ hn d hU hB b hb
  obtain ⟨a,ha,ho,hc,hr⟩ := hm.exists_rank_two_of_sylow_normal hf A S hA hne hAS hnS hd
  obtain ⟨b,hb,rfl⟩ := ha
  refine ⟨b,hb,ho,?_,hr⟩
  intro t ht
  apply hc
  rw [hS]
  exact mem_map_of_mem q ht

/-- The recognized marked section contradicts the source geometry with no rank premise. -/
theorem source_chosen_false_of_marked_partner_model
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
      PartnerChiefQuotientProperties T V L ρ →
      SmallDisplacementParabolics.ActionModel ρ → False := by
  dsimp only
  intro ρ d hU hB hp hm
  obtain ⟨a,ha,_,_,hr⟩ := source_chosen_partner_rank_two_of_marked_model
    h hg hMc hZ hn ρ d hU hB hp hm
  exact source_chosen_false_of_partner_model_displacement h hg hMc hZ hn hplane
    ρ d hU hB ⟨a,ha,hr.ge⟩ hm

open NoncentralChiefRefinement

/-- Construct the central witness on the literal faithful chief action, before recognition. -/
theorem source_chosen_partner_central_marked_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        σ.comp q = binarySectionRepresentation B U ∧
        PartnerChiefQuotientProperties T V L σ ∧
        ∃ a : L, (a : G) ∈ V ∧ orderOf (q a) = 2 ∧
          (∀ t ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q t)) ∧
          1 ≤ Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ∧
          Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ≤ 2 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ :=
    source_chosen_partner_faithful_marked_chief h hg hMc hZ hquotient hres hs hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,he,hpσ⟩ := hσ
  have d : BinaryConjugationSection L (U.val.map L.subtype) (B.val.map L.subtype)
      (σ.comp q) := by
    rw [show σ.comp q = binarySectionRepresentation B U from he]
    exact ambientBinarySection L B U hc.le
  exact ⟨σ,he,hpσ,source_chosen_partner_marked_central_displacement
    h hg hMc hZ hn σ d hU hB hpσ⟩

end CFSG.Quasithin.Chapter15.Section02
