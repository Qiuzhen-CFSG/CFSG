module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Centers
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Transport
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# The linear-two seed comparison

Ratio one on the actual central quotient forces equality of the offender rank
and fixed codimension on the seed. The offender is therefore one of the source
Sylow subgroups. Equivariant transport of the literal central quotients gives
the natural original component action and lifts Irr⁺ to the original ambient
module. Faithfulness then reflects containment of the image as inner action.

The full-moved-space hypothesis is the separate input produced by the
B.5.1-to-seed comparison; no equality with the ambient moved space is assumed.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2(1),
B.5.1(1i), and B.5.9, printed pp.86, 99 and 107.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}
    {A L : Subgroup G} (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA)

include p in
theorem seed_section_codim_le
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (B : Subgroup (SeedQuotient ρ hLA)) :
    fixedCodim s.action B ≤ fixedCodim (seedQuotientAction ρ hLA) B := by
  let := p.source.finite_module
  have h₁ := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central B
  have h₂ := fixedCodim_subrepresentation_le (seedQuotientAction ρ hLA) s.space B
  exact (Nat.le_add_right _ _).trans (h₁.trans h₂)

include p in
theorem seed_section_ratio_one
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hq : quadraticRatio s.action = 1) :
    IsBestOffender s.action (seedOffenderImage ρ hLA) ∧ SeedRankEquality ρ A L := by
  let := p.source.finite_module
  have ho := p.minimal.1.isOffender _
  have hs : IsOffender s.action (seedOffenderImage ρ hLA) :=
    ⟨ho.1, (seed_section_codim_le ρ hLA p s _).trans ho.2⟩
  obtain ⟨hb, he⟩ := hs.best_and_codim_eq_of_quadraticRatio_eq_one _ hq
  have hc : fixedCodim (seedQuotientAction ρ hLA) (seedOffenderImage ρ hLA) =
      rank (seedOffenderImage ρ hLA) :=
    le_antisymm ho.2 (he ▸ seed_section_codim_le ρ hLA p s _)
  rw [seedOffenderImage_fixedCodim, seedOffenderImage_rank] at hc
  exact ⟨hb, hc.symm⟩

omit [Finite G] in
theorem seed_irrPlus_of_section
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      s.space.toSubmodule) : IsIrrPlus ρ L (naturalSeedSpace ρ L A) := by
  have ht : s.space.toSubmodule = ⊤ := s.space_eq.trans hm
  have hi' : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) ⊤ := ht ▸ hi
  let H := L ⊔ A
  have hU : (⊤ : Submodule (ZMod 2) (naturalSeedSpace ρ L A)).map
      (naturalSeedSpace ρ L A).subtype = naturalSeedSpace ρ L A := by simp
  have hj : IsIrrPlus (ρ.comp H.subtype) (L.subgroupOf H) (naturalSeedSpace ρ L A) := by
    rw [← hU]
    exact IsIrrPlus.map_embedding (ρ.comp H.subtype) (seedQuotientAction ρ hLA)
      (seedQuotientMap ρ hLA) (naturalSeedSpace ρ L A).subtype
      (naturalSeedSpace ρ L A).subtype_injective (fun _ _ => rfl)
      (L.subgroupOf H) ⊤ hi'
  let e := Subgroup.subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  exact hj.of_intertwining (ρ.comp H.subtype) ρ e.toMonoidHom e.surjective
    (LinearMap.id) (fun _ _ h => h) (fun _ _ => rfl) (by simp)


section GeneralSection
variable {D E W : Type*} [Group D] [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) D W} {X : Subgroup D}

noncomputable def fullSectionSpaceEquiv (s : MovedSection σ X)
    (ht : s.space.toSubmodule = ⊤) : W ≃ₗ[ZMod 2] s.space.toSubmodule where
  toFun x := ⟨x, ht.symm ▸ Submodule.mem_top⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Finite G] in
theorem fullSectionSpaceEquiv_fixed (s : MovedSection σ X)
    (ht : s.space.toSubmodule = ⊤) (τ : Representation (ZMod 2) E W)
    (e : E ≃* X) (he : ∀ g w, τ g w = σ (e g) w) :
    (fixed τ).toSubmodule.map (fullSectionSpaceEquiv s ht).toLinearMap =
      s.central.toSubmodule := by
  rw [s.central_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ l
    obtain ⟨g, hg⟩ := e.surjective l
    apply Subtype.ext
    change σ l y = y
    rw [← hg, ← he]
    exact hy g
  · intro hx
    refine ⟨x.val, ?_, rfl⟩
    intro g
    rw [he]
    exact congrArg Subtype.val (hx (e g))

noncomputable def fullReducedSectionEquiv (s : MovedSection σ X)
    (ht : s.space.toSubmodule = ⊤) (τ : Representation (ZMod 2) E W)
    (e : E ≃* X) (he : ∀ g w, τ g w = σ (e g) w) :
    ActionEquiv (reducedAction τ) (s.action.comp X.subtype) where
  groupEquiv := e
  linearEquiv := Submodule.Quotient.equiv _ _ (fullSectionSpaceEquiv s ht)
    (fullSectionSpaceEquiv_fixed s ht τ e he)
  intertwines g x := by
    induction x using Submodule.Quotient.induction_on with | _ x =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    exact Subtype.ext (he g x)
end GeneralSection

noncomputable def seedReducedSectionEquiv
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤) :
    ActionEquiv (reducedAction (seedComponentAction ρ hLA))
      (s.action.comp (seedComponentImage ρ hLA).subtype) :=
  fullReducedSectionEquiv s (s.space_eq.trans hm) (seedComponentAction ρ hLA)
    (seedComponentEquiv ρ hLA p) (fun _ _ => rfl)

include p in
/-- The SL₂ row, on the actual seed and its actual Sylow offender image. -/
theorem compared_linearTwo_of_source
    (hr : primeRank 3 L = 1)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    (hm : moved (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA) = ⊤)
    (hi : IsIrrPlus (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA)
      c.sectionData.space.toSubmodule)
    (_hf : Function.Injective c.sectionData.action)
    (_hir : IsIrreducible (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype))
    (_hex : seedComponentImage ρ hLA = ⊤ ∨
      (∀ T : Sylow 2 (SeedQuotient ρ hLA), seedComponentImage ρ hLA ⊔ (T : Subgroup _) = ⊤) ∧
        OuterNaturalAction c.sectionData.action)
    (F : BinaryField)
    (_hg : offenderSubgroup c.sectionData.action = seedComponentImage ρ hLA)
    (e : ActionEquiv (c.sectionData.action.comp (seedComponentImage ρ hLA).subtype)
      (linearNatural F 2))
    (ho : ∀ B, IsBestOffender c.sectionData.action B → ∃ T : Sylow 2 (seedComponentImage ρ hLA),
      B = (T : Subgroup _).map (seedComponentImage ρ hLA).subtype)
    (hq : quadraticRatio c.sectionData.action = 1) : ComparedCase ρ hLA := by
  obtain ⟨hb, he⟩ := seed_section_ratio_one ρ hLA p c.sectionData hq
  obtain ⟨T, hT⟩ := ho _ hb
  let f := seedReducedSectionEquiv ρ hLA p c.sectionData hm
  have hn : IsLinearNatural (reducedAction (seedComponentAction ρ hLA)) F 2 :=
    ⟨{ groupEquiv := f.groupEquiv.trans e.groupEquiv
       linearEquiv := f.linearEquiv.trans e.linearEquiv
       intertwines := fun g v =>
         (congrArg e.linearEquiv (f.intertwines g v)).trans
           (e.intertwines (f.groupEquiv g) (f.linearEquiv v)) }⟩
  have ha : seedOffenderImage ρ hLA ≤ seedComponentImage ρ hLA := by
    rw [hT]
    rintro _ ⟨t, _, rfl⟩
    exact t.property
  exact .linearTwo F hn (seed_irrPlus_of_section ρ hLA c.sectionData hm hi)
    ⟨T, hT⟩ (inducesInner_of_seedOffenderImage_le ρ hLA p ha)
    (seed_disjoint_of_source ρ hLA p hr c) he

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
