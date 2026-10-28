module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SeedPlaneMarked
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.TwoAndFive.LinearTwo
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Lift

/-!
# Returning the B.5 seed marking to the literal component section

Seed equality identifies the moved spaces. The component equivalence from
B.5 preparation identifies their fixed vectors and hence their central
quotients. The final consumer retains the canonical map on K/O₂(K), using
the actual starred component and compatible conjugation action.

Source: Aschbacher–Smith, 13.7.18, printed p.945, and13.8.5, p.947.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource ComponentReduction ComponentReduction.PreliminaryActions
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem centralSectionModel_of_seed_mark {K : GroupClass.{u}} {A L : Subgroup G}
    (hLA : ⁅L,A⁆ = L) (p : Prepared ρ K hLA) (hL : IsComponent G L)
    (hi : IsIrrPlus ρ L (moved ρ L))
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) B W)
    (em : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) σ) :
    HasCentralSectionModel ρ L σ
      ((Preparation.seedComponentEquiv ρ hLA p.component_faithful).trans em.groupEquiv) := by
  classical
  let I := moved ρ L
  have hseed := seed_eq_moved_of_irrPlus ρ hLA p hL hi
  have ht := s.space_eq.trans (seedQuotient_moved_eq_top ρ hLA hL)
  let e₀ : I ≃ₗ[ZMod 2] naturalSeedSpace ρ L A := LinearEquiv.ofEq _ _ hseed.symm
  let e : I ≃ₗ[ZMod 2] s.space.toSubmodule := e₀.trans (fullSectionSpaceEquiv s ht)
  let eg := Preparation.seedComponentEquiv ρ hLA p.component_faithful
  have he (l : L) (w : I) :
      e ⟨ρ l w, (subspaceCommutator_invariant ρ ⊤ L l.property w).2 w.property⟩ =
        s.space.toRepresentation (eg l) (e w) := rfl
  let P := (fixedSpace ρ L).comap I.subtype
  have hfix (w : I) : w ∈ P ↔ e w ∈ s.central.toSubmodule := by
    rw [s.central_eq]
    change (∀ l : L, ρ l w = w) ↔
      (∀ x : seedComponentImage ρ hLA, s.space.toRepresentation x (e w) = e w)
    constructor
    · intro hw x
      obtain ⟨l,rfl⟩ := eg.surjective x
      apply Subtype.ext
      apply Subtype.ext
      exact hw l
    · intro hw l
      exact congrArg (fun z : s.space.toSubmodule => (z.val : V)) (hw (eg l))
  have hP : P.map e.toLinearMap = s.central.toSubmodule := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (hfix v).mp hv
    · intro hw
      obtain ⟨v,rfl⟩ := e.surjective w
      exact ⟨v,(hfix v).mpr hw,rfl⟩
  let eqv := Submodule.Quotient.equiv P s.central.toSubmodule e hP
  refine ⟨(fun l w => (subspaceCommutator_invariant ρ ⊤ L l.property w).2 w.property),
    eqv.trans em.linearEquiv, ?_⟩
  intro l w
  change em.linearEquiv (eqv (Submodule.Quotient.mk _)) =
    σ (em.groupEquiv (eg l)) (em.linearEquiv (eqv (Submodule.Quotient.mk w)))
  change em.linearEquiv (Submodule.Quotient.mk (e _)) =
    σ (em.groupEquiv (eg l)) (em.linearEquiv (Submodule.Quotient.mk (e w)))
  exact (congrArg (fun z : s.space.toSubmodule => em.linearEquiv (Submodule.Quotient.mk z))
    (he l w)).trans (em.intertwines (eg l) (Submodule.Quotient.mk (e w)))
end CFSG.Quasithin.ChapterB.SourceInduction

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {G : Type*} [Group G] [Finite G]
  {H V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

/-- The literal raw component section inherits a B.5 seed marking with the
same canonical component quotient map on every representative. -/
theorem source_hasSectionModel_of_seed_mark
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : Section08.TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    {A : Subgroup (Section08.Source.Hstar H)}
    (hLA : ⁅Section08.Source.starImage H K,A⁆ = Section08.Source.starImage H K)
    (p : Prepared ρ KnownSimple.IsKnownSimple hLA)
    (hL : IsComponent (Section08.Source.Hstar H) (Section08.Source.starImage H K))
    (hi : IsIrrPlus ρ (Section08.Source.starImage H K)
      (moved ρ (Section08.Source.starImage H K)))
    (s : MovedSection (seedQuotientAction ρ hLA) (seedComponentImage ρ hLA))
    {B W : Type*} [Group B] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) B W)
    (em : ActionEquiv (s.action.comp (seedComponentImage ρ hLA).subtype) σ) :
    HasSectionModel H V₃ V₁ ρ K hKH σ
      ((Section08.Components.componentStarEquiv H K hKH hK).trans
        ((Preparation.seedComponentEquiv ρ hLA p.component_faithful).trans em.groupEquiv)) := by
  exact hasSectionModel_of_star_model K hKH hK ρ hρ σ _
    (centralSectionModel_of_seed_mark ρ hLA p hL hi s σ em)

end CFSG.Quasithin.Chapter13.Section07
