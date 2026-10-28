module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ComponentPlaneComplete
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.NormalOffenderClassification
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Selection
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes
public import Theory.Representation.BinaryOffender.FaithfulRankOne

/-!
# The actual component selected by a strong quintic section offender

Strict replacement preserves the original offender containment and its
two-dimensional displacement bound. A minimal strong offender centralizes
the Fitting subgroup: B.1.9 makes any noncentral minimal offender have order
two, which cannot be strong in a faithful action. Generalized-Fitting
self-centralization then supplies an actual moved component. Its literal
normal closure and the complete small-displacement source theorem give
Irr⁺ and the four original component families, with no product-case callback.

This is used on the original F/Uc action, where the paired supports supply
the strict inequality and the literal E/Uc plane supplies the moved bound.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem strong_minimal_centralizes_fitting
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) {B : Subgroup G}
    (hB : IsMinimalBestOffender ρ B) (hstrong : IsStrongOffender ρ B) :
    B ≤ centralizer (fittingSubgroup G : Set G) := by
  by_contra hn
  have hmove : ⁅fittingSubgroup G,B⁆ ≠ ⊥ := by
    intro hz
    exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  obtain ⟨b⟩ := ChapterB.FittingStructure.localPlaneLaw ρ hf hcore B hB hmove
  have hr : rank B = 1 := by
    rw [rank,b.actor_card]
    decide
  have hpos := fixedCodim_pos_of_faithful ρ hf hB.1.1.1
  have hlt := hstrong.2
  rw [hr] at hlt
  omega

/-- A strong offender moving at most a plane selects an actual component,
inside the normal closure of an original contained minimal offender. -/
theorem component_of_strong_plane_offender
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple G)
    {A : Subgroup G} (hstrong : IsStrongOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) :
    ∃ B ≤ A, IsMinimalBestOffender ρ B ∧ IsQuadratic ρ B ∧
      IsStrongOffender ρ B ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ B) ≤ 2 ∧
      B ≤ centralizer (fittingSubgroup G : Set G) ∧
      ∃ K, IsComponent G K ∧ ⁅K,B⁆ = K ∧
        K ≤ normalClosure (B : Set G) ∧
        (K.subgroupOf (normalClosure (B : Set G))).Normal ∧
        IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K := by
  obtain ⟨B,hBA,hB,hquad,hBs⟩ := hstrong.exists_quadratic_minimalBestOffender ρ
  have hdB : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ B) ≤ 2 := by
    apply (Submodule.finrank_mono (show subspaceCommutator ρ ⊤ B ≤
      subspaceCommutator ρ ⊤ A from ?_)).trans hd
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,v,hv,rfl⟩
    exact Submodule.subset_span ⟨b,hBA hb,v,hv,rfl⟩
  have hfit := strong_minimal_centralizes_fitting ρ hf hcore hB hBs
  obtain ⟨K,hK,hmove⟩ := ComponentReduction.exists_component_moved ρ hcore hB.1 hfit
  have hn : B ≤ normalizer (K : Set G) := ChapterB.source_lemma_B_1_5_4 ρ hf hB.1 hK
  have hKB : ⁅K,B⁆ = K := by
    rcases hK.commutator_dichotomy B with hz | he
    · exact (hmove hz).elim
    · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
        (he ▸ le_iSup_conjugates K B)
  obtain ⟨hKN,hnK,_⟩ := moved_component_in_normalClosure ρ hf hK hB.1 hKB
  obtain ⟨hirr,hlist⟩ := component_irrPlus_and_actor_of_minimal_plane ρ hf hcore cover
    hK hB hKB hdB
  exact ⟨B,hBA,hB,hquad,hBs,hdB,hfit,K,hK,hKB,hKN,hnK,hirr,hlist⟩

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
