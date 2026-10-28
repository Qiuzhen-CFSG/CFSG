module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedModels
public import Theory.GroupTheory.GeneralizedFitting.ComponentSimpleQuotient
public import Theory.Representation.NormalComponentConstituents.CenterlessQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Recognition and original-component lift in the paired branch

The literal image of the component orbit on I is A5. Its centerless quotient
forces the orbit center to vanish by ambient faithful irreducibility. The
index-two component orbit then identifies the original component with A5,
even when that original factor acts trivially on I. Finally the existing
small-actor source lift gives the actual local subgroup and component cases.

Source: Aschbacher--Smith G.10.15 and 14.3.15,
printed pp.362--363 and 994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedPairedSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedPairedSource T M Mc F g B v L I)
include s

theorem orbit_center_eq_bot_of_image_alternating_five
    (e : s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 5)) :
    center (componentOrbit L ⊤) = ⊥ := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  have hQ : center (s.image H) = ⊥ := by
    apply bot_unique
    intro a ha
    have hh := ((centerCongr e) ⟨a,ha⟩).property
    change e a ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact mem_bot.mpr (e.map_eq_one_iff.mp hh)
  apply center_eq_bot_of_constituent_quotient F.terminalRepresentation
    s.hypothesis.faithful (s.hypothesis.irreducible_of_not_solvable s.nonsolvable)
    H I s.selected.invariant (s.selected.isIrrPlus.ne_bot F.terminalRepresentation)
    s.orbitProjection s.orbitProjection_surjective hQ
  intro a ha1
  calc
    _ = s.imageAction (s.orbitProjection a).val := rfl
    _ = s.imageAction (1:s.image H).val := congrArg (fun b => s.imageAction b.val) ha1
    _ = 1 := map_one s.imageAction

theorem component_alternating_five_of_image
    (e : s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 5)) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  let : IsSimpleGroup (s.image (componentOrbit L ⊤)) := e.isSimpleGroup
  obtain ⟨a⟩ := Theory.GroupTheory.ExchangedOrbit.component_equiv_simple_quotient
    s.component s.normalizer_index_eq_two s.orbitProjection s.orbitProjection_surjective
    (s.orbit_center_eq_bot_of_image_alternating_five e)
  exact ⟨a.trans e⟩

/-- The literal constituent image is A5, with every catalogue row discharged. -/
theorem image_alternating_five :
    Nonempty (s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 5)) :=
  PairedA5Models.alternating_five_of_selfDual_sharp_elementary
    s.image_component_hypothesis (by have := s.dimension_gt_two; omega)
    s.quotient_image_sylow_elementary s.image_selfDual

/-- Recognition of the original component, allowing that it is the factor
killed by the selected constituent. -/
theorem component_alternating_five : Nonempty (L ≃* alternatingGroup (Fin 5)) :=
  s.component_alternating_five_of_image s.image_alternating_five.some

/-- The original component cases in the noncentral-kernel branch. -/
theorem component_image_cases : ComponentImageCases L :=
  Or.inr (Or.inl (Or.inl s.component_alternating_five))

/-- The actual ambient local lift of the original component. -/
theorem local_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  source_component_catalogue_of_small_actor_image
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis s.small_actor s.component s.moved
    s.component_image_cases

end ExchangedPairedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
