module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ComparisonOvergroup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityActualPairSource
public import Theory.GroupTheory.CComponent.A5PairOddOvergroups

/-!
# The complete moved-comparison Hall branch

A comparison component smaller than O²(H) is moved by the original Sylow.
If its own two-core quotient is not A₅, source moved-component maximality
forces equality with the Borel-normalized containing component, and the
original Hall lies in the orbit Borel. If that quotient is A₅, its actual
normalizer has index two. The exchanged-A₅ prime-support theorem makes
every odd subgroup of the proper overlap H ∩ M a three-group, including
the prescribed Hall. This uses the comparison quotient, never the original
L's non-A₅ hypothesis in its place.

The consumer in MovingHall.Source combines the first case with the proved
terminal contradiction and the second with its direct Hall conclusion.
Only the single comparison K = O²(H) remains there. The direct A₅ bound
does not assert Hall placement in that comparison branch.
Source: Aschbacher–Smith 1.2.8(3), 10.2.3, printed pp.506–507,745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 ChapterB ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : MovingHall.Context D H B}

/-- The selected component and its containing component belong to the
original full-Sylow local family. -/
theorem ComparisonConfiguration.local_components (c : ComparisonConfiguration D ctx) :
    c.component.map H.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      c.overcomponent ∈ Chapter1.L G (T : Subgroup G) := by
  have hK : c.component.map H.subtype ∈ Chapter1.cComponentsIn H := by
    refine ⟨map_subtype_le _,?_⟩
    have hm : (c.component.map H.subtype).subgroupOf H = c.component :=
      comap_map_eq_self_of_injective H.subtype_injective _
    exact hm.symm ▸ c.component_isCComponent
  have hKH := Chapter1.lemma_1_2_6 T ctx.hstar.1.1
  have hTM : (T : Subgroup G) ≤ c.ambient :=
    (show (T : Subgroup G) ≤ H from ctx.hstar.1.1.2).trans
      (le_sup_right.trans c.borel_overgroup)
  have hIM := Chapter1.lemma_1_2_6 T ⟨Chapter1.mem_H_of_isTwoLocal c.maximal.1,hTM⟩
  exact ⟨hKH.2 (hKH.1 hK),hIM.2 (hIM.1 c.overcomponent_mem)⟩

/-- A comparison smaller than O²(H) is moved by the original Sylow. -/
theorem ComparisonConfiguration.moved
    (c : ComparisonConfiguration D ctx) (hne : c.component ≠ pResidual 2 H) :
    c.component.map H.subtype <
      conjugateSpanBy (c.component.map H.subtype) (T : Subgroup G) := by
  apply lt_of_le_of_ne (le_conjugateSpanBy _ _)
  intro he
  have hr := comparison_residual_eq_span D ctx c.component c.component_isCComponent c.generates
  exact hne ((map_injective H.subtype_injective) (he.trans hr.symm))

/-- The comparison's own non-A₅ hypothesis, not the original L hypothesis,
forces equality with its containing component in the moved branch. -/
theorem ComparisonConfiguration.overcomponent_eq_of_moved_nonA5
    (c : ComparisonConfiguration D ctx) (hne : c.component ≠ pResidual 2 H)
    (hnot : ¬ ClassicalGroup.IsPSL (c.component ⧸ pCore 2 c.component) 2 4) :
    c.component.map H.subtype = c.overcomponent := by
  let a := c.component.equivMapOfInjective H.subtype H.subtype_injective
  let e := QuotientGroup.congr (pCore 2 c.component)
    (pCore 2 (c.component.map H.subtype)) a (pCore_map_iso 2 a)
  have hnot' : ¬ ClassicalGroup.IsPSL
      (c.component.map H.subtype ⧸ pCore 2 (c.component.map H.subtype)) 2 4 :=
    fun hh => hnot (hh.of_mulEquiv e)
  obtain ⟨hK,hI⟩ := c.local_components D
  have hm := Chapter1.Section02.MovedMaximality.moved_local_mem_LStar
    D.simpleQTKE T hK (c.moved D hne) hnot'
  exact (hm.2 _ hI c.component_le).symm

/-- The source two-orbit theorem gives the literal comparison normalizer
index when the component is smaller than the residual. -/
theorem ComparisonConfiguration.normalizer_index_two_of_moved
    (c : ComparisonConfiguration D ctx) (hne : c.component ≠ pResidual 2 H) :
    (normalizer (c.component : Set H)).index = 2 := by
  have hsq := Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ
      c.component_isCComponent with hn | hi
  · let := hn
    have hS : (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ normalizer (c.component : Set H) := by
      rw [normalizer_eq_top]
      exact le_top
    have hTG := (map_mono (f := H.subtype) hS).trans (c.component.le_normalizer_map H.subtype)
    have hSm : (T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype =
        (T : Subgroup G) := map_subgroupOf_eq_of_le ctx.hstar.1.1.2
    rw [hSm] at hTG
    exact ((c.moved D hne).not_ge (conjugateSpanBy_le le_rfl hTG)).elim
  · exact hi

/-- The original Hall lies in a proper Sylow overgroup of H. The exchanged
A₅ comparison therefore gives its three-group bound directly. -/
theorem ComparisonConfiguration.hall_isThreeGroup_of_moved_a5
    (c : ComparisonConfiguration D ctx) (hne : c.component ≠ pResidual 2 H)
    (e : (c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) :
    IsPGroup 3 B := by
  have hS : (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ D.maximalLocal.subgroupOf H := by
    intro x hx
    exact le_normalizer_componentOrbit L T hx
  have hproper : D.maximalLocal.subgroupOf H ≠ ⊤ :=
    fun he => ctx.hstar.1.2 (subgroupOf_eq_top.mp he)
  exact c.component_isCComponent.a5_pair_odd_subgroup_isThreeGroup
    (T.subtype ctx.hstar.1.1.2) c.component e
    (c.normalizer_index_two_of_moved D hne) c.generates
    (D.maximalLocal.subgroupOf H) B hS hproper ctx.hall_le ctx.hall_odd

/-- Every moved comparison branch now gives either the required Hall bound
or literal Hall placement. Only the single comparison remains for source assembly. -/
theorem ComparisonConfiguration.hall_three_or_placed_of_moved
    (c : ComparisonConfiguration D ctx) (hne : c.component ≠ pResidual 2 H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    IsPGroup 3 B ∨ B.map H.subtype ≤ sourceOrbitBorel T L := by
  by_cases ha : ClassicalGroup.IsPSL (c.component ⧸ pCore 2 c.component) 2 4
  · obtain ⟨E,_,_,hE,⟨a⟩⟩ := ha
    obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
    exact Or.inl (c.hall_isThreeGroup_of_moved_a5 D hne (a.trans b))
  · exact Or.inr (c.hall_le_borel_of_eq D e (c.overcomponent_eq_of_moved_nonA5 D hne ha))

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
