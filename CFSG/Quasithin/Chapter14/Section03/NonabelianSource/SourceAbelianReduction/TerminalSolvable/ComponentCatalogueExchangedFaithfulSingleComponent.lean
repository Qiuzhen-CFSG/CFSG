module
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.SharpDegree
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentModels
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulGeometrySelection
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelComplete
/-!
# The single component in the faithful exchanged orbit

The sharp original bound d=m+2 excludes two distinct components in the
literal faithful action quotient. Its orbit image is therefore quasisimple.
Faithful transport and maximality of the original component show that the
original orbit is precisely L. Movement by the actual stabilizer follows,
so the unchanged ComponentInput holds for the originally chosen L.

The final theorem applies this to the original central-kernel branch. The
remaining action-model classification and noncentral paired-A5 branch are
separate obligations.
Source: Aschbacher--Smith G.9.3 and G.11.6, printed pp.356 and 366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s

/-- The sharp degree bound makes the faithful image orbit quasisimple. -/
theorem image_orbit_quasisimple : IsQuasisimple (s.image (componentOrbit L ⊤)) := by
  obtain ⟨C,_,hC⟩ := s.exists_image_component_hypothesis
  have hd : finrank (ZMod 2) I ≤ (finrank (ZMod 2) I - 2) + 2 := by
    have := s.dimension_gt_two
    omega
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hC hd
  exact he.symm ▸ hC.component.2

/-- The original component equals its whole orbit. The argument first proves
quasisimplicity of that orbit and then uses maximality of components. -/
theorem orbit_eq_component : componentOrbit L ⊤ = L := by
  let : IsQuasisimple (s.image (componentOrbit L ⊤)) := s.image_orbit_quasisimple
  let : IsQuasisimple (componentOrbit L ⊤) := IsQuasisimple.of_mulEquiv s.orbitEquiv.symm
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  have hc : IsComponent F.TerminalHdot (componentOrbit L ⊤) :=
    ⟨(inferInstance : (componentOrbit L ⊤).Normal).isSubnormal,inferInstance⟩
  exact (s.component.eq_of_le hc (le_componentOrbit L ⊤)).symm

/-- The literal stabilizer moves the originally chosen component. -/
theorem component_actor_moved : ⁅L,actor (F := F) (g := g) (I := I)⁆ ≠ ⊥ := by
  have hm := s.orbit_actor_moved
  rwa [s.orbit_eq_component] at hm

/-- All original G.9 fields now hold for the image of the originally chosen
component, with no movement or classification callback. -/
theorem componentInput : s.ComponentInput :=
  s.componentInput_of_actor_moved s.component_actor_moved

/-- The exhaustive carrier catalogue applies to the same faithful orbit
image and its original action, after the two-component branch is excluded. -/
theorem image_orbit_models :
    (IsSimpleGroup (s.image (componentOrbit L ⊤)) ∧
      Chapter1.Section02.LocalModels.TheoremCModel (s.image (componentOrbit L ⊤))) ∨
    (Nonempty (center (s.image (componentOrbit L ⊤)) ≃* Multiplicative (ZMod 3)) ∧
      Chapter1.Section02.LocalModels.ThreeCoverModel (s.image (componentOrbit L ⊤))) := by
  have hc := s.componentInput
  change ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
    (s.image (actor (F := F) (g := g) (I := I))) (s.image L)
    (s.image (componentOrbit L ⊤)) (finrank (ZMod 2) I - 2) at hc
  have he : s.image (componentOrbit L ⊤) = s.image L :=
    congrArg s.image s.orbit_eq_component
  rw [he] at hc
  exact he.symm ▸ hc.single_component_models

end ExchangedFaithfulSource

namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)


/-- The original central-kernel branch has one component and supplies the
literal original ComponentInput without a movement or catalogue premise. -/
theorem faithful_single_component :
    componentOrbit L ⊤ = L ∧ s.faithful_source.ComponentInput :=
  ⟨s.faithful_source.orbit_eq_component,s.faithful_source.componentInput⟩

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
