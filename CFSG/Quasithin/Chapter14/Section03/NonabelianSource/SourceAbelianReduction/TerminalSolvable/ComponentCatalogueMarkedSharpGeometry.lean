module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedGeometry
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.SharpDegree

/-!
# Sharp marked constituent geometry on the original image

The original degree bounds exclude two distinct components in a two-copy
constituent and in a proper faithful constituent. Equality is lifted from
the faithful constituent quotient to the original normal component orbit.
The original fixed marked line also transports through exactly this quotient.
These geometric reductions do not assert the remaining model recognition.

Source: Aschbacher–Smith G.9.3, G.11.7–8, printed pp.353–357,367–369.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
namespace MarkedAction
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H X : Subgroup D)
  (I : Submodule (ZMod 2) W) (hH : H ≤ subspaceStabilizer ρ I)
  (hX : X ≤ subspaceStabilizer ρ I)

/-- The fixed marked line descends through the literal action kernel quotient. -/
theorem fixedSpace_image_eq_line (v : I)
    (hfix : fixedSpace ρ X = Submodule.span (ZMod 2) {(v : W)}) :
    fixedSpace (kerRepresentation (action ρ H X I hH hX)) (image ρ H X I hH hX X) =
      Submodule.span (ZMod 2) {v} := by
  ext w
  constructor
  · intro hw
    have hf : (w : W) ∈ fixedSpace ρ X := by
      intro x
      let a : (H ⊔ X : Subgroup D) := ⟨x,(show X ≤ H ⊔ X from le_sup_right) x.property⟩
      let b : image ρ H X I hH hX X :=
        ⟨projection ρ H X I hH hX a,mem_map_of_mem _ x.property⟩
      exact congrArg Subtype.val (hw b)
    rw [hfix,Submodule.mem_span_singleton] at hf
    obtain ⟨c,hc⟩ := hf
    exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc⟩
  · intro hw a
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨x,rfl⟩ := (projection ρ H X I hH hX).subgroupMap_surjective
      (X.subgroupOf (H ⊔ X)) a
    have hv : (v : W) ∈ fixedSpace ρ X := hfix ▸ Submodule.mem_span_singleton_self _
    apply Subtype.ext
    change ρ (x : (H ⊔ X : Subgroup D)) (c • (v : W)) = c • (v : W)
    rw [map_smul,show ρ (x : (H ⊔ X : Subgroup D)) (v : W) = v from hv ⟨x,x.property⟩]
end MarkedAction

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- The actual component orbit equals the originally moved component in the
two-copy branch, with all G.9 earlier-source inputs discharged. -/
theorem orbit_eq_component_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    componentOrbit L ⊤ = L := by
  have hc := s.componentHypothesis_of_double_dimension hk hd
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hc
    (by have hi := s.dimension_gt_two; omega)
  exact (MarkedAction.image_eq_iff F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful _ s.irreducible) L (le_componentOrbit L ⊤)).mp he

/-- A proper chosen constituent lies in the isotropic alternative, so its
original actor rank gives the sharp degree needed for the genuine G.9 input. -/
theorem orbit_eq_component_of_actorFaithful_of_ne_top
    (hf : ActorFaithful (F := F) (g := g) (I := I)) (hi : I ≠ ⊤) :
    componentOrbit L ⊤ = L := by
  have hform := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem).2.2.2
  have hiso := hform.resolve_right (fun h => hi h.1)
  have hd := B.twice_finrank_le_of_isotropic s.hypothesis.nondegenerate I hiso
  have hdim := s.actor_dimension
  have hc := s.componentHypothesis_of_actorFaithful hf
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hc (by omega)
  exact (MarkedAction.image_eq_iff F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful _ s.irreducible) L (le_componentOrbit L ⊤)).mp he

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
