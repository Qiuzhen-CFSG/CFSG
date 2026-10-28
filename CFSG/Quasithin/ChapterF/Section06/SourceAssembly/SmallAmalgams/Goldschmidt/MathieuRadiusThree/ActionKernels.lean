module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalBranchAction

/-!
# Kernels of the literal radius-two action

The action on the six forward vertices has kernel exactly the pointwise
radius-two ball fixer. Fixing those six vertices also fixes their three
branches. The same kernel is retained by the faithful binary-block model,
so its image is the actual local quotient, even for an infinite ambient group.
The radius-two label groups at nearby centers normalize one another; their
commutator therefore lies in their intersection, with no ambient normality
assumption.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
the opening of (6.12), pp.403--404.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

namespace BranchFrame
variable {a : RankTwo.Vertex F} (f : BranchFrame F a) (h : CubicTreeAction F)

theorem sphereAction_eq_one_iff (g : RankTwo.stabilizer F a) :
    f.sphereAction h g = 1 ↔ g.val ∈ RankTwo.ballKernel F a 2 := by
  constructor
  · intro hg w hw
    have hbranch (i : Fin 3) : f.branchAction g i = i := by
      have hh := f.sphereAction_block h g (i, 0)
      rw [hg] at hh
      exact hh.symm
    have hd := (RankTwo.mem_ball_iff F h.generated a w 2).mp hw
    have hcases : (RankTwo.graph F).dist a w = 0 ∨
        (RankTwo.graph F).dist a w = 1 ∨ (RankTwo.graph F).dist a w = 2 := by omega
    rcases hcases with hd | hd | hd
    · rw [← h.tree.connected.dist_eq_zero_iff.mp hd]
      exact g.property
    · obtain ⟨i, hi⟩ := f.e.surjective ⟨w, dist_eq_one_iff_adj.mp hd⟩
      have hi' : (f.e i).val = w := congrArg Subtype.val hi
      rw [← hi', ← f.branchAction_eval, hbranch]
    · obtain ⟨x, hx⟩ := (f.sphereEquiv h).surjective ⟨w, hd⟩
      have hx' : f.point x = w := congrArg Subtype.val hx
      rw [← hx', ← f.sphereAction_eval h g x, hg]
      rfl
  · intro hg
    apply Equiv.ext
    intro x
    apply f.point_injective h
    rw [f.sphereAction_eval]
    exact hg _ ((RankTwo.mem_ball_iff F h.generated a _ 2).mpr
      (le_of_eq (f.point_dist h x)))

/-- The denominator is a subgroup of the actual vertex stabilizer. -/
theorem sphereAction_ker :
    (f.sphereAction h).ker =
      (RankTwo.ballKernel F a 2).subgroupOf (RankTwo.stabilizer F a) := by
  ext g
  exact f.sphereAction_eq_one_iff h g

theorem blockAction_ker :
    (f.blockAction h).ker =
      (RankTwo.ballKernel F a 2).subgroupOf (RankTwo.stabilizer F a) := by
  ext g
  change f.blockAction h g = 1 ↔ g.val ∈ RankTwo.ballKernel F a 2
  rw [← f.sphereAction_eq_one_iff h]
  constructor
  · intro hg
    rw [← f.blockAction_coordinates, hg, map_one]
  · intro hg
    apply Theory.SpecificGroups.SymmetricSix.SynthemeCalculation.coordinateHom_injective
    rw [f.blockAction_coordinates, hg, map_one]

/-- The six-point model image is the literal radius-two quotient. -/
def radiusTwoQuotientEquiv :
    (RankTwo.stabilizer F a ⧸
      (RankTwo.ballKernel F a 2).subgroupOf (RankTwo.stabilizer F a)) ≃*
        (f.blockAction h).range :=
  (QuotientGroup.quotientMulEquivOfEq (f.blockAction_ker h).symm).trans
    (QuotientGroup.quotientKerEquivRange (f.blockAction h))

end BranchFrame

namespace CanonicalLabelSetup
variable {s : ℕ} (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hr : d.radius = 3) (hs : 4 ≤ s)

include h hr hs in
theorem nearby_labelBall_normalizes {a b : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).dist a b ≤ 2) :
    d.labelBall a 2 ≤ normalizer (d.labelBall b 2 : Set G) := by
  apply le_trans _ (d.labelBall_normalized b 2)
  intro g hg
  have hk := d.labelBall_le_ballKernel h a 2 2 (by omega) hs hg
  exact hk b ((RankTwo.mem_ball_iff F h.generated a b 2).mpr hab)

include h hr hs in
theorem nearby_labelBall_commutator_le {a b : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).dist a b ≤ 2) :
    ⁅d.labelBall a 2, d.labelBall b 2⁆ ≤ d.labelBall a 2 ⊓ d.labelBall b 2 := by
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp
      (d.nearby_labelBall_normalizes h hr hs (by simpa only [dist_comm] using hab))
  · exact le_normalizer_iff_commutator_le_right.mp
      (d.nearby_labelBall_normalizes h hr hs hab)

end CanonicalLabelSetup
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
