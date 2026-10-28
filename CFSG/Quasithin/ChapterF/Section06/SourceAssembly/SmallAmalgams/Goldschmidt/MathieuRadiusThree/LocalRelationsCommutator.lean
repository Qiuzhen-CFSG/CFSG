module

public import Theory.GroupTheory.MutualBinaryActions.IntersectionBound
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelElementary
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.ActionKernels

/-!
# The small commutator in the radius-three label argument

The two radius-two label groups at nearby same-side centers are abelian
of order at most sixteen and normalize one another. If their intersection
has order at least eight, both mutual conjugation images have order at most
two, and consequently the commutator has order at most two. Both label
groups lie in the first center's finite stabilizer, so this argument retains
the possibly infinite ambient group of the original tree action.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
the intersection-size contradiction preceding (6.12.3), printed p.404.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

theorem CanonicalLabelSetup.nearby_labelBall_commutator_card_le_two_of_eight_le_intersection
    (d : CanonicalLabelSetup F s) (h : CubicTreeAction F)
    (hr : d.radius = 3) (hs : 4 ≤ s)
    {a b : RankTwo.Vertex F} (ha : a.type = d.side) (hb : b.type = d.side)
    (hab : (RankTwo.graph F).dist a b ≤ 2)
    (hI : 8 ≤ Nat.card (d.labelBall a 2 ⊓ d.labelBall b 2 : Subgroup G)) :
    Nat.card (⁅d.labelBall a 2, d.labelBall b 2⁆ : Subgroup G) ≤ 2 := by
  have hA := d.radiusTwo_card_le h (by omega) hs a ha
  have hB := d.radiusTwo_card_le h (by omega) hs b hb
  let : IsElementaryAbelian 2 (d.labelBall a 2) := hA.1
  let : IsElementaryAbelian 2 (d.labelBall b 2) := hB.1
  let : Finite (RankTwo.stabilizer F a) := h.finite_stabilizer a
  have hAK : d.labelBall a 2 ≤ RankTwo.stabilizer F a :=
    d.labelBall_le_stabilizer a 2 (by omega) (by omega)
  have hBK : d.labelBall b 2 ≤ RankTwo.stabilizer F a := by
    intro g hg
    have hk := d.labelBall_le_ballKernel h b 2 2 (by omega) hs hg
    exact hk a ((RankTwo.mem_ball_iff F h.generated b a 2).mpr
      (by simpa only [dist_comm] using hab))
  apply Subgroup.commutator_card_le_two_of_large_abelian_intersection_in_finite_subgroup
    (d.labelBall a 2) (d.labelBall b 2) (RankTwo.stabilizer F a) hAK hBK
  · exact d.nearby_labelBall_normalizes h hr hs (by simpa only [dist_comm] using hab)
  · exact d.nearby_labelBall_normalizes h hr hs hab
  · omega
  · omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
