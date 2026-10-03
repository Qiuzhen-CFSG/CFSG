module
public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# The distance-two neighborhood commutator stays in each neighboring core

At critical length greater than four, let W be the literal distance-two
V-join at the first vertex and R its residual two-core O₂(E_first). For
each neighbor middle of first, [W,R] lies in W intersect R intersect
Q_middle. All subgroups belong to the same original graph and path.

Radius-four critical minimality puts W inside every neighboring core.
The first stabilizer normalizes both W and R, and R lies in each neighboring
stabilizer. Three applications of the normalizer/commutator criterion
therefore give the required simultaneous bounds.

This is the actual subgroup relation used for W=[W_first,Q]C in
Stellmacher (9.10)(12), printed p.59, and in the preceding residual-edge
calculation (10). No classification or extraction hypothesis is required.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_neighborhood_residual_commutator_le_intersection
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 4 < ctx.criticalPath.length)
    (middle : ctx.Γ.Vertex)
    (hmiddle : middle ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep) :
    let W := DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep
    let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
    ⁅W,R⁆ ≤ W ⊓ (R ⊓ QAt ctx.Γ middle) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := DistanceTwoNeighborhoodV Γ cp.firstStep
  let P := GAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let R := twoCoreIn E
  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx hb
  have hQP : QAt Γ cp.firstStep ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.stabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hWP : W ≤ P := hgeometry.1.trans hQP
  have hE : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hRQ : R ≤ QAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hRmiddle : R ≤ GAt Γ middle := hRQ.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core
      cp.firstStep middle hmiddle default).2.2)
  have hWmiddle : W ≤ QAt Γ middle := by
    apply (distance_two_neighborhood_le_source_odd_w Γ cp.firstStep).trans
    apply source_odd_w_le_core_of_distance Γ cp cp.firstStep middle
    have hdist := nine_eight_adjacent_distance_le Γ (target := middle)
      ((mem_neighborhood_iff_adjacent Γ).mp hmiddle)
    rw [Γ.distance_refl] at hdist
    change Γ.distance cp.firstStep middle ≤ 1 at hdist
    change 4 < cp.length at hb
    change Γ.distance cp.firstStep middle + 3 < cp.length
    omega
  have hWW : ⁅W,R⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hRP.trans hgeometry.2.2.2.1)
  have hWR : ⁅W,R⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_right.mp
    (hWP.trans hPR)
  have hWQ : ⁅W,R⁆ ≤ QAt Γ middle :=
    (Subgroup.commutator_mono hWmiddle le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hRmiddle.trans (stabilizer_le_normalizer_q Γ middle)))
  exact le_inf hWW (le_inf hWR hWQ)

end Stellmacher.SectionNine
