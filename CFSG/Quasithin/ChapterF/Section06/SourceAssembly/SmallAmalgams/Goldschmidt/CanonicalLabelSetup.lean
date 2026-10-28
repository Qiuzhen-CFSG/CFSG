module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralBalance
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Canonical involution data for the two terminal source branches

This record exposes the geometric output of Goldschmidt (6.4)--(6.8)
consumed by the radius-two and odd-radius terminal arguments. Its existence
is a separate theorem to be proved from the actual `TwoPerfectTreeAction F`, the two local exclusions
`∀ i, ¬ Nonempty (pResidual 2 (F i) ≃* Multiplicative (ZMod 3))` and
`∀ i, ¬ Nonempty (pResidual 2 (F i) ≃* alternatingGroup (Fin 4))`, the minimal
singularity index `s ≥ 5` (both short regularity and a length-s failure), and
the earlier-source (5.3) nonmembership in the track fixer. No existence
assertion is included in this interface.

The label is meaningful on its specified vertex type. Ball claims retain the
precise short-arc bound. For radius two they give the entire ball of radius
three and the entire moved sphere of radius four, since the source has s≥5.
For odd radius the exact whole-track interval remains available without any
unproved inequality between radius and singularity index.
-/

@[expose] public section
open Subgroup SimpleGraph
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G]

structure CanonicalLabelSetup (F : Bool → Subgroup G) (s : ℕ) where
  side : Bool
  radius : ℕ
  label : RankTwo.Vertex F → G
  order_two : ∀ v, v.type = side → orderOf (label v) = 2
  central : ∀ v, v.type = side → label v ∈ RankTwo.stabilizer F v ∧
    ∀ g ∈ RankTwo.stabilizer F v, Commute (label v) g
  conjugate : ∀ (g : G) v, v.type = side →
    label (g • v) = g * label v * g⁻¹
  radius_cases : radius = 2 ∨ Odd radius ∧ 3 ≤ radius
  fixes_ball : ∀ v, v.type = side → ∀ w,
    (RankTwo.graph F).dist v w ≤ radius + 1 →
    (RankTwo.graph F).dist v w ≤ s → label v • w = w
  moves_sphere : ∀ v, v.type = side → radius + 2 ≤ s → ∀ w,
    (RankTwo.graph F).dist v w = radius + 2 → label v • w ≠ w
  neighbor_product : ∀ (v u₁ u₂ u₃ : RankTwo.Vertex F),
    (RankTwo.graph F).Adj v u₁ → (RankTwo.graph F).Adj v u₂ →
    (RankTwo.graph F).Adj v u₃ → u₁ ≠ u₂ → u₁ ≠ u₃ → u₂ ≠ u₃ →
    u₁.type = side → label u₁ * label u₂ * label u₃ = 1
  edge_center_cyclic : ∀ (v w : RankTwo.Vertex F), (RankTwo.graph F).Adj v w →
    IsCyclic (Subgroup.center (RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w : Subgroup G))
  track : Track (RankTwo.graph F) G
  center : ℤ
  center_type : (track.vertex center).type = side
  interval : track.CentralInterval (label (track.vertex center))
  central_left : interval.centralLeft = center - 1
  central_right : interval.centralRight = center + 1
  fixed_left : interval.fixedLeft = center - (radius + 1)
  fixed_right : interval.fixedRight = center + (radius + 1)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
