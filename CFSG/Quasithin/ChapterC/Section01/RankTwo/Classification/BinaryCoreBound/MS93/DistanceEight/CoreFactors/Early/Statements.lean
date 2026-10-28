module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Layers

/-!
# Literal output contracts for the remaining early source calculations

`SourcePath` records the path chosen on pp.895--896, with index four at a.
Its extra predecessor records the first Z-inequality, whose left subscript
lies just outside the displayed path. `FirstFacts` spells out all five
clauses of (4.5.1). Its centralizer equality uses the actual quotient map
of G_a by B_a and the original endpoint Z-action. Products are setwise
subgroup products; normality is always relative to the stated local group.

`FirstFactsOnPath` requests the three forward and three reversed instances
used when the source applies symmetry or shifts the center. `OrbitFacts`
is the output of (4.5.2)--(4.5.3) at the central vertex. These are proof
obligations, not assumptions added to the final source theorem. No constructor
from `Earlier` is asserted here. The early-layer assembly must construct the
path and first facts, then discharge them in the orbit-layer proof.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895--898.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
variable {M : Type*} [Group M] (R : Subgroup M)

/-- The finite source path for (4.5), including its stated outside predecessor.
Existence must be proved using the preceding regular extension and replacement. -/
structure SourcePath (a : Vertex R) where
  first : Vertex R
  last : Vertex R
  walk : (cosetGraph R).Walk first last
  start_color : color R first = false
  length_eq : walk.length = 14
  isPath : walk.IsPath
  center_eq : walk.getVert 4 = a
  critical : ∀ i : ℕ, Even i → i ≤ 6 →
    (cosetGraph R).dist (walk.getVert i) (walk.getVert (i + 8)) = 8 ∧
      ¬ Z R (walk.getVert i) ≤ Q R (walk.getVert (i + 8))
  turns : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 12 →
    ∃ g ∈ stabilizer R (walk.getVert i),
      act R g (walk.getVert (i + 2)) = walk.getVert (i - 2)
  edge_Z_ne : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 12 →
    Z R (walk.getVert (i - 1)) ≠ Z R (walk.getVert (i + 1))
  predecessor : Vertex R
  predecessor_adjacent : Adjacent R first predecessor
  first_edge_Z_ne : Z R predecessor ≠ Z R (walk.getVert 1)

/-- All literal outputs of (4.5.1) for a,c,d,e,f at offsets 0,2,4,6,8
and t at offset 3. This structure does not assert their existence. -/
structure FirstFacts (geometry : Geometry R) (a c d e f t : Vertex R) where
  commutator_eq : ⁅V R a, V R d⁆ = H R a ⊓ H R d
  commutator_card : Nat.card (⁅V R a, V R d⁆ : Subgroup (FreeAmalgam R)) = 2
  intersection_le : V R a ⊓ Q R e ≤ Z R a ⊔ Q R f
  intersection_product_le : (V R a ⊓ Q R e : Set (FreeAmalgam R)) ⊆
    (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))
  B_le : B R a (geometry.Z_normal a) ≤ Q R e
  B_normal : ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a)).Normal
  quotient_centralizer : letI := B_normal
    let π := QuotientGroup.mk' ((B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a))
    ((V R a ⊓ Q R e).subgroupOf (stabilizer R a)).map π =
      ((V R a).subgroupOf (stabilizer R a)).map π ⊓
        centralizer (((Z R f).subgroupOf (stabilizer R a)).map π :
          Set (stabilizer R a ⧸ (B R a (geometry.Z_normal a)).subgroupOf (stabilizer R a)))
  hatW_product : (hatW R a c d : Set (FreeAmalgam R)) * (Q R d : Set (FreeAmalgam R)) =
    (Q R t : Set (FreeAmalgam R))
  H_card : Nat.card (H R a) = 4

/-- The translated and reversed instances needed by the next source calculation.
Every one is an output to prove; none is a new hypothesis of the final theorem. -/
structure FirstFactsOnPath (geometry : Geometry R) {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
    FirstFacts R geometry (p.walk.getVert i) (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 4)) (p.walk.getVert (i + 6))
      (p.walk.getVert (i + 8)) (p.walk.getVert (i + 3))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
    FirstFacts R geometry (p.walk.getVert i) (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 4)) (p.walk.getVert (i - 6))
      (p.walk.getVert (i - 8)) (p.walk.getVert (i - 3))

/-- The remaining local normality, generation and orbit-layer conclusions.
The setwise products retain the literal source factors and their order. -/
structure OrbitFacts {a : Vertex R} (p : SourcePath R a) where
  Z_le_pair : Z R a ≤ stabilizer R (p.walk.getVert 5) ⊓ stabilizer R (p.walk.getVert 6)
  Z_normal_pair : ((Z R a).subgroupOf
    (stabilizer R (p.walk.getVert 5) ⊓ stabilizer R (p.walk.getVert 6))).Normal
  local_generation :
    (((stabilizer R a ⊓ stabilizer R (p.walk.getVert 3)) ⊔ Z R (p.walk.getVert 12)) :
      Set (FreeAmalgam R)) * (C R a : Set (FreeAmalgam R)) =
        (stabilizer R a : Set (FreeAmalgam R))
  hatV_eq : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a
  hatV_product : (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) =
    (Vcirc R a : Set (FreeAmalgam R)) * (Z R a : Set (FreeAmalgam R))
  hatV_commutator : ⁅hatV R a (p.walk.getVert 6), Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)
  hatW_commutator : ⁅hatW R a (p.walk.getVert 6) (p.walk.getVert 8), Q R a⁆ ≤ Z R a

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early
