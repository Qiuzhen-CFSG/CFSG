module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Statements

/-!
# Remaining calculation outputs for the first source lemma

The kernel calculation is (4.5.1)(ii)--(iii), on the actual local quotient.
The layer calculation is the setwise product in (iv) and the lower bound in
(v). The upper bound and clause (i) are proved separately. These records are
outputs still to construct, not additional assumptions of the source theorem.
Both calculation families may be proved for an explicit SourcePath while its
existence is constructed independently; First retains their final assembly.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.896.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First
variable {M : Type*} [Group M] (R : Subgroup M)

/-- The literal kernel and quotient outputs, without either cardinality claim. -/
structure KernelCalculation (geometry : Geometry R) (a e f : Vertex R) : Prop where
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

/-- Every translated and reversed kernel calculation used in the next source lemma. -/
structure KernelFactsOnPath (geometry : Geometry R) {a : Vertex R}
    (p : SourcePath R a) : Prop where
  forward : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
    KernelCalculation R geometry (p.walk.getVert i) (p.walk.getVert (i + 6))
      (p.walk.getVert (i + 8))
  backward : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
    KernelCalculation R geometry (p.walk.getVert i) (p.walk.getVert (i - 6))
      (p.walk.getVert (i - 8))

/-- The second orbit layer's product and the missing lower bound for H.
The cardinality transport to other M-vertices already exists in Initial.Bounds. -/
structure LayerFactsOnPath {a : Vertex R} (p : SourcePath R a) : Prop where
  forward_product : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 6 →
    (hatW R (p.walk.getVert i) (p.walk.getVert (i + 2)) (p.walk.getVert (i + 4)) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert (i + 4)) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert (i + 3)) : Set (FreeAmalgam R))
  backward_product : ∀ i : ℕ, Even i → 8 ≤ i → i ≤ 12 →
    (hatW R (p.walk.getVert i) (p.walk.getVert (i - 2)) (p.walk.getVert (i - 4)) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert (i - 4)) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert (i - 3)) : Set (FreeAmalgam R))
  H_card_lower : ∀ v, color R v = false → 4 ≤ Nat.card (H R v)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.First
