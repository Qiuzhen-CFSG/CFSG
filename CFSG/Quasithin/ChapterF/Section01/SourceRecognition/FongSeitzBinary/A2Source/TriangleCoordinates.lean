module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.SourcePlane

/-!
# The one-field chart on a literal source triangle

Short-geodesic uniqueness, diameter three and valence q+1 construct the
projective plane on the actual marked parabolic cosets. The centerfree natural
core then gives the affine chart and all line-coset incidence equations.

The graph hypotheses here still need to be established for the same m=3
marked BN quotient, and its earlier natural actor needs to be transported
through the original endpoint marking. This module does not assert that
those two source obligations, or six-root recognition, have been discharged.

Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2
variable (h : LocallyRankOneTriple P B)
  (c : BOneActionData (family P) (base (family P) true) (base (family P) false) k W)
  (hcore : Q (family P) (base (family P) true) = Z (family P) (base (family P) true))
  (hcenter : centerIn c.actor = ⊥)
  (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
  (hu : (graph (family P)).UniqueGeodesicsBelow 3)
  (hd : ∀ v w, (graph (family P)).dist v w ≤ 3)
  (hv : ∀ v, Nat.card ((graph (family P)).neighborSet v) = Nat.card k + 1)

/-- The plane uses the actual two coset fibers and their original incidence. -/
@[instance_reducible] def trianglePlane : ProjectivePlane (Point (family P)) (Line (family P)) :=
  projectivePlaneOfGeometry (family P) h.generate hu hd (Nat.card k) Finite.one_lt_card hv

omit [CharP k 2] in
/-- The graph valence retains exactly the field from the one natural core. -/
theorem trianglePlane_order :
    letI := trianglePlane h hu hd hv
    ProjectivePlane.order (Point (family P)) (Line (family P)) = Nat.card k := by
  let := trianglePlane h hu hd hv
  have hc : pointCount (Point (family P)) (sourceAxis P) = Nat.card k + 1 :=
    (Nat.card_congr (pointsOnLineEquivNeighbors (family P) (sourceAxis P))).trans
      (hv (sourceAxis P).val)
  rw [ProjectivePlane.pointCount_eq] at hc
  omega

variable (o : {p : Point (family P) // p ∉ sourceAxis P})

/-- An actual affine coordinate equivalence from short-path geometry and the natural core. -/
def triangleAffineChart : (Fin 2 → k) ≃ {p : Point (family P) // p ∉ sourceAxis P} :=
  letI := trianglePlane h hu hd hv
  sourceAffineChart h c hcore hcenter E (trianglePlane_order h hu hd hv) o

/-- Coordinates are evaluated by the original source core in the original point action. -/
theorem triangleAffineChart_apply (t : Fin 2 → k) :
    (triangleAffineChart h c hcore hcenter E hu hd hv o t).val =
      ((coreCoordinates c h hcore hcenter E).symm (.ofAdd t) : G) • o.val := rfl

/-- Every affine line is a coset of a conjugate of the one marked Sylow fixed line. -/
theorem triangleAffineChart_all_affine_lines
    (hn : B ≤ normalizer (c.actor : Set G)) (m : Line (family P)) (hml : m ≠ sourceAxis P) :
    ∃ b : Fin 2 → k, ∃ a : c.actor, ∀ t : Fin 2 → k,
      (triangleAffineChart h c hcore hcenter E hu hd hv o
        (Matrix.mulVec (c.quotient a).val t + b)).val ∈ m ↔
      ∀ s ∈ (c.imageSylow : Subgroup SL(2,k)), Matrix.mulVec s.val t = t := by
  let := trianglePlane h hu hd hv
  exact sourceAffineChart_all_affine_lines h c hcore hcenter E
    (trianglePlane_order h hu hd hv) o hn m hml
/-- Direct affine field-line equations on the literal source triangle. -/
theorem triangleAffineChart_line_equation
    (hn : B ≤ normalizer (c.actor : Set G)) (m : Line (family P)) (hm : m ≠ sourceAxis P) :
    ∃ b d : Fin 2 → k, d ≠ 0 ∧ ∀ t : Fin 2 → k,
      (triangleAffineChart h c hcore hcenter E hu hd hv o t).val ∈ m ↔
        ∃ r : k, t = b + r • d := by
  let := trianglePlane h hu hd hv
  exact sourceAffineChart_line_equation h c hcore hcenter E
    (trianglePlane_order h hu hd hv) o hn m hm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
