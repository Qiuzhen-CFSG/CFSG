module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.QuotientPlane
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# Literal original-source application of the A₂ affine chart

The genuine F.1.1 hypotheses supply the faithful local triple on the
original generated carrier. Its marked quotient and its original natural
actors therefore instantiate the quotient plane and its one-field line
equations. Evaluations use the same quotient map as originalMarkedIso;
both full endpoint groups fix their original marked vertices.

This discharges the metric and affine-coordinate premises on this source
quotient. It does not yet construct six compatible roots or apply the
Steinberg presentation. The independent universal/geometric marking still
requires its local natural-action transport.

Source: DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224;
Aschbacher–Smith F.1.9 and F.1.11.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace OriginalCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S) (d : SourceQuotient L S)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (hcenter : centerIn c₁.actor = ⊥)

/-- The projective plane on the original quotient's two full parabolic fibers. -/
@[instance_reducible] def plane :
    ProjectivePlane (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)) :=
  QuotientPlane.plane d h.generatedLocallyRankOneTriple c₀ c₁ hn₀ hn₁ E₀ hm

/-- The exact original-core coordinate equivalence, before projection to the finite quotient. -/
def coreCoordinates : Q (fullFamily L S) (base (fullFamily L S) true) ≃*
    Multiplicative (Fin 2 → k₁) :=
  A2Source.coreCoordinates c₁ h.generatedLocallyRankOneTriple
    (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁

/-- A single-field affine chart on the actual original-source quotient. -/
def affineChart (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d}) :
    (Fin 2 → k₁) ≃ {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d} :=
  QuotientPlane.affineChart d h.generatedLocallyRankOneTriple c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o

/-- Affine coordinates retain the literal original quotient evaluation. -/
theorem affineChart_apply
    (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d}) (t : Fin 2 → k₁) :
    (affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val =
      d.q ((coreCoordinates h c₀ c₁ E₁ hcenter).symm (.ofAdd t) : generated L S) • o.val := rfl

/-- Every affine source-quotient line has an ordinary equation in this one field. -/
theorem affineChart_line_equation
    (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})
    (m : Line (TriangleGeometry.family d)) (hml : m ≠ QuotientPlane.axis d) :
    ∃ b v : Fin 2 → k₁, v ≠ 0 ∧ ∀ t : Fin 2 → k₁,
      (affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val ∈ m ↔
        ∃ r : k₁, t = b + r • v :=
  QuotientPlane.affineChart_line_equation d h.generatedLocallyRankOneTriple
    c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o m hml

include h c₀ c₁ hn₀ hn₁ E₀ hm in
/-- An affine origin exists; choosing it introduces no extra source premise. -/
theorem exists_affine_origin :
    Nonempty {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d} := by
  let := plane h d c₀ c₁ hn₀ hn₁ E₀ hm
  apply (Nat.card_pos_iff.mp ?_).1
  rw [card_affinePoints,QuotientPlane.plane_order d h.generatedLocallyRankOneTriple c₀ c₁ hn₀ hn₁ E₀ hm]
  exact pow_pos Nat.card_pos 2

/-- The full first original endpoint fixes the original marked point under originalMarkedIso. -/
theorem left_fixes_point (a : parabolic L S 0) :
    ((originalMarkedIso d).left a : (generated L S) ⧸ d.D) • QuotientPlane.centerPoint d =
      QuotientPlane.centerPoint d := by
  apply Subtype.ext
  change ((originalMarkedIso d).left a : (generated L S) ⧸ d.D) • base (TriangleGeometry.family d) false = _
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact ((originalMarkedIso d).left a).property

/-- The full second original endpoint fixes the original marked line under the same marking. -/
theorem right_fixes_axis (a : parabolic L S 1) :
    ((originalMarkedIso d).right a : (generated L S) ⧸ d.D) • QuotientPlane.axis d =
      QuotientPlane.axis d := by
  apply Subtype.ext
  change ((originalMarkedIso d).right a : (generated L S) ⧸ d.D) • base (TriangleGeometry.family d) true = _
  apply MulAction.mem_stabilizer_iff.mp
  rw [CosetGeometry.stabilizer_base]
  exact ((originalMarkedIso d).right a).property

end OriginalCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
