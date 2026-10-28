module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.OriginalCoordinates
public import Theory.Combinatorics.TranslationPlane.ProjectiveRecognition
public import Theory.Combinatorics.CollineationAction

/-!
# Projective coordinates of the original centerfree A₂ source quotient

The proved one-field affine line equations give an incidence equivalence
with the actual projectivization PG(2,k₁), including every point at infinity.
The original infinity line is z=0 and the original core chart is [x:y:1].
Conjugating the literal quotient action by these coordinates gives a faithful
collineation representation, with its full point and line actions retained.

This removes projective-plane recognition as an extra premise. It does not
identify the entire collineation group with PSL₃ or assert that the six root
relations and generation have already been established. The field, original
natural actor, m=3 and centerfree hypotheses remain the genuine earlier
source inputs of DGS 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace ProjectiveCoordinates
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

/-- Full projective coordinates built from the original source natural action.
Both the point chart and the infinity-line marking are literal. -/
theorem exists_coordinates
    (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d}) :
    ∃ (ep : Point (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁)
      (el : Line (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁),
      el (QuotientPlane.axis d) = TranslationPlane.FieldChart.axis k₁ ∧
      (∀ p m, ep p ∈ el m ↔ p ∈ m) ∧
      ∀ t : Fin 2 → k₁,
        ep (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val =
          TranslationPlane.FieldChart.point k₁ t := by
  let := OriginalCoordinates.plane h d c₀ c₁ hn₀ hn₁ E₀ hm
  exact TranslationPlane.exists_projective_coordinates (QuotientPlane.axis d)
    (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
    (OriginalCoordinates.affineChart_line_equation h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)

variable (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})

/-- The chosen coordinates of every original quotient point. -/
def pointCoordinates : Point (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁ :=
  (exists_coordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).choose

/-- The matching coordinates of every original quotient line. -/
def lineCoordinates : Line (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁ :=
  (exists_coordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).choose_spec.choose

theorem lineCoordinates_axis :
    lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (QuotientPlane.axis d) =
      TranslationPlane.FieldChart.axis k₁ :=
  (exists_coordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).choose_spec.choose_spec.1

theorem coordinates_incident (p : Point (TriangleGeometry.family d))
    (m : Line (TriangleGeometry.family d)) :
    pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o p ∈
      lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o m ↔ p ∈ m :=
  (exists_coordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).choose_spec.choose_spec.2.1 p m

theorem pointCoordinates_affine (t : Fin 2 → k₁) :
    pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (OriginalCoordinates.affineChart h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t).val =
        TranslationPlane.FieldChart.point k₁ t :=
  (exists_coordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).choose_spec.choose_spec.2.2 t

/-- Native point coordinates retain the same original-core quotient map. -/
theorem pointCoordinates_source (t : Fin 2 → k₁) :
    pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o
      (d.q ((OriginalCoordinates.coreCoordinates h c₀ c₁ E₁ hcenter).symm (.ofAdd t) :
        generated L S) • o.val) = TranslationPlane.FieldChart.point k₁ t :=
  pointCoordinates_affine h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o t

/-- The same source quotient acts on the native projective plane, by both fibers. -/
def action : (generated L S) ⧸ d.D →*
    Collineation (TranslationPlane.FieldChart.PG k₁) (TranslationPlane.FieldChart.PG k₁) :=
  (Collineation.transport (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
    (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)
    (coordinates_incident h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o)).comp
      (Collineation.ofAction ((generated L S) ⧸ d.D)
        (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)))

theorem action_point (g : (generated L S) ⧸ d.D) (p : Point (TriangleGeometry.family d)) :
    Collineation.pointHom _ _ (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o g)
      (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o p) =
        pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (g • p) := by
  simp only [action,MonoidHom.comp_apply,Collineation.transport_point,
    Equiv.symm_apply_apply,Collineation.ofAction_point]

theorem action_line (g : (generated L S) ⧸ d.D) (m : Line (TriangleGeometry.family d)) :
    Collineation.lineHom _ _ (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o g)
      (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o m) =
        lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (g • m) := by
  simp only [action,MonoidHom.comp_apply,Collineation.transport_line,
    Equiv.symm_apply_apply,Collineation.ofAction_line]

/-- Original overlap faithfulness is retained by this actual projective action. -/
theorem action_injective :
    Function.Injective (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o) := by
  let := QuotientPlane.faithful d h.generatedLocallyRankOneTriple
  intro g k he
  apply eq_of_smul_eq_smul (α := Vertex (TriangleGeometry.family d))
  rintro ⟨i,q⟩
  cases i
  · have hh := congrArg (fun a => Collineation.pointHom _ _ a
      (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o ⟨⟨false,q⟩,rfl⟩)) he
    rw [action_point,action_point] at hh
    exact congrArg Subtype.val ((pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).injective hh)
  · have hh := congrArg (fun a => Collineation.lineHom _ _ a
      (lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o ⟨⟨true,q⟩,rfl⟩)) he
    rw [action_line,action_line] at hh
    exact congrArg Subtype.val ((lineCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o).injective hh)

/-- The full original right endpoint fixes the native infinity line. -/
theorem right_fixes_axis (a : parabolic L S 1) :
    Collineation.lineHom _ _
      (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o ((originalMarkedIso d).right a))
        (TranslationPlane.FieldChart.axis k₁) = TranslationPlane.FieldChart.axis k₁ := by
  rw [←lineCoordinates_axis h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o,
    action_line,OriginalCoordinates.right_fixes_axis]

/-- The full original left endpoint fixes the matched point on the infinity line. -/
theorem left_fixes_point (a : parabolic L S 0) :
    Collineation.pointHom _ _
      (action h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o ((originalMarkedIso d).left a))
        (pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (QuotientPlane.centerPoint d)) =
          pointCoordinates h d c₀ c₁ hn₀ hn₁ E₀ E₁ hm hcenter o (QuotientPlane.centerPoint d) := by
  rw [action_point,OriginalCoordinates.left_fixes_point]

end ProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
