module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedAffineIncidence
public import Theory.Combinatorics.TranslationPlane.ProjectiveRecognition
public import Theory.Combinatorics.CollineationAction

/-!
# Projective coordinates for the independent marked A₂ quotient

The proved affine field-line equations extend the transported original
natural-core chart to all points and lines of PG(2,k₁). Conjugating the
actual quotient action by this incidence identification yields a faithful
projective collineation representation. Both full original endpoint maps
fix their literal marked vertices. Source parameters still evaluate through
the supplied endpoint marking; no map from the original ambient completion
to this quotient is used.

The subsequent six-root recognition uses this faithful action. No unknown
group/model equivalence or elementary-root relation is an input here.
Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224.
-/

@[expose] public noncomputable section
open Subgroup Configuration Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace MarkedProjectiveCoordinates
variable {G X : Type*} [Group G] [Group X] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam)
  (h : HypothesisF11 L S)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance markedProjectiveFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)
  (hn₀ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₀.actor : Set (generated L S)))
  (hn₁ : (commonBorel L S).subgroupOf (generated L S) ≤ normalizer (c₁.actor : Set (generated L S)))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hm : RootCoordinates.rotationOrder d = 3) (split : SplitData d.tits) (hcenter : centerIn c₁.actor = ⊥)

/-- Full projective coordinates built from the original source natural action.
Both the point chart and the infinity-line marking are literal. -/
theorem exists_coordinates
    (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d}) :
    ∃ (ep : Point (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁)
      (el : Line (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁),
      el (QuotientPlane.axis d) = TranslationPlane.FieldChart.axis k₁ ∧
      (∀ p m, ep p ∈ el m ↔ p ∈ m) ∧
      ∀ t : Fin 2 → k₁,
        ep (MarkedPlane.affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o t).val =
          TranslationPlane.FieldChart.point k₁ t := by
  let := MarkedPlane.plane d mark h c₀ c₁ hn₀ hn₁ E₀ hm
  exact TranslationPlane.exists_projective_coordinates (QuotientPlane.axis d)
    (MarkedPlane.affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (MarkedPlane.affineChart_line_equation d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)

variable (o : {p : Point (TriangleGeometry.family d) // p ∉ QuotientPlane.axis d})

/-- The chosen coordinates of every independent quotient point. -/
def pointCoordinates : Point (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁ :=
  (exists_coordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).choose

/-- The matching coordinates of every independent quotient line. -/
def lineCoordinates : Line (TriangleGeometry.family d) ≃ TranslationPlane.FieldChart.PG k₁ :=
  (exists_coordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).choose_spec.choose

theorem lineCoordinates_axis :
    lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (QuotientPlane.axis d) =
      TranslationPlane.FieldChart.axis k₁ :=
  (exists_coordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).choose_spec.choose_spec.1

theorem coordinates_incident (p : Point (TriangleGeometry.family d))
    (m : Line (TriangleGeometry.family d)) :
    pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o p ∈
      lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o m ↔ p ∈ m :=
  (exists_coordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).choose_spec.choose_spec.2.1 p m

theorem pointCoordinates_affine (t : Fin 2 → k₁) :
    pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      (MarkedPlane.affineChart d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o t).val =
        TranslationPlane.FieldChart.point k₁ t :=
  (exists_coordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).choose_spec.choose_spec.2.2 t

/-- The projective chart keeps the source core parameter through its literal full-endpoint marking. -/
theorem pointCoordinates_source (t : Fin 2 → k₁) :
    pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o
      ((MarkedCoreTransport.originalCoreEquiv d mark true
        ((A2Source.coreCoordinates c₁ h.generatedLocallyRankOneTriple
          (paired_cores_eq_centers_of_actions h.generatedLocallyRankOneTriple c₀ c₁).2 hcenter E₁).symm
            (.ofAdd t)) : X ⧸ d.D) • o.val) = TranslationPlane.FieldChart.point k₁ t :=
  pointCoordinates_affine d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o t

/-- The same source quotient acts on the native projective plane, by both fibers. -/
def action : X ⧸ d.D →*
    Collineation (TranslationPlane.FieldChart.PG k₁) (TranslationPlane.FieldChart.PG k₁) :=
  (Collineation.transport (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)
    (coordinates_incident d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o)).comp
      (Collineation.ofAction (X ⧸ d.D)
        (Point (TriangleGeometry.family d)) (Line (TriangleGeometry.family d)))

theorem action_point (g : X ⧸ d.D) (p : Point (TriangleGeometry.family d)) :
    Collineation.pointHom _ _ (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o g)
      (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o p) =
        pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (g • p) := by
  simp only [action,MonoidHom.comp_apply,Collineation.transport_point,
    Equiv.symm_apply_apply,Collineation.ofAction_point]

theorem action_line (g : X ⧸ d.D) (m : Line (TriangleGeometry.family d)) :
    Collineation.lineHom _ _ (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o g)
      (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o m) =
        lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (g • m) := by
  simp only [action,MonoidHom.comp_apply,Collineation.transport_line,
    Equiv.symm_apply_apply,Collineation.ofAction_line]

/-- Original overlap faithfulness is retained by this actual projective action. -/
theorem action_injective :
    Function.Injective (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o) := by
  let := MarkedPlane.faithful d mark h
  intro g k he
  apply eq_of_smul_eq_smul (α := Vertex (TriangleGeometry.family d))
  rintro ⟨i,q⟩
  cases i
  · have hh := congrArg (fun a => Collineation.pointHom _ _ a
      (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o ⟨⟨false,q⟩,rfl⟩)) he
    rw [action_point,action_point] at hh
    exact congrArg Subtype.val ((pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).injective hh)
  · have hh := congrArg (fun a => Collineation.lineHom _ _ a
      (lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o ⟨⟨true,q⟩,rfl⟩)) he
    rw [action_line,action_line] at hh
    exact congrArg Subtype.val ((lineCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o).injective hh)

/-- The full original right endpoint fixes the native infinity line. -/
theorem right_fixes_axis (a : parabolic L S 1) :
    Collineation.lineHom _ _
      (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (mark.right a))
        (TranslationPlane.FieldChart.axis k₁) = TranslationPlane.FieldChart.axis k₁ := by
  have hf : (mark.right a : X ⧸ d.D) • QuotientPlane.axis d = QuotientPlane.axis d := by
    apply Subtype.ext
    change (mark.right a : X ⧸ d.D) • CosetGeometry.base (TriangleGeometry.family d) true = _
    apply MulAction.mem_stabilizer_iff.mp
    rw [CosetGeometry.stabilizer_base]
    exact (mark.right a).property
  rw [←lineCoordinates_axis d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o,action_line,hf]

/-- The full original left endpoint fixes the matched point on the infinity line. -/
theorem left_fixes_point (a : parabolic L S 0) :
    Collineation.pointHom _ _
      (action d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (mark.left a))
        (pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (QuotientPlane.centerPoint d)) =
          pointCoordinates d mark h c₀ c₁ hn₀ hn₁ E₀ E₁ hm split hcenter o (QuotientPlane.centerPoint d) := by
  have hf : (mark.left a : X ⧸ d.D) • QuotientPlane.centerPoint d = QuotientPlane.centerPoint d := by
    apply Subtype.ext
    change (mark.left a : X ⧸ d.D) • CosetGeometry.base (TriangleGeometry.family d) false = _
    apply MulAction.mem_stabilizer_iff.mp
    rw [CosetGeometry.stabilizer_base]
    exact (mark.left a).property
  rw [action_point,hf]

end MarkedProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
