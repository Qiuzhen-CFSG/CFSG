module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.PlaneRecognition.Geometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.PlaneRecognition.LocalGroups
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.FivePointQuotients.Action
public import Theory.GroupAction.RankTwoCosetGeometry.Valence

/-!
# Projective coordinates on the native completion graph

The model's false cosets are identified with projective points, and its true
cosets with line covectors. The coset maps send a representative to its action
on the standard point or line. The literal parabolics fix these coordinates;
transitivity and the existing native orders make both maps bijections.

Common representatives preserve incidence. Each coset pencil and each native
projective pencil has five members, so this inclusion is an equality. The
coordinate identifications preserve the actual PSL point action and the
inverse-transpose line action, including their projective quotient conventions.

Source: the PSL₃(4) model of Aschbacher–Smith F.4.8 and F.4.26,
printed pp.278 and 288.
-/

public section

namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
noncomputable section
open Configuration Projectivization Subgroup.CosetGeometry
open Matrix.PSL3Four Matrix.PSL3Four.SylowModel.MatrixRealization
open Matrix.PSL3.LinearThree
open scoped Matrix
local instance : DecidableEq F := Classical.decEq _

private def coordinateAction (i : Bool) : PSL →* Equiv.Perm PG :=
  (bif i then Collineation.lineHom PG PG else Collineation.pointHom PG PG).comp pslCollineation

private def baseCoordinate (i : Bool) : PG := bif i then standardPlane else standardPoint

private theorem coordinateAction_fixes {i : Bool} {g : PSL} (hg : g ∈ modelCompletion.family i) :
    coordinateAction i g (baseCoordinate i) = baseCoordinate i := by
  cases i
  · have hl : g ∈ pointLocal F := by
      have he : pointParabolic F = pointLocal F :=
        Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local true
      rw [Completion.family_false, model_left_range] at hg
      exact he ▸ hg
    obtain ⟨A, hA, rfl⟩ := hl
    change A • standardPoint = standardPoint
    have hAv : A • (![1, 0, 0] : Fin 3 → F) = ![1, 0, 0] := hA
    simp only [standardPoint, smul_mk, hAv]
  · have hl : g ∈ lineLocal F := by
      have he : lineParabolic F = lineLocal F :=
        Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local false
      rw [Completion.family_true, model_right_range] at hg
      exact he ▸ hg
    obtain ⟨A, hA, rfl⟩ := hl
    change Matrix.SpecialLinearGroup.inverseTranspose A • standardPlane = standardPlane
    rw [standardPlane, smul_mk]
    congr 1
    have h := (mem_lineLocalSL_iff F A⁻¹).mp ((lineLocalSL F).inv_mem hA)
    change A⁻¹.val.transpose *ᵥ ![0, 0, 1] = ![0, 0, 1]
    ext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h.1
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h.2.1
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h.2.2

private theorem coordinateAction_transitive (i : Bool) (p : PG) :
    ∃ g : PSL, coordinateAction i g (baseCoordinate i) = p := by
  cases i
  · obtain ⟨A, hA⟩ := MulAction.exists_smul_eq SL standardPoint p
    exact ⟨(A : PSL), hA⟩
  · obtain ⟨A, hA⟩ := MulAction.exists_smul_eq SL standardPlane p
    refine ⟨((A.transpose)⁻¹ : PSL), ?_⟩
    change Matrix.SpecialLinearGroup.inverseTranspose (A.transpose)⁻¹ • standardPlane = p
    have h : Matrix.SpecialLinearGroup.inverseTranspose (A.transpose)⁻¹ = A := by
      change (((A.transpose)⁻¹)⁻¹).transpose = A
      rw [inv_inv]
      rfl
    rwa [h]

private def cosetCoordinate (i : Bool) : (PSL ⧸ modelCompletion.family i) → PG :=
  Quotient.lift (fun g => coordinateAction i g (baseCoordinate i)) (by
    intro g h hgh
    have hfix := coordinateAction_fixes (QuotientGroup.leftRel_apply.mp hgh)
    calc
      coordinateAction i g (baseCoordinate i) =
          coordinateAction i g (coordinateAction i (g⁻¹ * h) (baseCoordinate i)) :=
        congrArg (coordinateAction i g) hfix.symm
      _ = coordinateAction i h (baseCoordinate i) := by
        rw [map_mul, map_inv]
        simp only [Equiv.Perm.mul_apply]
        exact (coordinateAction i g).apply_symm_apply _)

private theorem cosetCoordinate_surjective (i : Bool) :
    Function.Surjective (cosetCoordinate i) := by
  intro p
  obtain ⟨g, hg⟩ := coordinateAction_transitive i p
  exact ⟨g, hg⟩

private theorem card_model_coset (i : Bool) : Nat.card (PSL ⧸ modelCompletion.family i) = 21 := by
  have hc : Nat.card (modelCompletion.family i) = 960 := by
    cases i
    · exact modelCompletion.left_card_eq
    · exact modelCompletion.right_card_eq
  have h := (modelCompletion.family i).card_mul_index
  rw [hc, card_PSL, Subgroup.index_eq_card] at h
  omega

private def cosetCoordinateEquiv (i : Bool) : (PSL ⧸ modelCompletion.family i) ≃ PG :=
  Equiv.ofBijective (cosetCoordinate i)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨cosetCoordinate_surjective i, (card_model_coset i).trans card_projectivePlane.symm⟩)

/-- The literal model cosets identified with projective points or line covectors. -/
def modelCoordinates (i : Bool) : RankTwo.Fiber modelCompletion.family i ≃ PG :=
  (RankTwo.fiberEquivQuotient modelCompletion.family i).trans (cosetCoordinateEquiv i)

private theorem modelCoordinates_base (i : Bool) :
    modelCoordinates i ⟨RankTwo.base modelCompletion.family i, rfl⟩ = baseCoordinate i := by
  change coordinateAction i 1 (baseCoordinate i) = _
  rw [map_one]
  rfl

private theorem modelCoordinates_smul (i : Bool) (g : PSL)
    (v : RankTwo.Fiber modelCompletion.family i) :
    modelCoordinates i (g • v) = coordinateAction i g (modelCoordinates i v) := by
  rcases v with ⟨⟨j, v⟩, h⟩
  dsimp only at h
  subst j
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective v
  change coordinateAction i (g * a) (baseCoordinate i) =
    coordinateAction i g (coordinateAction i a (baseCoordinate i))
  rw [map_mul]
  rfl

/-- Natural projective point equivariance, for the actual PSL element. -/
theorem modelCoordinates_point_smul (g : PSL) (p : modelCompletion.Point) :
    modelCoordinates false (g • p) = g • modelCoordinates false p := by
  rw [modelCoordinates_smul]
  exact pslCollineation_point g _

/-- Lines are covectors, so their determinant-one action is inverse transpose. -/
theorem modelCoordinates_line_smul (A : SL) (l : modelCompletion.Line) :
    modelCoordinates true ((A : PSL) • l) =
      Matrix.SpecialLinearGroup.inverseTranspose A • modelCoordinates true l :=
  modelCoordinates_smul true (A : PSL) l

/-- Equivariance on lines for every projective group element. -/
theorem modelCoordinates_line_action (g : PSL) (l : modelCompletion.Line) :
    modelCoordinates true (g • l) =
      Collineation.lineHom PG PG (pslCollineation g) (modelCoordinates true l) :=
  modelCoordinates_smul true g l

private theorem coordinates_incident {p : modelCompletion.Point} {l : modelCompletion.Line}
    (h : p ∈ l) : modelCoordinates false p ∈ modelCoordinates true l := by
  obtain ⟨g, hp, hl⟩ := RankTwo.incident_common_translate modelCompletion.family h.2
  rw [p.property] at hp
  rw [l.property] at hl
  have hp' : p = g • (⟨RankTwo.base modelCompletion.family false, rfl⟩ : modelCompletion.Point) :=
    Subtype.ext hp.symm
  have hl' : l = g • (⟨RankTwo.base modelCompletion.family true, rfl⟩ : modelCompletion.Line) :=
    Subtype.ext hl.symm
  rw [hp', hl', modelCoordinates_smul, modelCoordinates_smul,
    modelCoordinates_base, modelCoordinates_base]
  exact (Collineation.mem_iff (pslCollineation g) standardPoint standardPlane).mpr
    standardPoint_incident_standardPlane

private theorem card_model_neighbor_base (i : Bool) :
    Nat.card (modelCompletion.graph.neighborSet (RankTwo.base modelCompletion.family i)) = 5 := by
  rw [RankTwo.card_neighbor_base]
  have hP : Nat.card (modelCompletion.family i) = 960 := by
    cases i
    · exact modelCompletion.left_card_eq
    · exact modelCompletion.right_card_eq
  have hi : modelCompletion.family i ⊓ modelCompletion.family (!i) =
      modelCompletion.middle.range := by
    cases i
    · exact model_overlap
    · simpa only [Completion.family_false, Completion.family_true, Bool.not_true, inf_comm] using model_overlap
  have hI : Nat.card ((modelCompletion.family (!i)).subgroupOf (modelCompletion.family i)) = 192 := by
    rw [← Subgroup.inf_subgroupOf_left, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show modelCompletion.family i ⊓ modelCompletion.family (!i) ≤
        modelCompletion.family i from inf_le_left)).toEquiv, hi]
    exact modelCompletion.middle_card
  have h := ((modelCompletion.family (!i)).subgroupOf (modelCompletion.family i)).card_mul_index
  rw [hP, hI] at h
  omega

theorem model_neighbor_card (v : modelCompletion.Vertex) :
    Nat.card (modelCompletion.graph.neighborSet v) = 5 := by
  obtain ⟨g, hg⟩ := exists_smul_base modelCompletion.family v
  have hc := Nat.card_congr ((translationGraphIso modelCompletion.family g).mapNeighborSet
    (RankTwo.base modelCompletion.family v.type))
  exact (show Nat.card (modelCompletion.graph.neighborSet v) =
    Nat.card (modelCompletion.graph.neighborSet (RankTwo.base modelCompletion.family v.type)) by
      simpa only [translationGraphIso_apply, hg] using hc.symm).trans (card_model_neighbor_base v.type)

/-- Both directions of incidence for the actual model's two coset spaces. -/
theorem modelCoordinates_incidence (p : modelCompletion.Point) (l : modelCompletion.Line) :
    modelCoordinates false p ∈ modelCoordinates true l ↔ p ∈ l := by
  let f : {m : modelCompletion.Line // p ∈ m} → {m : PG // modelCoordinates false p ∈ m} :=
    fun m => ⟨modelCoordinates true m.val, coordinates_incident m.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext ((modelCoordinates true).injective (congrArg Subtype.val hab))
  have hc : Nat.card {m : modelCompletion.Line // p ∈ m} =
      Nat.card {m : PG // modelCoordinates false p ∈ m} := by
    rw [Nat.card_congr (RankTwo.linesOnPointEquivNeighbors modelCompletion.family p),
      model_neighbor_card]
    change 5 = lineCount PG (modelCoordinates false p)
    rw [ProjectivePlane.lineCount_eq, order_projectivePlane]
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2
  refine ⟨fun h => ?_, coordinates_incident⟩
  obtain ⟨m, hm⟩ := hs ⟨modelCoordinates true l, h⟩
  have he := (modelCoordinates true).injective (congrArg Subtype.val hm)
  exact he ▸ m.property

end
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
