module

public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Lifts
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Orders

/-!
# The concrete M23 pair-stabilizer image

After diagonal adjustment of the incidence coordinates, the actual pair
stabilizer induces precisely PSL(3,4) extended by its field involution.
Its pointwise-pair subgroup induces precisely PSL(3,4). Certified lifts of
all elementary transvections and of Frobenius prove containment; faithfulness
and the group orders prove equality. Thus the represented group is the
index-three subgroup of PΓL(3,4), with the explicit point and line maps retained.

Source: Aschbacher, *Sporadic Groups*, §18; Aschbacher--Smith,
*The Classification of Quasithin Groups*, §5.2, PDF pp.672–674.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneImage
open Configuration

/-- The final incidence coordinates on complementary points. -/
noncomputable abbrev pointEquiv := adjustedCoordinates.pointEquiv

/-- The final incidence coordinates on derived lines. -/
noncomputable abbrev lineEquiv := adjustedCoordinates.lineEquiv

theorem incident_iff (p : pairComplement x.val) (l : pairLines x.val) :
    pointEquiv p ∈ lineEquiv l ↔ p.val ∈ l.val :=
  adjustedCoordinates.incident_iff p l

/-- The actual pair-stabilizer representation in the adjusted field coordinates. -/
noncomputable abbrev collineation := pairCollineation adjustedCoordinates

theorem collineation_injective : Function.Injective collineation :=
  pairCollineation_injective adjustedCoordinates

@[simp] theorem collineation_point (g : pairStabilizer) (p : pairComplement x.val) :
    Collineation.pointHom PG PG (collineation g) (pointEquiv p) =
      pointEquiv (complementAction x.val g p) := by
  simp [collineation, pointEquiv]

@[simp] theorem collineation_line (g : pairStabilizer) (l : pairLines x.val) :
    Collineation.lineHom PG PG (collineation g) (lineEquiv l) =
      lineEquiv (Sporadic.Mathieu.M23Geometry.lineAction x.val g l) := by
  simp [collineation, lineEquiv]

/-- The pointwise-pair representation, retaining the actual kernel subgroup. -/
noncomputable def pointwiseCollineation : pointwisePairStabilizer →* Collineation PG PG :=
  collineation.comp pointwisePairStabilizer.subtype

theorem pointwiseCollineation_injective : Function.Injective pointwiseCollineation :=
  collineation_injective.comp Subtype.val_injective

/-- The represented pointwise stabilizer is exactly the represented PSL subgroup. -/
theorem pointwise_image_eq : pointwisePairStabilizer.map collineation =
    Matrix.PSL3Four.pslCollineation.range := by
  symm
  apply Subgroup.eq_of_le_of_card_ge psl_range_le_pointwise_image
  rw [Subgroup.card_map_of_injective collineation_injective, pointwisePairStabilizer_card]
  change 20160 ≤ Nat.card (Set.range Matrix.PSL3Four.pslCollineation)
  rw [Nat.card_range_of_injective Matrix.PSL3Four.pslCollineation_injective,
    Matrix.PSL3Four.card_PSL]

/-- Range form of the pointwise-pair image equality. -/
theorem pointwiseCollineation_range : pointwiseCollineation.range =
    Matrix.PSL3Four.pslCollineation.range := by
  rw [pointwiseCollineation, MonoidHom.range_comp, Subgroup.range_subtype]
  exact pointwise_image_eq

private theorem field_range_le : Matrix.PSL3Four.fieldCollineation.range ≤ collineation.range := by
  rintro c ⟨t, rfl⟩
  change ZMod 2 at t
  fin_cases t
  · change Matrix.PSL3Four.fieldCollineation 1 ∈ collineation.range
    rw [map_one]
    exact Subgroup.one_mem _
  · change Matrix.PSL3Four.fieldCollineation (Multiplicative.ofAdd (1 : ZMod 2)) ∈
      collineation.range
    have h : Matrix.PSL3Four.fieldCollineation (Multiplicative.ofAdd (1 : ZMod 2)) =
        Matrix.PSL3Four.frobeniusCollineation :=
      Matrix.PSL3Four.involutionHom_generator _ _
    rw [h]
    exact ⟨frobeniusLift, frobeniusLift_collineation⟩

/-- The field-extension representation is contained in the actual M23 image. -/
theorem fieldExtension_range_le : Matrix.PSL3Four.pairedAction.range ≤ collineation.range := by
  rintro c ⟨g, rfl⟩
  rw [← Matrix.PSL3Four.linear_mul_field g, map_mul,
    Matrix.PSL3Four.pairedAction_linearInclusion,
    Matrix.PSL3Four.pairedAction_fieldInclusion]
  apply Subgroup.mul_mem
  · obtain ⟨h, _, hh⟩ := psl_range_le_pointwise_image ⟨g.left, rfl⟩
    exact ⟨h, hh⟩
  · exact field_range_le ⟨g.right, rfl⟩

/-- The actual pair stabilizer has exactly the desired index-three image. -/
theorem collineation_range : collineation.range = Matrix.PSL3Four.pairedAction.range := by
  symm
  apply Subgroup.eq_of_le_of_card_ge fieldExtension_range_le
  change Nat.card (Set.range collineation) ≤ Nat.card (Set.range Matrix.PSL3Four.pairedAction)
  rw [Nat.card_range_of_injective collineation_injective,
    Nat.card_range_of_injective Matrix.PSL3Four.pairedAction_injective,
    pairStabilizer_card, Matrix.PSL3Four.card_FieldExtension]

end Sporadic.Mathieu.M23Geometry.PairPlaneImage
