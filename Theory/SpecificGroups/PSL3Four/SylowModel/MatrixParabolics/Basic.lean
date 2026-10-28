module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization
public import Theory.SpecificGroups.PSL3Four.FieldExtension.PairedAction

/-!
# Standard parabolic geometry for the matrix field extension

The standard flag consists of the point spanned by `e₀` and the plane spanned
by `e₀,e₁`. In the covector model the latter is represented by `e₂`. We retain
both projective linear stabilizers and their stabilizers in the field extension.
The semilinear stabilizers consist exactly of elements whose linear part lies
in the corresponding projective parabolic, and both contain the coordinate
Sylow subgroup. The root-plane radicals are normal in the previously defined matrix locals,
so their actual quotients are available independently of the geometric
identification and the five-point quotient action.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel.MatrixRealization

open Configuration Projectivization

/-- The point spanned by the first standard basis vector. -/
def standardPoint : PG := mk F ![1, 0, 0] (by simp)

/-- The plane spanned by the first two standard basis vectors, as a covector. -/
def standardPlane : PG := mk F ![0, 0, 1] (by simp)

/-- The first projective parabolic in PSL₃(4). -/
def projectiveParabolic₁ : Subgroup PSL :=
  (MulAction.stabilizer (Equiv.Perm PG) standardPoint).comap
    (Collineation.pointHom PG PG |>.comp pslCollineation)

/-- The second projective parabolic in PSL₃(4). -/
def projectiveParabolic₂ : Subgroup PSL :=
  (MulAction.stabilizer (Equiv.Perm PG) standardPlane).comap
    (Collineation.lineHom PG PG |>.comp pslCollineation)

/-- The point stabilizer in the semilinear field extension. -/
def parabolic₁ : Subgroup FieldExtension :=
  (MulAction.stabilizer (Equiv.Perm PG) standardPoint).comap pointAction

/-- The plane stabilizer in the semilinear field extension. -/
def parabolic₂ : Subgroup FieldExtension :=
  (MulAction.stabilizer (Equiv.Perm PG) standardPlane).comap lineAction

/-- The standard flag stabilizer, without any assertion that it is a Sylow group. -/
def flagIntersection : Subgroup FieldExtension := parabolic₁ ⊓ parabolic₂

@[simp] theorem mem_parabolic₁ (g : FieldExtension) :
    g ∈ parabolic₁ ↔ pointAction g standardPoint = standardPoint := Iff.rfl

@[simp] theorem mem_parabolic₂ (g : FieldExtension) :
    g ∈ parabolic₂ ↔ lineAction g standardPlane = standardPlane := Iff.rfl

@[simp] theorem mem_flagIntersection (g : FieldExtension) :
    g ∈ flagIntersection ↔
      pointAction g standardPoint = standardPoint ∧
        lineAction g standardPlane = standardPlane := Iff.rfl

theorem standardPoint_incident_standardPlane : standardPoint ∈ standardPlane := by
  simp [standardPoint, standardPlane, Configuration.ofField.mem_iff,
    Projectivization.orthogonal_mk, dotProduct, Fin.sum_univ_three]

theorem parabolic₁_comap_linearInclusion :
    parabolic₁.comap linearInclusion = projectiveParabolic₁ := by
  ext g
  change Collineation.pointHom PG PG (pairedAction (linearInclusion g)) standardPoint =
      standardPoint ↔ Collineation.pointHom PG PG (pslCollineation g) standardPoint =
      standardPoint
  rw [pairedAction_linearInclusion]

theorem parabolic₂_comap_linearInclusion :
    parabolic₂.comap linearInclusion = projectiveParabolic₂ := by
  ext g
  change Collineation.lineHom PG PG (pairedAction (linearInclusion g)) standardPlane =
      standardPlane ↔ Collineation.lineHom PG PG (pslCollineation g) standardPlane =
      standardPlane
  rw [pairedAction_linearInclusion]

theorem rootPlane₁_le_local₁ : rootPlane₁ ≤ local₁ := Subgroup.le_normalizer
theorem rootPlane₂_le_local₂ : rootPlane₂ ≤ local₂ := Subgroup.le_normalizer

instance rootPlane₁_normal_local₁ : (rootPlane₁.subgroupOf local₁).Normal :=
  Subgroup.normal_in_normalizer

instance rootPlane₂_normal_local₂ : (rootPlane₂.subgroupOf local₂).Normal :=
  Subgroup.normal_in_normalizer

theorem card_rootPlane₁ : Nat.card rootPlane₁ = 16 := by
  exact (Nat.card_congr (markedEquiv V₁).toEquiv).symm.trans card_V₁

theorem card_rootPlane₂ : Nat.card rootPlane₂ = 16 := by
  exact (Nat.card_congr (markedEquiv V₂).toEquiv).symm.trans card_V₂

theorem card_rootPlane₁_subgroupOf_local₁ :
    Nat.card (rootPlane₁.subgroupOf local₁) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootPlane₁_le_local₁).toEquiv,
    card_rootPlane₁]

theorem card_rootPlane₂_subgroupOf_local₂ :
    Nat.card (rootPlane₂.subgroupOf local₂) = 16 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe rootPlane₂_le_local₂).toEquiv,
    card_rootPlane₂]

/-- The actual first local quotient by its root plane. -/
abbrev LocalQuotient₁ := local₁ ⧸ rootPlane₁.subgroupOf local₁
/-- The actual second local quotient by its root plane. -/
abbrev LocalQuotient₂ := local₂ ⧸ rootPlane₂.subgroupOf local₂

theorem sylow_le_localIntersection :
    (sylow : Subgroup FieldExtension) ≤ local₁ ⊓ local₂ :=
  le_inf sylow_le_local₁ sylow_le_local₂


@[simp] theorem frobenius_standardPoint : projectiveFrobenius standardPoint = standardPoint := by
  rw [standardPoint, projectiveFrobenius_mk]
  congr 1
  ext i
  fin_cases i <;> simp

@[simp] theorem frobenius_standardPlane : projectiveFrobenius standardPlane = standardPlane := by
  rw [standardPlane, projectiveFrobenius_mk]
  congr 1
  ext i
  fin_cases i <;> simp

@[simp] theorem fieldCollineation_standardPoint (t : C2) :
    Collineation.pointHom PG PG (fieldCollineation t) standardPoint = standardPoint := by
  rcases c2_cases t with rfl | rfl
  · simp
  · rw [show τ = Multiplicative.ofAdd (1 : ZMod 2) from rfl,
      fieldCollineation_generator, frobeniusCollineation_point, frobenius_standardPoint]

@[simp] theorem fieldCollineation_standardPlane (t : C2) :
    Collineation.lineHom PG PG (fieldCollineation t) standardPlane = standardPlane := by
  rcases c2_cases t with rfl | rfl
  · simp
  · rw [show τ = Multiplicative.ofAdd (1 : ZMod 2) from rfl,
      fieldCollineation_generator, frobeniusCollineation_line, frobenius_standardPlane]

/-- The point stabilizer is exactly the extension of the projective parabolic
by the whole field complement. -/
theorem mem_parabolic₁_iff_left (g : FieldExtension) :
    g ∈ parabolic₁ ↔ g.left ∈ projectiveParabolic₁ := by
  change Collineation.pointHom PG PG
    (pslCollineation g.left * fieldCollineation g.right) standardPoint = _ ↔ _
  rw [map_mul, Equiv.Perm.mul_apply, fieldCollineation_standardPoint]
  rfl

theorem mem_parabolic₂_iff_left (g : FieldExtension) :
    g ∈ parabolic₂ ↔ g.left ∈ projectiveParabolic₂ := by
  change Collineation.lineHom PG PG
    (pslCollineation g.left * fieldCollineation g.right) standardPlane = _ ↔ _
  rw [map_mul, Equiv.Perm.mul_apply, fieldCollineation_standardPlane]
  rfl

theorem projective_mem_parabolic₁ (a : U) : projective a ∈ projectiveParabolic₁ := by
  change specialLinear a • standardPoint = standardPoint
  rw [standardPoint, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  change (1 : Fˣ) • (![1,0,0] : Fin 3 → F) = matrix a *ᵥ ![1,0,0]
  ext i
  fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem projective_mem_parabolic₂ (a : U) : projective a ∈ projectiveParabolic₂ := by
  change SpecialLinearGroup.inverseTranspose (specialLinear a) • standardPlane = standardPlane
  rw [standardPlane, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  change (1 : Fˣ) • (![0,0,1] : Fin 3 → F) =
    ((specialLinear a)⁻¹.val.transpose) *ᵥ ![0,0,1]
  rw [← map_inv]
  change (1 : Fˣ) • (![0,0,1] : Fin 3 → F) = (matrix a⁻¹).transpose *ᵥ ![0,0,1]
  ext i
  fin_cases i <;> simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem sylow_le_parabolic₁ : (sylow : Subgroup FieldExtension) ≤ parabolic₁ := by
  rintro g ⟨a, rfl⟩
  exact (mem_parabolic₁_iff_left _).mpr (projective_mem_parabolic₁ a.left)

theorem sylow_le_parabolic₂ : (sylow : Subgroup FieldExtension) ≤ parabolic₂ := by
  rintro g ⟨a, rfl⟩
  exact (mem_parabolic₂_iff_left _).mpr (projective_mem_parabolic₂ a.left)

theorem sylow_le_flagIntersection : (sylow : Subgroup FieldExtension) ≤ flagIntersection :=
  le_inf sylow_le_parabolic₁ sylow_le_parabolic₂

end Matrix.PSL3Four.SylowModel.MatrixRealization
