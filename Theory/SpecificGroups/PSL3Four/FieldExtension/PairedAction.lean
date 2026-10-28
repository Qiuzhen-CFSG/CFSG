module

public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.Combinatorics.ProjectivePlaneMatrixAction
/-!
# Faithful paired action of the field extension of PSL(3,4)

The determinant-one matrix action descends through the scalar center to a
collineation action of PSL(3,4). Coordinate Frobenius preserves orthogonality
and conjugates this action by the field automorphism. These two actions give
the paired point and line representation of `FieldExtension`.

Faithfulness uses four points: two coordinate points, their sum, and a point
whose coordinate is not fixed by Frobenius. A linear map inducing Frobenius
would scale the first two coordinate vectors by the same factor, forcing that
last coordinate to be fixed. Thus the field involution lies outside the
projective linear image. The point action is faithful, and incidence duality
gives faithfulness of the line action as well.

Source: Aschbacher, *Sporadic Groups*, §18, especially 18.7–18.9.
-/

public section

open Configuration Projectivization
namespace Matrix.PSL3Four
noncomputable section

/-- The paired projective action descended from determinant-one matrices. -/
@[expose] def pslCollineation : PSL →* Collineation PG PG :=
  QuotientGroup.lift _ Configuration.specialLinearCollineation (by
    classical
    intro A hA
    apply Collineation.ext_points
    intro p
    have h : MulAction.toPermHom SL PG A = 1 := by
      exact (show A ∈ (MulAction.toPermHom SL PG).ker from
        (Projectivization.SL_mulAction_ker (ι := Fin 3) (K := F)).symm ▸ hA)
    exact Equiv.congr_fun h p)

@[simp] theorem pslCollineation_mk (A : SL) :
    pslCollineation (A : PSL) = specialLinearCollineation A := rfl

@[simp] theorem pslCollineation_point (A : PSL) (p : PG) :
    Collineation.pointHom PG PG (pslCollineation A) p = A • p := by
  induction A using QuotientGroup.induction_on with | H A => rfl

@[simp] theorem pslCollineation_pointPerm (A : PSL) :
    Collineation.pointHom PG PG (pslCollineation A) = Projectivization.PSLAction.toPermHom A :=
  Equiv.ext (pslCollineation_point A)

theorem pslCollineation_injective : Function.Injective pslCollineation := by
  intro A B h
  apply ProjectiveSpecialLinearGroup.toPermHom_injective
  simpa only [pslCollineation_pointPerm] using congrArg (Collineation.pointHom PG PG) h

/-- Coordinatewise Frobenius as an injective semilinear map. -/
@[expose] def frobeniusSemilinear : (Fin 3 → F) →ₛₗ[fieldFrobenius.toRingHom] (Fin 3 → F) where
  toFun v i := fieldFrobenius (v i)
  map_add' v w := by ext i; exact map_add fieldFrobenius _ _
  map_smul' a v := by ext i; exact map_mul fieldFrobenius _ _

theorem frobeniusSemilinear_involutive : Function.Involutive frobeniusSemilinear := by
  intro v
  ext i
  exact fieldFrobenius_involutive (v i)

/-- The involutive permutation induced by coordinatewise squaring. -/
@[expose] def projectiveFrobenius : Equiv.Perm PG where
  toFun := Projectivization.map frobeniusSemilinear frobeniusSemilinear_involutive.injective
  invFun := Projectivization.map frobeniusSemilinear frobeniusSemilinear_involutive.injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk]
    congr 1
    exact frobeniusSemilinear_involutive v
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [Projectivization.map_mk]
    congr 1
    exact frobeniusSemilinear_involutive v

@[simp] theorem projectiveFrobenius_mk (v : Fin 3 → F) (hv : v ≠ 0) :
    projectiveFrobenius (mk F v hv) =
      mk F (fun i => fieldFrobenius (v i))
        (by exact (map_zero frobeniusSemilinear) ▸ frobeniusSemilinear_involutive.injective.ne hv) := rfl

theorem projectiveFrobenius_involutive : Function.Involutive projectiveFrobenius :=
  projectiveFrobenius.left_inv

theorem frobenius_dotProduct (v w : Fin 3 → F) :
    (fun i => fieldFrobenius (v i)) ⬝ᵥ (fun i => fieldFrobenius (w i)) =
      fieldFrobenius (v ⬝ᵥ w) := by
  simp only [dotProduct, map_sum, map_mul]

/-- Coordinate Frobenius on both points and line covectors. -/
@[expose] def frobeniusCollineation : Collineation PG PG :=
  ⟨(projectiveFrobenius, projectiveFrobenius), by
    intro p l
    induction p using Projectivization.ind with | h v hv =>
    induction l using Projectivization.ind with | h w hw =>
    simp only [projectiveFrobenius_mk, ofField.mem_iff, orthogonal_mk,
      frobenius_dotProduct]
    exact map_eq_zero_iff fieldFrobenius fieldFrobenius.injective⟩

@[simp] theorem frobeniusCollineation_point :
    Collineation.pointHom PG PG frobeniusCollineation = projectiveFrobenius := rfl

@[simp] theorem frobeniusCollineation_line :
    Collineation.lineHom PG PG frobeniusCollineation = projectiveFrobenius := rfl

theorem frobeniusCollineation_sq : frobeniusCollineation ^ 2 = 1 := by
  apply Collineation.ext <;> intro p <;> exact projectiveFrobenius_involutive p

theorem frobenius_smul (A : SL) (v : Fin 3 → F) :
    frobeniusSemilinear (A • v) = slFrobenius A • frobeniusSemilinear v := by
  ext i
  change fieldFrobenius (∑ j, A i j * v j) =
    ∑ j, fieldFrobenius (A i j) * fieldFrobenius (v j)
  simp only [map_sum, map_mul]

theorem projectiveFrobenius_smul (A : PSL) (p : PG) :
    projectiveFrobenius (A • p) = pslFrobenius A • projectiveFrobenius p := by
  induction A using QuotientGroup.induction_on with | H A =>
  induction p using Projectivization.ind with | h v hv =>
  change mk F (frobeniusSemilinear (A • v)) _ =
    mk F (slFrobenius A • frobeniusSemilinear v) _
  congr 1
  exact frobenius_smul A v

theorem pslCollineation_frobenius (A : PSL) :
    pslCollineation (pslFrobenius A) =
      frobeniusCollineation * pslCollineation A * frobeniusCollineation⁻¹ := by
  classical
  apply Collineation.ext_points
  intro p
  simp only [map_mul, map_inv, Equiv.Perm.mul_apply, pslCollineation_point]
  change pslFrobenius A • p = projectiveFrobenius (A • projectiveFrobenius p)
  rw [projectiveFrobenius_smul, projectiveFrobenius_involutive]

/-- The field complement acting by coordinate Frobenius. -/
@[expose] def fieldCollineation : C2 →* Collineation PG PG :=
  involutionHom frobeniusCollineation frobeniusCollineation_sq

/-- Compatibility of the linear and field actions for the semidirect-product lift. -/
theorem pairedAction_compatibility (t : C2) :
    pslCollineation.comp (fieldAction t).toMonoidHom =
      (MulAut.conj (fieldCollineation t)).toMonoidHom.comp pslCollineation := by
  change ZMod 2 at t
  fin_cases t
  · apply MonoidHom.ext
    intro A
    change pslCollineation (fieldAction 1 A) =
      fieldCollineation 1 * pslCollineation A * (fieldCollineation 1)⁻¹
    simp
  · apply MonoidHom.ext
    intro A
    change pslCollineation (pslFrobenius A) =
      frobeniusCollineation * pslCollineation A * frobeniusCollineation⁻¹
    exact pslCollineation_frobenius A

/-- The paired collineation representation of the actual semidirect product. -/
@[expose] def pairedAction : FieldExtension →* Collineation PG PG :=
  SemidirectProduct.lift pslCollineation fieldCollineation pairedAction_compatibility

@[simp] theorem pairedAction_linearInclusion (A : PSL) :
    pairedAction (linearInclusion A) = pslCollineation A :=
  SemidirectProduct.lift_inl _ _ _ A

@[simp] theorem pairedAction_fieldInclusion (t : C2) :
    pairedAction (fieldInclusion t) = fieldCollineation t :=
  SemidirectProduct.lift_inr _ _ _ t

/-- Frobenius is not induced by any determinant-one linear matrix. -/
theorem projectiveFrobenius_not_linear (A : SL) :
    MulAction.toPermHom SL PG A ≠ projectiveFrobenius := by
  intro h
  have hv (v : Fin 3 → F) (hv : v ≠ 0) :
      ∃ a : Fˣ, a • (fun i => fieldFrobenius (v i)) = A • v := by
    have he := Equiv.congr_fun h (mk F v hv)
    change A • mk F v hv = projectiveFrobenius (mk F v hv) at he
    simpa only [smul_mk, projectiveFrobenius_mk, mk_eq_mk_iff] using he
  obtain ⟨a, ha⟩ := hv ![1, 0, 0] (by simp)
  obtain ⟨b, hb⟩ := hv ![0, 1, 0] (by simp)
  obtain ⟨c, hc⟩ := hv ![1, 1, 0] (by simp)
  obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
  obtain ⟨d, hd⟩ := hv ![1, x, 0] (by simp)
  have ha0 := congrFun ha 0
  have ha1 := congrFun ha 1
  have hb0 := congrFun hb 0
  have hb1 := congrFun hb 1
  have hc0 := congrFun hc 0
  have hc1 := congrFun hc 1
  have hd0 := congrFun hd 0
  have hd1 := congrFun hd 1
  change (a : F) * fieldFrobenius 1 = (A.val *ᵥ ![1, 0, 0]) 0 at ha0
  change (a : F) * fieldFrobenius 0 = (A.val *ᵥ ![1, 0, 0]) 1 at ha1
  change (b : F) * fieldFrobenius 0 = (A.val *ᵥ ![0, 1, 0]) 0 at hb0
  change (b : F) * fieldFrobenius 1 = (A.val *ᵥ ![0, 1, 0]) 1 at hb1
  change (c : F) * fieldFrobenius 1 = (A.val *ᵥ ![1, 1, 0]) 0 at hc0
  change (c : F) * fieldFrobenius 1 = (A.val *ᵥ ![1, 1, 0]) 1 at hc1
  change (d : F) * fieldFrobenius 1 = (A.val *ᵥ ![1, x, 0]) 0 at hd0
  change (d : F) * fieldFrobenius x = (A.val *ᵥ ![1, x, 0]) 1 at hd1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1
  have hab : (a : F) = b := by linear_combination -hc0 + hc1 + ha0 - hb1 - ha1 + hb0
  have hda : (d : F) = a := by rw [← ha0, ← hb0] at hd0; simpa using hd0
  apply hx
  apply mul_left_cancel₀ a.ne_zero
  change (a : F) * x ^ 2 = (a : F) * x
  rw [hda, ← ha1, ← hb1, ← hab] at hd1
  simpa using hd1

theorem projectiveFrobenius_not_psl (A : PSL) :
    Projectivization.PSLAction.toPermHom A ≠ projectiveFrobenius := by
  induction A using QuotientGroup.induction_on with
  | H A => exact projectiveFrobenius_not_linear A

/-- The action on projective points. -/
@[expose] def pointAction : FieldExtension →* Equiv.Perm PG :=
  (Collineation.pointHom PG PG).comp pairedAction

/-- The point permutation alone is faithful. -/
theorem pointAction_injective : Function.Injective pointAction := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have he : Projectivization.PSLAction.toPermHom g.left *
      Collineation.pointHom PG PG (fieldCollineation g.right) = 1 := by
    change Collineation.pointHom PG PG (pslCollineation g.left * fieldCollineation g.right) = 1 at hg
    simpa only [map_mul, pslCollineation_pointPerm] using hg
  rcases g with ⟨A, t⟩
  change ZMod 2 at t
  fin_cases t
  · change Projectivization.PSLAction.toPermHom A *
        Collineation.pointHom PG PG (fieldCollineation 1) = 1 at he
    have hA : Projectivization.PSLAction.toPermHom A = 1 := by
      simpa only [map_one, mul_one] using he
    have hA' : A = 1 := ProjectiveSpecialLinearGroup.toPermHom_injective (by simpa using hA)
    subst A
    rfl
  · change Projectivization.PSLAction.toPermHom A *
        Collineation.pointHom PG PG (fieldCollineation (Multiplicative.ofAdd (1 : ZMod 2))) = 1 at he
    exfalso
    apply projectiveFrobenius_not_psl A
    have he' : Projectivization.PSLAction.toPermHom A * projectiveFrobenius = 1 := by
      simpa only [fieldCollineation, involutionHom_generator, frobeniusCollineation_point] using he
    have hf : projectiveFrobenius * projectiveFrobenius = 1 := by
      ext p
      exact projectiveFrobenius_involutive p
    exact mul_right_cancel (he'.trans hf.symm)

/-- The semidirect product acts faithfully by paired collineations. -/
theorem pairedAction_injective : Function.Injective pairedAction :=
  fun _ _ h => pointAction_injective (congrArg (Collineation.pointHom PG PG) h)

/-- The action on line covectors. -/
@[expose] def lineAction : FieldExtension →* Equiv.Perm PG :=
  (Collineation.lineHom PG PG).comp pairedAction

private theorem collineation_lineHom_injective :
    Function.Injective (Collineation.lineHom PG PG) := by
  classical
  intro g h he
  let swap : Collineation PG PG → Collineation PG PG := fun g =>
    ⟨(Collineation.lineHom PG PG g, Collineation.pointHom PG PG g), by
      intro p l
      exact orthogonal_comm.trans ((g.property l p).trans orthogonal_comm)⟩
  have hs : swap g = swap h := Collineation.ext_points (fun p => Equiv.congr_fun he p)
  apply Collineation.ext
  · intro p
    exact congrArg (fun c => Collineation.lineHom PG PG c p) hs
  · intro p
    exact Equiv.congr_fun he p

/-- The line permutation alone is faithful. -/
theorem lineAction_injective : Function.Injective lineAction :=
  fun _ _ h => pairedAction_injective (collineation_lineHom_injective h)

@[simp] theorem pslCollineation_line_mk (A : SL) (l : PG) :
    Collineation.lineHom PG PG (pslCollineation (A : PSL)) l =
      SpecialLinearGroup.inverseTranspose A • l := rfl

@[simp] theorem pairedAction_linear_point (A : SL) (p : PG) :
    Collineation.pointHom PG PG (pairedAction (linearInclusion (A : PSL))) p = A • p := by
  rw [pairedAction_linearInclusion, pslCollineation_mk]
  rfl

@[simp] theorem pairedAction_linear_line (A : SL) (l : PG) :
    Collineation.lineHom PG PG (pairedAction (linearInclusion (A : PSL))) l =
      SpecialLinearGroup.inverseTranspose A • l := by
  rw [pairedAction_linearInclusion, pslCollineation_line_mk]

@[simp] theorem fieldCollineation_generator :
    fieldCollineation (Multiplicative.ofAdd (1 : ZMod 2)) = frobeniusCollineation :=
  involutionHom_generator _ _

@[simp] theorem pairedAction_field_generator :
    pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2))) =
      frobeniusCollineation := by
  rw [pairedAction_fieldInclusion, fieldCollineation_generator]

@[simp] theorem pairedAction_field_point (p : PG) :
    Collineation.pointHom PG PG
      (pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)))) p =
      projectiveFrobenius p := by
  rw [pairedAction_field_generator]
  rfl

@[simp] theorem pairedAction_field_line (l : PG) :
    Collineation.lineHom PG PG
      (pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)))) l =
      projectiveFrobenius l := by
  rw [pairedAction_field_generator]
  rfl

/-- On nonzero coordinate vectors, projective Frobenius squares every entry. -/
theorem projectiveFrobenius_mk_sq (v : Fin 3 → F) (hv : v ≠ 0) :
    projectiveFrobenius (mk F v hv) = mk F (fun i => v i ^ 2)
      (by exact (map_zero frobeniusSemilinear) ▸ frobeniusSemilinear_involutive.injective.ne hv) := rfl

end
end Matrix.PSL3Four
