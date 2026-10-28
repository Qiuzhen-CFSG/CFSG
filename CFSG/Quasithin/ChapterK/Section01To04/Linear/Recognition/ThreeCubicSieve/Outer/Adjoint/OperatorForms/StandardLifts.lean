module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.Lifts
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm

/-!
# Compatible standard lifts of the actual projective adjoint action

An adjoint marking makes the scalar center of SL₃ act trivially. Together
with the central-kernel hypothesis this identifies the literal quotient
SL₃/Z(SL₃) with the representation's action image. Conjugation by a linear
normalizer element therefore gives an automorphism of precisely this quotient.

Standard automorphism coverage and the linear–field–graph factorization
supply a matrix conjugator and a coefficient automorphism. Conjugation,
entrywise coefficient transport and transpose preserve the trace-zero space.
Their explicit intertwining identities give a semilinear operator inducing
the same projective automorphism as the original normalizer element. Equality
of projective representatives is respected by both actions.

No faithfulness on SL₃, involution equation or Schur linearity is required.
The coverage theorem includes the fields of orders two and four, and the
construction includes the identity normalizer element.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript pp.26–28; Aschbacher–Smith K.3.2, printed
pp.451,454–456. The actual standard automorphisms use GLS III, §2.7.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.StandardLifts
open Matrix
variable {F : Type*} [Field F]
private abbrev mat (x : AdjointSpace F) : Matrix (Fin 3) (Fin 3) F := LinearMap.toMatrix' x.val
private lemma mat_injective : Function.Injective (mat (F := F)) :=
  LinearMap.toMatrix'.injective.comp Subtype.val_injective
private lemma mat_trace (x : AdjointSpace F) : (mat x).trace = 0 := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact x.property

private def ofMat (X : Matrix (Fin 3) (Fin 3) F) (hX : X.trace = 0) : AdjointSpace F :=
  ⟨X.toLin', by change LinearMap.trace F _ X.toLin' = 0; rwa [Matrix.trace_toLin'_eq]⟩
@[simp] private lemma mat_ofMat (X : Matrix (Fin 3) (Fin 3) F) (hX : X.trace = 0) :
    mat (ofMat X hX) = X := LinearMap.toMatrix'_toLin' X
@[simp] private lemma mat_add (x y : AdjointSpace F) : mat (x + y) = mat x + mat y := by
  exact map_add LinearMap.toMatrix' x.val y.val
@[simp] private lemma mat_smul (c : F) (x : AdjointSpace F) : mat (c • x) = c • mat x := by
  exact map_smul LinearMap.toMatrix' c x.val

private def conj (g : GL (Fin 3) F) : AdjointSpace F ≃ₗ[F] AdjointSpace F where
  toFun x := ofMat (g.val * mat x * g.inv) ((Matrix.trace_units_conj g (mat x)).trans (mat_trace x))
  invFun x := ofMat (g.inv * mat x * g.val) ((Matrix.trace_units_conj' g (mat x)).trans (mat_trace x))
  left_inv x := by
    apply mat_injective
    simp only [mat_ofMat, ← mul_assoc, g.inv_val, one_mul]
    rw [mul_assoc, g.inv_val, mul_one]
  right_inv x := by
    apply mat_injective
    simp only [mat_ofMat, ← mul_assoc, g.val_inv, one_mul]
    rw [mul_assoc, g.val_inv, mul_one]
  map_add' x y := by apply mat_injective; simp [mul_add, add_mul]
  map_smul' c x := by apply mat_injective; simp
@[simp] private lemma mat_conj (g : GL (Fin 3) F) (x : AdjointSpace F) :
    mat (conj g x) = g.val * mat x * g.inv := LinearMap.toMatrix'_toLin' _

private def transpose : AdjointSpace F ≃ₗ[F] AdjointSpace F where
  toFun x := ofMat (mat x).transpose (by rw [Matrix.trace_transpose, mat_trace])
  invFun x := ofMat (mat x).transpose (by rw [Matrix.trace_transpose, mat_trace])
  left_inv x := by apply mat_injective; simp
  right_inv x := by apply mat_injective; simp
  map_add' x y := by apply mat_injective; simp
  map_smul' c x := by apply mat_injective; simp
@[simp] private lemma mat_transpose (x : AdjointSpace F) : mat (transpose x) = (mat x).transpose :=
  LinearMap.toMatrix'_toLin' _

private def coefficients (φ : F ≃+* F) : AdjointSpace F ≃+ AdjointSpace F where
  toFun x := ofMat ((mat x).map φ) (by rw [← AddMonoidHom.map_trace, mat_trace, map_zero])
  invFun x := ofMat ((mat x).map φ.symm) (by rw [← AddMonoidHom.map_trace, mat_trace, map_zero])
  left_inv x := by apply mat_injective; simp only [mat_ofMat]; ext i j; simp
  right_inv x := by apply mat_injective; simp only [mat_ofMat]; ext i j; simp
  map_add' x y := by apply mat_injective; simp only [mat_ofMat, mat_add]; ext i j; exact map_add φ _ _
@[simp] private lemma mat_coefficients (φ : F ≃+* F) (x : AdjointSpace F) :
    mat (coefficients φ x) = (mat x).map φ := LinearMap.toMatrix'_toLin' _
private lemma coefficients_smul (φ : F ≃+* F) (c : F) (x : AdjointSpace F) :
    coefficients φ (c • x) = φ c • coefficients φ x := by
  apply mat_injective
  simp only [mat_coefficients, mat_smul]
  ext i j
  exact map_mul φ c (mat x i j)

variable (B : BinaryField)
private def binaryCoefficients (φ : B.Carrier ≃+* B.Carrier) :
    AdjointSpace B.Carrier ≃ₗ[ZMod 2] AdjointSpace B.Carrier :=
  { coefficients φ with map_smul' := ZMod.map_smul (coefficients φ) }
private lemma mat_binaryRep (s : SL(3,B.Carrier)) (x : AdjointSpace B.Carrier) :
    mat (binaryRep B s x) = s.val * mat x * (s⁻¹).val := by
  change LinearMap.toMatrix' (natural (RingHom.id B.Carrier) s ∘ₗ x.val ∘ₗ
    natural (RingHom.id B.Carrier) s⁻¹) = _
  have hn (a : SL(3,B.Carrier)) : LinearMap.toMatrix' (natural (RingHom.id B.Carrier) a) = a.val := by
    change LinearMap.toMatrix' (a.val.map (RingHom.id B.Carrier)).toLin' = _
    rw [LinearMap.toMatrix'_toLin']
    rfl
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hn, hn]
  exact (mul_assoc _ _ _).symm

private lemma binaryRep_center (s : SL(3,B.Carrier)) (hs : s ∈ Subgroup.center _) :
    binaryRep B s = 1 := by
  apply LinearMap.ext
  intro x
  apply mat_injective
  rw [mat_binaryRep]
  change s.val * mat x * (s⁻¹).val = mat x
  obtain ⟨c, hc, hcs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
  have hcomm : s.val * mat x = mat x * s.val := by
    rw [← hcs]
    exact (Matrix.scalar_commute c (fun a => Commute.all c a) (mat x)).eq
  rw [hcomm, mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, mul_one]

private lemma binaryRep_projective_eq (l h : SL(3,B.Carrier))
    (hh : (QuotientGroup.mk l : PSL(3,B.Carrier)) = QuotientGroup.mk h) :
    binaryRep B l = binaryRep B h := by
  have hc := binaryRep_center B (l⁻¹ * h) (QuotientGroup.eq.mp hh)
  have he := congrArg (fun f => binaryRep B l * f) hc
  simpa only [← map_mul, mul_inv_cancel_left, mul_one] using he.symm

open Matrix.PSL3.OuterSolvable
private lemma conj_intertwines (g : GL (Fin 3) B.Carrier) (l : SL(3,B.Carrier))
    (x : AdjointSpace B.Carrier) :
    conj g (binaryRep B l x) = binaryRep B (linearConjSL B.Carrier g l) (conj g x) := by
  apply mat_injective
  have hv (a : SL(3,B.Carrier)) : (linearConjSL B.Carrier g a).val =
      g.val * a.val * g.inv := congrArg Units.val (linearConjSL_toGL B.Carrier g a)
  rw [mat_conj, mat_binaryRep, mat_binaryRep, mat_conj, ← map_inv, hv, hv]
  simp only [mul_assoc, ← mul_assoc g.inv g.val, g.inv_val, one_mul]

private lemma coefficients_intertwines (φ : B.Carrier ≃+* B.Carrier) (l : SL(3,B.Carrier))
    (x : AdjointSpace B.Carrier) :
    coefficients φ (binaryRep B l x) =
      binaryRep B (SpecialLinearGroup.map φ.toRingHom l) (coefficients φ x) := by
  apply mat_injective
  rw [mat_coefficients, mat_binaryRep, mat_binaryRep, mat_coefficients, ← map_inv]
  simp only [Matrix.map_mul]; rfl

private lemma transpose_intertwines (l : SL(3,B.Carrier)) (x : AdjointSpace B.Carrier) :
    transpose (binaryRep B l x) = binaryRep B (graphSL B.Carrier l) (transpose x) := by
  apply mat_injective
  have hv (a : SL(3,B.Carrier)) : (graphSL B.Carrier a).val = (a⁻¹).val.transpose := by
    exact (Matrix.adjugate_transpose a.val).symm
  rw [mat_transpose, mat_binaryRep, mat_binaryRep, mat_transpose, ← map_inv, hv, hv, inv_inv]
  simp only [Matrix.transpose_mul, mul_assoc]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

private lemma center_le_ker (e : σ.Equiv (binaryRep B)) : Subgroup.center _ ≤ σ.ker := by
  intro l hl
  change σ l = 1
  apply LinearMap.ext
  intro v
  apply e.toLinearEquiv.injective
  change e (σ l v) = e v
  have he := LinearMap.congr_fun (e.isIntertwining' l) v
  change e (σ l v) = binaryRep B l (e v) at he
  simpa only [binaryRep_center B l hl, Module.End.one_apply] using he

private lemma groupHom_ker_eq_center (e : σ.Equiv (binaryRep B))
    (hk : σ.ker ≤ Subgroup.center _) : σ.asGroupHom.ker = Subgroup.center _ := by
  have hh : σ.asGroupHom.ker = σ.ker := by
    ext l
    change σ.asGroupHom l = 1 ↔ σ l = 1
    exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩
  rw [hh]
  exact le_antisymm hk (center_le_ker B σ e)

private def projectiveImageEquiv (e : σ.Equiv (binaryRep B))
    (hk : σ.ker ≤ Subgroup.center _) : PSL(3,B.Carrier) ≃* actionImage σ :=
  (QuotientGroup.quotientMulEquivOfEq (groupHom_ker_eq_center B σ e hk).symm).trans
    (QuotientGroup.quotientKerEquivRange σ.asGroupHom)

private lemma projectiveImageEquiv_mk (e : σ.Equiv (binaryRep B))
    (hk : σ.ker ≤ Subgroup.center _) (l : SL(3,B.Carrier)) :
    projectiveImageEquiv B σ e hk (QuotientGroup.mk l) = actionHom σ l := rfl

private def quotientActor (e : σ.Equiv (binaryRep B)) (hk : σ.ker ≤ Subgroup.center _)
    (t : linearNormalizer σ) : MulAut PSL(3,B.Carrier) :=
  MulAut.congr (projectiveImageEquiv B σ e hk).symm ((actionImage σ).normalizerMonoidHom t)

private lemma quotientActor_intertwines (e : σ.Equiv (binaryRep B))
    (hk : σ.ker ≤ Subgroup.center _) (t : linearNormalizer σ) (l h : SL(3,B.Carrier))
    (ha : quotientActor B σ e hk t (QuotientGroup.mk l) = QuotientGroup.mk h) (v : V) :
    t.val.val (σ l v) = σ h (t.val.val v) := by
  have he := congrArg (projectiveImageEquiv B σ e hk) ha
  change projectiveImageEquiv B σ e hk
    ((projectiveImageEquiv B σ e hk).symm
      ((actionImage σ).normalizerMonoidHom t
        (projectiveImageEquiv B σ e hk (QuotientGroup.mk l)))) =
    projectiveImageEquiv B σ e hk (QuotientGroup.mk h) at he
  rw [MulEquiv.apply_symm_apply, projectiveImageEquiv_mk, projectiveImageEquiv_mk] at he
  have hu := congrArg (fun a : actionImage σ => a.val * t.val) he
  change (t.val * σ.asGroupHom l * t.val⁻¹) * t.val = σ.asGroupHom h * t.val at hu
  rw [inv_mul_cancel_right] at hu
  exact congrArg (fun a : (Module.End (ZMod 2) V)ˣ => a.val v) hu

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.StandardLifts
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
open StandardLifts Matrix.PSL3.OuterSolvable
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

/-- Every normalizer element of an actual binary adjoint representation has
a compatible semilinear lift of its literal projective action. The adjoint
marking and central kernel suffice; irreducibility is not needed. -/
theorem normalizer_lifts (hk : σ.ker ≤ Subgroup.center _) : NormalizerLifts B σ := by
  intro e t
  let α := quotientActor B σ e hk t
  have hα : α ∈ standard B.Carrier := by
    rw [standard_eq_top_of_two_power_card B.Carrier B.degree_pos B.card_eq]
    trivial
  obtain ⟨g, φ, hf | hg⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization
    B.Carrier field_linearConj graph_linearConj_exists field_commute_graph α hα
  · refine ⟨{
      quotientAction := α
      equiv := (binaryCoefficients B φ).trans ((conj g).restrictScalars (ZMod 2))
      conjugator := g
      coefficient := φ
      scalar_action := ?_
      matrix_action := Or.inl ?_
      original_action := quotientActor_intertwines B σ e hk t
      adjoint_action := ?_ }⟩
    · intro c x
      change conj g (coefficients φ (c • x)) = φ c • conj g (coefficients φ x)
      rw [coefficients_smul, map_smul]
    · intro x
      change mat (conj g (coefficients φ x)) = _
      rw [mat_conj, mat_coefficients]
    · intro l h ha x
      change conj g (coefficients φ (binaryRep B l x)) =
        binaryRep B h (conj g (coefficients φ x))
      rw [coefficients_intertwines, conj_intertwines]
      have hq : (QuotientGroup.mk
          (linearConjSL B.Carrier g (Matrix.SpecialLinearGroup.map φ.toRingHom l)) :
          PSL(3,B.Carrier)) = QuotientGroup.mk h := by
        simpa only [hf, MulAut.mul_apply, fieldAction_mk, linearConj_mk] using ha
      rw [binaryRep_projective_eq B _ _ hq]
  · refine ⟨{
      quotientAction := α
      equiv := ((transpose (F := B.Carrier)).restrictScalars (ZMod 2)).trans
        ((binaryCoefficients B φ).trans ((conj g).restrictScalars (ZMod 2)))
      conjugator := g
      coefficient := φ
      scalar_action := ?_
      matrix_action := Or.inr ?_
      original_action := quotientActor_intertwines B σ e hk t
      adjoint_action := ?_ }⟩
    · intro c x
      change conj g (coefficients φ (transpose (c • x))) =
        φ c • conj g (coefficients φ (transpose x))
      rw [map_smul, coefficients_smul, map_smul]
    · intro x
      change mat (conj g (coefficients φ (transpose x))) = _
      rw [mat_conj, mat_coefficients, mat_transpose]
      rfl
    · intro l h ha x
      change conj g (coefficients φ (transpose (binaryRep B l x))) =
        binaryRep B h (conj g (coefficients φ (transpose x)))
      rw [transpose_intertwines, coefficients_intertwines, conj_intertwines]
      have hq : (QuotientGroup.mk (linearConjSL B.Carrier g
          (Matrix.SpecialLinearGroup.map φ.toRingHom (graphSL B.Carrier l))) :
          PSL(3,B.Carrier)) = QuotientGroup.mk h := by
        have hgm : graph B.Carrier (QuotientGroup.mk l) =
            QuotientGroup.mk (graphSL B.Carrier l) := rfl
        simpa only [hg, MulAut.mul_apply, hgm, fieldAction_mk, linearConj_mk] using ha
      rw [binaryRep_projective_eq B _ _ hq]
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms
