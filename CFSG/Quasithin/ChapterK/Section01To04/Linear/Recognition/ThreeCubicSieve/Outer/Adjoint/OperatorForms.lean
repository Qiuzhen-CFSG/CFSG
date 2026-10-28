module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.Forms
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.Centralizer
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.Scalars
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.Lifts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.OperatorForms.StandardLifts

/-!
# From actual projective lifts to adjoint involution forms

For two operators implementing the same automorphism of the actual PSL₃
quotient, their quotient is a binary adjoint intertwiner. The centralizer
calculation makes it a defining-field scalar. Schur linearity of the original
actor then removes the coefficient automorphism. Finally the trace pairing
and the square-one equation remove the remaining scalar.

The resulting operator identities use every given representation equivalence,
including the identity actor and the fields of orders two and four. The actual
projective lifts from `StandardLifts` discharge the lift-existence premise and
give `involution_forms` under the central-kernel hypothesis. No faithfulness
on the SL₃ cover is assumed here.

Source: GM, Proposition 4.8, step 3A, manuscript p.27; Aschbacher–Smith K.3.2,
printed pp.454–456. See `Outer/Source.md` for the source copies and conventions.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
namespace OperatorForms
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

/-- The literal normalizer operator on the specified adjoint model. -/
def actor (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ) :
    AdjointSpace B.Carrier ≃ₗ[ZMod 2] AdjointSpace B.Carrier :=
  e.toLinearEquiv.symm.trans
    ((LinearMap.GeneralLinearGroup.toLinearEquiv t.val).trans e.toLinearEquiv)

private theorem actor_square (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ)
    (ht : t ^ 2 = 1) : Function.Involutive (actor B σ e t) := by
  intro x
  have he := congrArg (fun a : linearNormalizer σ => a.val.val) ht
  have hx := LinearMap.congr_fun he (e.symm x)
  change t.val.val (t.val.val (e.symm x)) = e.symm x at hx
  change e (t.val.val (e.symm (e (t.val.val (e.symm x))))) = x
  have he' (v : V) : e.symm (e v) = v := e.toLinearEquiv.symm_apply_apply v
  rw [he', hx]
  exact e.toLinearEquiv.apply_symm_apply x

private theorem actor_intertwines (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ)
    (L : SemilinearLift B σ t) (l h : SL(3,B.Carrier))
    (hl : L.quotientAction (QuotientGroup.mk l) = QuotientGroup.mk h)
    (x : AdjointSpace B.Carrier) :
    actor B σ e t (binaryRep B l x) = binaryRep B h (actor B σ e t x) := by
  change e (t.val.val (e.symm (binaryRep B l x))) =
    binaryRep B h (e (t.val.val (e.symm x)))
  have he' : e.symm (binaryRep B l x) = σ l (e.symm x) :=
    LinearMap.congr_fun (e.symm.toIntertwiningMap.isIntertwining' l) x
  rw [he', L.original_action l h hl]
  exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' h) _

variable [IsIrreducible σ]

/-- The quotient of compatible operators is a scalar on the actual adjoint. -/
theorem actor_eq_lift_scalar (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ)
    (L : SemilinearLift B σ t) :
    ∃ c : B.Carrier, ∀ x : AdjointSpace B.Carrier,
      actor B σ e t x = L.equiv (c • x) := by
  let : IsIrreducible (binaryRep B) :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv e)).mp inferInstance
  let C := (actor B σ e t).trans L.equiv.symm
  have hC : ∀ l, ∀ x, C (binaryRep B l x) = binaryRep B l (C x) := by
    intro l x
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,B.Carrier))
      (L.quotientAction (QuotientGroup.mk l))
    have hh' : L.quotientAction (QuotientGroup.mk l) = QuotientGroup.mk h := hh.symm
    apply L.equiv.injective
    change L.equiv (L.equiv.symm (actor B σ e t (binaryRep B l x))) =
      L.equiv (binaryRep B l (L.equiv.symm (actor B σ e t x)))
    rw [L.adjoint_action l h hh', L.equiv.apply_symm_apply, L.equiv.apply_symm_apply]
    exact actor_intertwines B σ e t L l h hh' x
  let f : IntertwiningMap (binaryRep B) (binaryRep B) :=
    C.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _ hC
  obtain ⟨c, hc⟩ := binary_centralizer B f
  refine ⟨c, fun x => ?_⟩
  have hx := congrArg L.equiv (hc x)
  change L.equiv (L.equiv.symm (actor B σ e t x)) = L.equiv (c • x) at hx
  simpa only [L.equiv.apply_symm_apply] using hx

/-- Schur linearity eliminates the coefficient automorphism of an actual lift. -/
theorem coefficient_eq_one (e : σ.Equiv (binaryRep B)) (t : linearNormalizer σ)
    (ht : SchurNormalizer.IsSchurLinear σ t) (L : SemilinearLift B σ t) :
    L.coefficient = RingEquiv.refl B.Carrier := by
  obtain ⟨c, hc⟩ := actor_eq_lift_scalar B σ e t L
  let : Nontrivial (AdjointSpace B.Carrier) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_adjointSpace]; decide)
  obtain ⟨y, hy⟩ := exists_ne (0 : AdjointSpace B.Carrier)
  obtain ⟨x, hx⟩ := (actor B σ e t).surjective y
  apply RingEquiv.ext
  intro a
  have hs : L.coefficient a • y = a • y := by
    calc
      L.coefficient a • y = L.coefficient a • L.equiv (c • x) := by rw [← hc, hx]
      _ = L.equiv (a • (c • x)) := (L.scalar_action a (c • x)).symm
      _ = L.equiv (c • (a • x)) := by rw [smul_comm a c x]
      _ = actor B σ e t (a • x) := (hc (a • x)).symm
      _ = a • actor B σ e t x := schurLinear_smul B σ e t ht a x
      _ = a • y := by rw [hx]
  change L.coefficient a = a
  exact smul_left_injective B.Carrier (m := y) hy hs

/-- A Schur-linear involution has the literal standard matrix action once its
projective action has an actual semilinear lift. -/
theorem hasStandardAction_of_lift (e : σ.Equiv (binaryRep B))
    (t : linearNormalizer σ) (h2 : t ^ 2 = 1)
    (ht : SchurNormalizer.IsSchurLinear σ t) (L : SemilinearLift B σ t) :
    HasStandardAction B σ e t := by
  obtain ⟨c, hc⟩ := actor_eq_lift_scalar B σ e t L
  have hφ := coefficient_eq_one B σ e t ht L
  have hT (x : AdjointSpace B.Carrier) : actor B σ e t x = c • L.equiv x := by
    rw [hc, L.scalar_action, hφ]
    rfl
  have hm : (∀ x, mat (actor B σ e t x) =
      c • (L.conjugator.val * mat x * L.conjugator.inv)) ∨
      (∀ x, mat (actor B σ e t x) =
      c • (L.conjugator.val * (mat x).transpose * L.conjugator.inv)) := by
    rcases L.matrix_action with h | h
    · left
      intro x
      rw [hT]
      change LinearMap.toMatrix' (c • (L.equiv x).val) = _
      rw [map_smul, h x, hφ]
      rfl
    · right
      intro x
      rw [hT]
      change LinearMap.toMatrix' (c • (L.equiv x).val) = _
      rw [map_smul, h x, hφ]
      rfl
  have hc1 := scalar_eq_one_of_square (actor B σ e t)
    (actor_square B σ e t h2) c L.conjugator hm
  refine ⟨L.conjugator, ?_⟩
  rcases hm with h | h
  · left
    intro v
    have hv := h (e v)
    change mat (e (t.val.val (e.symm (e v)))) = _ at hv
    have he' : e.symm (e v) = v := e.toLinearEquiv.symm_apply_apply v
    rw [he', hc1, one_smul] at hv
    exact hv
  · right
    intro v
    have hv := h (e v)
    change mat (e (t.val.val (e.symm (e v)))) = _ at hv
    have he' : e.symm (e v) = v := e.toLinearEquiv.symm_apply_apply v
    rw [he', hc1, one_smul] at hv
    exact hv
end OperatorForms

/-- Assembly of the operator-form obligation from actual projective lifts.
The lift-existence premise remains an independent mathematical prerequisite. -/
theorem involution_forms_of_normalizerLifts (B : BinaryField)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]
    (h : OperatorForms.NormalizerLifts B σ) : InvolutionForms B σ := by
  intro e t h2 ht
  obtain ⟨L⟩ := h e t
  exact OperatorForms.hasStandardAction_of_lift B σ e t h2 ht L

/-- Every Schur-linear involution on an actual binary adjoint model acts by
matrix conjugation or conjugation after transpose, through every specified
adjoint marking. The central SL₃ kernel is allowed, and no field or scalar
factor remains. This supplies the operator-form premise of
`Outer.adjoint_estimate_of_forms`. -/
theorem involution_forms (B : BinaryField)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]
    (hk : σ.ker ≤ Subgroup.center _) : InvolutionForms B σ :=
  involution_forms_of_normalizerLifts B σ (OperatorForms.normalizer_lifts B σ hk)

/-- The identity actor is included in the literal standard-action interface. -/
theorem hasStandardAction_one (B : BinaryField)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)
    (e : σ.Equiv (binaryRep B)) : HasStandardAction B σ e 1 := by
  refine ⟨1, Or.inl ?_⟩
  intro v
  change LinearMap.toMatrix' (e v).val =
    (1 : Matrix (Fin 3) (Fin 3) B.Carrier) * LinearMap.toMatrix' (e v).val * 1
  simp only [one_mul, mul_one]

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
