module
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Bounds
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Swap
public import Theory.SpecificGroups.PSL2.AutomorphismModel
import Mathlib.Tactic

/-!
# The canonical PSL₂ form of the operator bounds

Characteristic two makes the actual SL₂-to-PSL₂ quotient an isomorphism.
The projective actions here are pulled back by its inverse. Thus the bounds
apply to the genuine projective group and its field automorphisms. Involutivity
of an inner automorphism implies that its lift squares into the center, which
is trivial; no involution-lifting assumption is needed.

Source: GLS, vol. 2, Theorem 26.24, final paragraph.
-/
@[expose] public section
open Module
namespace Representation.BinaryOffender.NaturalTensor
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The genuine PSL₂ natural sum, via the inverse of its canonical quotient. -/
noncomputable def projectiveNaturalSumAction (ι : Type*) :
    Representation F (Theory.PSL2.Group F) (ι → NaturalSpace F) :=
  (naturalSumAction F ι).comp (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom

/-- The genuine projective tensor action, still tensored over F. -/
noncomputable def projectiveTensorAction :
    Representation (ZMod 2) (Theory.PSL2.Group F × Theory.PSL2.Group F) (TensorSpace F) :=
  (binaryTensorAction F).comp
    (((Theory.PSL2.sl2QuotientEquiv F).symm).prodCongr
      (Theory.PSL2.sl2QuotientEquiv F).symm).toMonoidHom

omit [Algebra (ZMod 2) F] in
/-- An involutive inner automorphism has an involutive matrix lift. -/
theorem inner_involutive_lift (r : Matrix.SpecialLinearGroup (Fin 2) F)
    (hr : Function.Involutive (fun g => r * g * r⁻¹)) : r * r = 1 := by
  have hc : r * r ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h : (r * r) * g * (r * r)⁻¹ = g := by
      simpa [mul_assoc] using hr g
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  simpa only [Theory.PSL2.sl2_center_eq_bot, Subgroup.mem_bot] using hc

omit [Algebra (ZMod 2) F] in
/-- Lift the source's involutive projective inner automorphism through the quotient. -/
theorem projective_inner_involutive_lift (r : Theory.PSL2.Group F)
    (hr : Function.Involutive (fun g => r * g * r⁻¹)) :
    (Theory.PSL2.sl2QuotientEquiv F).symm r * (Theory.PSL2.sl2QuotientEquiv F).symm r = 1 := by
  apply inner_involutive_lift F
  intro g
  apply (Theory.PSL2.sl2QuotientEquiv F).injective
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using
    hr (Theory.PSL2.sl2QuotientEquiv F g)

variable [Finite F]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- All inner involution intertwiners for genuine projective natural sums. -/
theorem projective_natural_sum_inner_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) (Theory.PSL2.Group F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = projectiveNaturalSumAction F ι g (e v))
    (T : Module.End (ZMod 2) V) (hTi : Function.Injective T)
    (r : Theory.PSL2.Group F) (hr : Function.Involutive (fun g => r * g * r⁻¹)) (hne : r ≠ 1)
    (hT : ∀ g v, T (ρ g v) = ρ (r * g * r⁻¹) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T := by
  let Q := Theory.PSL2.sl2QuotientEquiv F
  apply natural_sum_inner_bound F hF (ρ.comp Q.toMonoidHom) e
    (fun g v => by simpa [projectiveNaturalSumAction, Q] using he (Q g) v)
    T hTi (Q.symm r) (projective_inner_involutive_lift F r hr)
    (fun h => hne (by simpa using congrArg Q h))
  intro g v
  simpa using hT (Q g) v

/-- All inner-field intertwiners for the same genuine projective natural action. -/
theorem projective_natural_sum_field_bound {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) (Theory.PSL2.Group F) V)
    (e : V ≃ₗ[ZMod 2] (ι → NaturalSpace F))
    (he : ∀ g v, e (ρ g v) = projectiveNaturalSumAction F ι g (e v))
    (T : Module.End (ZMod 2) V) (r : Theory.PSL2.Group F)
    (σ : F ≃+* F) (hσ : ∃ a, σ a ≠ a)
    (hT : ∀ g v, T (ρ g v) = ρ (r * Theory.PSL2.fieldAut σ g * r⁻¹) (T v)) :
    Fintype.card ι * n ≤ operatorFixedCodim T := by
  let Q := Theory.PSL2.sl2QuotientEquiv F
  apply natural_sum_field_bound F hF (ρ.comp Q.toMonoidHom) e
    (fun g v => by simpa [projectiveNaturalSumAction, Q] using he (Q g) v)
    T (Q.symm r) σ.toRingHom hσ
  intro g v
  have hf : Theory.PSL2.fieldAut σ (Q g) = Q (Matrix.SpecialLinearGroup.map σ.toRingHom g) :=
    Theory.PSL2.fieldAut_apply_quotientMap σ g
  change T (ρ (Q g) v) = ρ (Q (Q.symm r * Matrix.SpecialLinearGroup.map σ.toRingHom g *
    (Q.symm r)⁻¹)) (T v)
  rw [map_mul Q, map_mul Q, map_inv Q, Q.apply_symm_apply]
  rw [← hf]
  exact hT (Q g) v

omit [Finite F] in
/-- The projective tensor model is the actual matrix tensor after the quotient map. -/
theorem projectiveTensorAction_quotient
    (g : Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    (v : TensorSpace F) :
    projectiveTensorAction F ((Theory.PSL2.sl2QuotientEquiv F).prodCongr
      (Theory.PSL2.sl2QuotientEquiv F) g) v = tensorAction F g v := by
  rcases g with ⟨g, h⟩
  simp [projectiveTensorAction, binaryTensorAction, MulEquiv.prodCongr]

end Representation.BinaryOffender.NaturalTensor
