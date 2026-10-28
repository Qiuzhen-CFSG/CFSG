module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Recovering a field involution from a reflected root pairing

If two additive labels satisfy ψ(x f(y)) = y f(x), divide f by f(1).
Substitution at 1 shows that the normalized map squares to the identity;
substitution into the same pairing then proves multiplicativity. Thus the
labels differ by a scalar and an involutory field automorphism. Over a finite
binary field, a nontrivial reflected action selects the unique nontrivial
involution, retaining fields of orders four and sixteen.

The source application is the B–D commutator and its image under the linear
root reflection in Fong--Seitz II (8C), (8.15)--(8.16), (8.21)--(8.23).
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource

/-- Reversing a nondegenerate field-valued pairing forces its two additive
labels to differ by a scalar and an involutory field automorphism. -/
theorem reflected_pairing_field {E : Type*} [Field E]
    (f ψ : E ≃+ E) (h : ∀ x y, ψ (x * f y) = y * f x) :
    ∃ (k : E) (σ : E ≃+* E), k ≠ 0 ∧ Function.Involutive σ ∧
      (∀ x, f x = k * σ x) ∧ ∀ x, ψ (k * x) = k * σ x := by
  let k := f 1
  have hk : k ≠ 0 := fun hz => one_ne_zero (f.injective (hz.trans f.map_zero.symm))
  have hp (x : E) : ψ (x*k) = f x := by simpa only [one_mul] using h x 1
  have hf (x y : E) : f (x * f y / k) = y * f x := by
    rw [←hp,div_mul_cancel₀ _ hk,h]
  let σ : E → E := fun x => f x / k
  have hσ1 : σ 1 = 1 := div_self hk
  have hσσ (x : E) : σ (σ x) = x := by
    have he := hf 1 x
    simp only [one_mul] at he
    change f (f x / k) / k = x
    rw [he,mul_div_cancel_right₀ _ hk]
  have hm (x y : E) : σ (x * y) = σ x * σ y := by
    have he := hf x (σ y)
    have hey : f (σ y) / k = y := hσσ y
    rw [mul_div_assoc,hey] at he
    change f (x*y)/k = (f x/k)*(f y/k)
    rw [he]
    dsimp only [σ]
    ring
  let e : E ≃+* E := {
    toFun := σ
    invFun := σ
    left_inv := hσσ
    right_inv := hσσ
    map_mul' := hm
    map_add' := fun x y => by change f (x+y)/k = _; rw [map_add,add_div] }
  refine ⟨k,e,hk,hσσ,?_,?_⟩
  · intro x
    exact (mul_div_cancel₀ (f x) hk).symm
  · intro x
    rw [mul_comm k x,hp]
    exact (mul_div_cancel₀ (f x) hk).symm

/-- In a finite binary field the nontrivial automorphism forced by the
reflected pairing is the given nontrivial Hermitian involution. -/
theorem reflected_pairing_conjugation {E : Type*} [Field E] [Finite E] [CharP E 2]
    (f ψ : E ≃+ E) (h : ∀ x y, ψ (x * f y) = y * f x)
    (hψ : ψ ≠ AddEquiv.refl E) (τ : E ≃+* E)
    (hτ : Function.Involutive τ) (hτne : τ ≠ RingEquiv.refl E) :
    ∃ k : E, k ≠ 0 ∧ (∀ x, f x = k * τ x) ∧
      ∀ x, ψ (k*x) = k * τ x := by
  obtain ⟨k,σ,hk,hσ,hf,hp⟩ := reflected_pairing_field f ψ h
  have hσne : σ ≠ RingEquiv.refl E := by
    intro he
    apply hψ
    ext x
    have hh := hp (x/k)
    simpa only [he,RingEquiv.refl_apply,AddEquiv.refl_apply,mul_div_cancel₀ _ hk] using hh
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let a : E ≃ₐ[ZMod 2] E := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x; exact DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) E))
      (algebraMap (ZMod 2) E) ) x)
  let b : E ≃ₐ[ZMod 2] E := AlgEquiv.ofRingEquiv (f := τ) (by
    intro x; exact DFunLike.congr_fun (RingHom.ext_zmod (τ.toRingHom.comp (algebraMap (ZMod 2) E))
      (algebraMap (ZMod 2) E) ) x)
  have ha : orderOf a = 2 := orderOf_eq_prime (by ext x; exact hσ x)
    (fun he => hσne (congrArg AlgEquiv.toRingEquiv he))
  have hb : orderOf b = 2 := orderOf_eq_prime (by ext x; exact hτ x)
    (fun he => hτne (congrArg AlgEquiv.toRingEquiv he))
  have he : σ = τ := congrArg AlgEquiv.toRingEquiv (IsCyclic.eq_of_orderOf_eq_two ha hb)
  exact ⟨k,hk,he ▸ hf,he ▸ hp⟩
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
