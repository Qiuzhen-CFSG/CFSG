module
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Multiplicity actions on finite sums of an absolutely irreducible module

Schur's lemma makes every block of a commuting actor a scalar. A nonzero
vector and a dual coordinate construct the full multiplicity representation;
regular coordinates on each summand then give its literal fiber action.
No faithfulness assumption on the actor or its multiplicity action is used.

Source application: Suzuki Steinberg isotypic components in Aschbacher–Smith
§13.6, printed p.935.
-/

public noncomputable section
open Module Representation
namespace Representation.SchurCopies
variable {k D A E I : Type*} [Field k] [Group D] [Group A]
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  [Fintype I] [DecidableEq I]

omit [Fintype I] in
private theorem block_scalar
    (σ : Representation k D E) [IsIrreducible σ] [IsAbsolutelyIrreducible σ]
    (T : Module.End k (I → E))
    (hc : ∀ d x, T (fun i => σ d (x i)) = fun i => σ d (T x i))
    (i j : I) : ∃ c : k, ∀ v, T (Pi.single j v) i = c • v := by
  classical
  let f : σ.IntertwiningMap σ := {
    toLinearMap := (LinearMap.proj i).comp (T.comp (LinearMap.single k (fun _ : I => E) j))
    isIntertwining' d := by
      apply LinearMap.ext
      intro (v : E)
      have hs : (fun l => σ d ((Pi.single j v : I → E) l)) = Pi.single j (σ d v) := by
        funext l
        by_cases h : j = l
        · subst l; simp
        · simp [Ne.symm h]
      have h := congrFun (hc d (Pi.single j v)) i
      rw [hs] at h
      exact h }
  obtain ⟨c, hc⟩ := (isAbsolutelyIrreducible_iff_surjective σ).mp inferInstance f
  refine ⟨c, fun v => ?_⟩
  have h := congrArg (fun q : σ.IntertwiningMap σ => q v) hc
  exact h.symm

/-- An arbitrary commuting actor on copies of an absolutely irreducible module
has an actual representation on the multiplicity coordinates. -/
theorem exists_multiplicity
    (σ : Representation k D E) [IsIrreducible σ] [IsAbsolutelyIrreducible σ]
    (ρ : Representation k A (I → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i)) :
    ∃ μ : Representation k A (I → k),
      ∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v := by
  classical
  let : Nontrivial E := Subrepresentation.irreducible_module_nontrivial σ
  obtain ⟨z,hz⟩ := exists_ne (0 : E)
  obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one k hz
  let j : (I → k) →ₗ[k] (I → E) := {
    toFun c i := c i • z
    map_add' c d := by ext i; exact add_smul _ _ _
    map_smul' c d := by ext i; exact mul_smul _ _ _ }
  let r : (I → E) →ₗ[k] (I → k) := {
    toFun x i := l (x i)
    map_add' x y := by ext i; exact l.map_add _ _
    map_smul' c x := by ext i; exact l.map_smul _ _ }
  have hrj (c : I → k) : r (j c) = c := by
    ext i
    change l (c i • z) = c i
    rw [map_smul,hl,smul_eq_mul,mul_one]
  have he (a : A) (c : I → k) (v : E) :
      ρ a (fun i => c i • v) = fun i => r (ρ a (j c)) i • v := by
    funext i
    have hexp (x : I → E) : x = ∑ b : I, Pi.single b (x b) := by
      ext b
      simp
    have hsum (x : I → E) : ρ a x i = ∑ b : I, ρ a (Pi.single b (x b)) i := by
      conv_lhs => rw [hexp x]
      rw [map_sum, Finset.sum_apply]
    rw [hsum]
    change _ = l (ρ a (j c) i) • v
    rw [hsum, map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro b _
    obtain ⟨t,ht⟩ := block_scalar σ (ρ a) (hc a) i b
    rw [ht,ht]
    change t • (c b • v) = l (t • (c b • z)) • v
    rw [map_smul,map_smul,hl,smul_eq_mul,smul_eq_mul,mul_one,smul_smul]
  let μ : Representation k A (I → k) := {
    toFun a := r.comp ((ρ a).comp j)
    map_one' := by
      apply LinearMap.ext
      intro c
      change r (ρ 1 (j c)) = c
      rw [map_one, Module.End.one_apply, hrj]
    map_mul' a b := by
      apply LinearMap.ext
      intro c
      change r (ρ (a*b) (j c)) = r (ρ a (j (r (ρ b (j c)))))
      rw [map_mul, Module.End.mul_apply]
      have h := he b c z
      exact congrArg (fun w => r (ρ a w)) h }
  exact ⟨μ, he⟩
end Representation.SchurCopies

namespace Representation.SchurCopies
variable {k D A E I P : Type*} [Field k] [Group D] [Group A]
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]

/-- Regular coordinates on each irreducible copy turn every commuting actor
into an actual fiberwise multiplicity action. -/
theorem exists_fiber_action
    (σ : Representation k D E) [IsIrreducible σ] [IsAbsolutelyIrreducible σ]
    (ρ : Representation k A (I → E))
    (hc : ∀ a d x, ρ a (fun i => σ d (x i)) = fun i => σ d (ρ a x i))
    (e : E ≃ₗ[k] (P → k)) :
    ∃ μ : Representation k A (I → k),
      ∀ a f x, (fun i => e (ρ a f i) x) = μ a (fun i => e (f i) x) := by
  obtain ⟨μ,hμ⟩ := exists_multiplicity σ ρ hc
  refine ⟨μ, ?_⟩
  intro a f x
  let z : P → E := fun y => e.symm (Pi.single y 1)
  have hdecomp : f = ∑ y : P, fun i => e (f i) y • z y := by
    funext i
    apply e.injective
    simp only [Finset.sum_apply, map_sum, map_smul, z, LinearEquiv.apply_symm_apply]
    funext j
    simp [Pi.single_apply]
  have hz (y : P) : e (z y) = Pi.single y 1 := e.apply_symm_apply _
  have hact : ρ a f = ∑ y : P, fun i => μ a (fun i => e (f i) y) i • z y := by
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact hμ a _ _
  rw [hact]
  funext i
  simp only [Finset.sum_apply, map_sum, map_smul, hz]
  simp [Pi.single_apply]
end Representation.SchurCopies
