module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8
public import Theory.AlgebraicGroup.Automorphisms.Lang.proposition_2_1_10_invariant_subgroup

/-!
This module proves GLS3, Proposition 2.1.10. In addition to the separately
proved invariant-subgroup restriction, it shows that a positive iterate of a
Frobenius endomorphism has the corresponding power of its level. The proof
iterates the original matrix intertwining equation and uses that iterated
matrix Frobenius has exponent multiplied by the number of iterations. The
converse regroups a Frobenius witness for a positive power and takes the
positive real root of its level.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private def endomorphismIterate
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) : ℕ → AlgebraicGroup.Morphism K K
  | 0 => AlgebraicGroup.Morphism.id K
  | m + 1 => (endomorphismIterate σ m).comp σ

omit [IsAlgClosed k] in
private theorem endomorphismIterate_onPoints
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (m : ℕ) :
    (endomorphismIterate σ m).onPoints = σ.onPoints^[m] := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext x
      change (endomorphismIterate σ m).onPoints (σ.onPoints x) = _
      rw [ih]
      rfl

private theorem iterate_intertwining
    {α β : Type*} (f : α → α) (g : β → β) (e : α → β)
    (h : ∀ x, e (f x) = g (e x)) (m : ℕ) (x : α) :
    e (f^[m] x) = g^[m] (e x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

omit [IsAlgClosed k] in
private theorem generalLinearFrobenius_iterate_apply
    (n r a m : ℕ) [Fact r.Prime] [CharP k r]
    (x : GL (Fin n) k) :
    (generalLinearFrobenius (k := k) n r a)^[m] x =
      generalLinearFrobenius (k := k) n r (a * m) x := by
  induction m with
  | zero =>
      ext i j
      simp [generalLinearFrobenius]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      ext i j
      change iterateFrobenius k r a
          (iterateFrobenius k r (a * m)
            ((x : Matrix (Fin n) (Fin n) k) i j)) =
        iterateFrobenius k r (a * (m + 1))
          ((x : Matrix (Fin n) (Fin n) k) i j)
      rw [← iterateFrobenius_add_apply]
      congr 2
      simp [Nat.mul_succ, Nat.add_comm]

public theorem proposition_2_1_10
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K) (q₀ : NNReal) :
    ((IsFrobeniusEndomorphismOfLevel (r := r) q₀ σ →
      (∀ (H : ClosedSubgroup K)
        (hInv : σ.onPoints '' (H : Set (Variety.Point K)) =
          (H : Set (Variety.Point K))),
        ∃ τ : AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety,
          IsFrobeniusEndomorphismOfLevel (r := r) q₀ τ ∧
            ∀ x, H.inclusion.onPoints (τ.onPoints x) =
              σ.onPoints (H.inclusion.onPoints x)) ∧
      (∀ m : ℕ, 0 < m →
        ∃ τ : AlgebraicGroup.Morphism K K,
          IsFrobeniusEndomorphismOfLevel (r := r) (q₀ ^ m) τ ∧
            ∀ x, τ.onPoints x = σ.onPoints^[m] x)) ∧
    (∀ m : ℕ, 0 < m →
      (∃ q₁ : NNReal, ∃ τ : AlgebraicGroup.Morphism K K,
        IsFrobeniusEndomorphismOfLevel (r := r) q₁ τ ∧
          ∀ x, τ.onPoints x = σ.onPoints^[m] x) →
      IsFrobeniusEndomorphism (r := r) σ))
    := by
  constructor
  · intro hσ
    constructor
    · intro H hInv
      exact proposition_2_1_10_invariant_subgroup σ q₀ hσ H hInv
    · intro m hm
      rcases hσ with ⟨j, a, n, H, hj, ha, hq, e, he⟩
      letI := H.carrierAlgebraicGroup
      refine ⟨endomorphismIterate σ m, ?_, fun x =>
        congrFun (endomorphismIterate_onPoints σ m) x⟩
      refine ⟨j, a * m, n, H, hj, Nat.mul_pos ha hm, ?_, e, ?_⟩
      · rw [← pow_mul, Nat.mul_comm m j, pow_mul, hq]
        norm_cast
        rw [pow_mul]
      · intro x
        rw [endomorphismIterate_onPoints]
        have hleft :
            (σ.onPoints^[m])^[j] x = (σ.onPoints^[j])^[m] x := by
          rw [← Function.iterate_mul, ← Function.iterate_mul, Nat.mul_comm]
        rw [hleft, iterate_intertwining (σ.onPoints^[j])
          (generalLinearFrobenius (k := k) n r a)
          (fun y => glPointEquiv n (H.inclusion.onPoints (e.hom.onPoints y))) he]
        exact generalLinearFrobenius_iterate_apply n r a m _
  · intro m hm hσm
    rcases hσm with ⟨q₁, τ, hτ, hiter⟩
    rcases hτ with ⟨m', a, n, H, hm', ha', hq, e, he⟩
    letI := H.carrierAlgebraicGroup
    let q₀ : NNReal := q₁ ^ (1 / (m : ℝ))
    have hroot : q₀ ^ m = q₁ := by
      dsimp [q₀]
      rw [← NNReal.rpow_mul_natCast]
      have hm0 : (m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hm)
      field_simp
      simp
    refine ⟨q₀, ?_⟩
    refine ⟨m * m', a, n, H, ?_, ha', ?_, e, ?_⟩
    · exact Nat.mul_pos hm hm'
    · rw [pow_mul, hroot, hq]
    · intro x
      rw [Function.iterate_mul]
      have hiter' : τ.onPoints = σ.onPoints^[m] := funext hiter
      rw [← hiter']
      exact he x

end Theory.AlgebraicGroup
