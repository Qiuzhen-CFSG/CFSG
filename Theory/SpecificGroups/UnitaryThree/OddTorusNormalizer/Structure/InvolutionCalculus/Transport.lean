module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.PermutationAction
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.InvolutionCalculus.Swap

/-!
# Changing the coordinates of a frame involution

Every order-two permutation of three coordinates is conjugate to the swap
of coordinates zero and one. Reindexing the determinant-one triple gives
a multiplicative equivalence of pair coordinates, preserves the diagonal
cubic kernel, and transports the literal conjugation formula. Thus the swap
calculation applies to every transposition without changing the ambient
special or projective subgroup.

Source: GLS4, Chapter 4, Lemma 3.11(c), and Chapter 2, Lemma 17.4.
-/

public section

namespace UnitaryThree.OddTorusNormalizer.InvolutionCalculus
variable {G : Type*} [Group G]

open BenderSuzuki.MatrixGroups HermitianForm HermitianForm.EvenInner
variable {E : Type*} [Field E]

lemma frameTriple_mul (J : HermitianForm 3 E) (x y : normOne J × normOne J)
    (i : Fin 3) : frameTriple J (x * y) i = frameTriple J x i * frameTriple J y i := by
  fin_cases i <;> simp [frameTriple, mul_comm, mul_left_comm, mul_assoc]

@[expose] def framePairEquiv (J : HermitianForm 3 E) (τ : Equiv.Perm (Fin 3)) :
    (normOne J × normOne J) ≃* (normOne J × normOne J) where
  toFun := permuteFramePair J τ
  invFun := permuteFramePair J τ⁻¹
  left_inv x := by rw [← permuteFramePair_mul, inv_mul_cancel, permuteFramePair_one]
  right_inv x := by rw [← permuteFramePair_mul, mul_inv_cancel, permuteFramePair_one]
  map_mul' x y := Prod.ext (frameTriple_mul J x y (τ⁻¹ 0))
    (frameTriple_mul J x y (τ⁻¹ 1))

lemma framePairEquiv_cubic_scalar (J : HermitianForm 3 E) (τ : Equiv.Perm (Fin 3))
    (a : normOne J) (ha : a ^ 3 = 1) :
    framePairEquiv J τ (a, a) = (a, a) := by
  have hi : (a * a)⁻¹ = a := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, pow_zero, one_mul] using ha
  have hf (i : Fin 3) : frameTriple J (a, a) i = a := by
    fin_cases i <;> simp [frameTriple, hi]
  exact Prod.ext (hf (τ⁻¹ 0)) (hf (τ⁻¹ 1))

lemma framePairEquiv_cubic_iff (J : HermitianForm 3 E) (τ : Equiv.Perm (Fin 3))
    (x : normOne J × normOne J) :
    (framePairEquiv J τ x).1 = (framePairEquiv J τ x).2 ∧
      (framePairEquiv J τ x).2 ^ 3 = 1 ↔ x.1 = x.2 ∧ x.2 ^ 3 = 1 := by
  have hf (τ : Equiv.Perm (Fin 3)) (x : normOne J × normOne J)
      (h : x.1 = x.2 ∧ x.2 ^ 3 = 1) : framePairEquiv J τ x = x := by
    obtain ⟨a, b⟩ := x
    obtain ⟨hab, hb⟩ := h
    change a = b at hab
    subst b
    exact framePairEquiv_cubic_scalar J τ a hb
  constructor
  · intro h
    have he := hf τ⁻¹ (framePairEquiv J τ x) h
    change permuteFramePair J τ⁻¹ (permuteFramePair J τ x) = _ at he
    rw [← permuteFramePair_mul, inv_mul_cancel, permuteFramePair_one] at he
    rwa [← he] at h
  · intro h
    rwa [hf τ x h]

lemma exists_swap_coordinates (σ : Equiv.Perm (Fin 3)) (hσ : orderOf σ = 2) :
    ∃ τ : Equiv.Perm (Fin 3), σ * τ = τ * Equiv.swap 0 1 := by
  have hf : ∀ s : Equiv.Perm (Fin 3), s ≠ 1 → s ^ 2 = 1 →
      ∃ r : Equiv.Perm (Fin 3), s * r = r * Equiv.swap 0 1 := by decide
  apply hf σ
  · intro h
    simp [h] at hσ
  · simpa only [hσ] using pow_orderOf_eq_one σ

lemma reindexed_range (J : HermitianForm 3 E)
    (f : normOne J × normOne J →* G) (τ : Equiv.Perm (Fin 3)) :
    (f.comp (framePairEquiv J τ).toMonoidHom).range = f.range := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨framePairEquiv J τ x, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (framePairEquiv J τ).surjective x
    exact ⟨y, rfl⟩

lemma reindexed_action (J : HermitianForm 3 E)
    (f : normOne J × normOne J →* G) (t : G) (σ τ : Equiv.Perm (Fin 3))
    (hτ : σ * τ = τ * Equiv.swap 0 1)
    (hact : ∀ x, t * f x * t⁻¹ = f (permuteFramePair J σ x)) (a b : normOne J) :
    t * (f.comp (framePairEquiv J τ).toMonoidHom) (a, b) * t⁻¹ =
      (f.comp (framePairEquiv J τ).toMonoidHom) (b, a) := by
  change t * f (permuteFramePair J τ (a, b)) * t⁻¹ =
    f (permuteFramePair J τ (b, a))
  rw [hact, ← permuteFramePair_mul, hτ, permuteFramePair_mul]
  rfl

end UnitaryThree.OddTorusNormalizer.InvolutionCalculus
