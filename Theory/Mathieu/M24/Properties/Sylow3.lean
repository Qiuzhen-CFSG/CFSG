module

public import Theory.Mathieu.M24.Properties.Order

/-!
# A concrete nonabelian Sylow 3-subgroup of M24

A word in the standard generators supplies a conjugate `y` of the cubic
standard generator `x`. Their commutator `z = y*x*y⁻¹*x⁻¹` gives 27 distinct
words `x^i*y^j*z^k`. Kernel-checked permutation tables verify their coordinate
multiplication and inversion laws. Thus these words form a subgroup of order
27, and the checked order of M24 makes it Sylow. The generators do not commute.

The point tables are checked against words in the existing generators, so the
subgroup lies in the actual Witt-design automorphism carrier.

Sources: the ATLAS degree-24 generators documented in `M24.Generators`;
Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(5), printed p.4 (the odd-rank calculation in its converse).
-/

namespace Sporadic.Mathieu
noncomputable section
set_option maxRecDepth 100000

private def rankA : M24 := ⟨m24GeneratorA, m24GeneratorA_mem⟩
private def rankB : M24 := ⟨m24GeneratorB, m24GeneratorB_mem⟩
private def rankConjugator : M24 :=
  rankB⁻¹ * rankA * rankB * rankA * rankB * rankA * rankB⁻¹ * rankA *
  rankB * rankA * rankB⁻¹ * rankA * rankB * rankA * rankB⁻¹ * rankA *
  rankB * rankA * rankB⁻¹ * rankA * rankB⁻¹ * rankA
private def rankYWord : M24 := rankConjugator * rankB * rankConjugator⁻¹
private def rankXPerm : Equiv.Perm (Fin 24) where
  toFun := ![23, 4, 21, 9, 6, 18, 1, 7, 8, 15, 5, 11, 12, 17, 2, 3, 13, 16, 10, 0, 20, 14, 22, 19]
  invFun := ![19, 6, 14, 15, 1, 10, 4, 7, 8, 3, 18, 11, 12, 16, 21, 9, 17, 13, 5, 23, 20, 2, 22, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def rankYPerm : Equiv.Perm (Fin 24) where
  toFun := ![7, 1, 15, 3, 4, 5, 6, 16, 13, 14, 2, 22, 11, 19, 18, 10, 0, 23, 9, 8, 17, 21, 12, 20]
  invFun := ![16, 1, 10, 3, 4, 5, 6, 0, 19, 18, 15, 12, 22, 8, 9, 2, 7, 20, 14, 13, 23, 21, 11, 17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private def rankZPerm : Equiv.Perm (Fin 24) where
  toFun := ![23, 1, 10, 21, 4, 3, 6, 20, 7, 14, 15, 11, 12, 16, 18, 2, 17, 13, 9, 0, 8, 5, 22, 19]
  invFun := ![19, 1, 15, 5, 4, 21, 6, 8, 20, 18, 2, 11, 12, 17, 9, 10, 13, 16, 14, 23, 7, 3, 22, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private theorem rankYPerm_eq_word : rankYPerm = (rankYWord : Equiv.Perm (Fin 24)) := by
  ext i
  fin_cases i <;> decide +kernel
private theorem rankXPerm_eq_word : rankXPerm = (rankB : Equiv.Perm (Fin 24)) := by
  decide +kernel
private def rankX : M24 := ⟨rankXPerm, rankXPerm_eq_word.symm ▸ rankB.property⟩
private def rankY : M24 := ⟨rankYPerm, rankYPerm_eq_word.symm ▸ rankYWord.property⟩
private theorem rankZPerm_eq_word :
    rankZPerm = ((rankY * rankX * rankY⁻¹ * rankX⁻¹ : M24) : Equiv.Perm (Fin 24)) := by
  decide +kernel
private def rankZ : M24 := ⟨rankZPerm,
  rankZPerm_eq_word.symm ▸ (rankY * rankX * rankY⁻¹ * rankX⁻¹).property⟩
private abbrev Coordinates := Fin 3 × Fin 3 × Fin 3
private def evaluate (t : Coordinates) : M24 :=
  rankX ^ t.1.val * rankY ^ t.2.1.val * rankZ ^ t.2.2.val
private def product (s t : Coordinates) : Coordinates :=
  (s.1+t.1, s.2.1+t.2.1, s.2.2+t.2.2+s.2.1*t.1)
private def inverse (s : Coordinates) : Coordinates :=
  (-s.1, -s.2.1, -s.2.2+s.2.1*s.1)
private theorem evaluate_one : evaluate (0,0,0) = 1 := by
  simp [evaluate]
private theorem evaluate_mul : ∀ s t, evaluate (product s t) = evaluate s * evaluate t := by
  have h : ∀ s t : Coordinates,
      (evaluate (product s t) : Equiv.Perm (Fin 24)) = evaluate s * evaluate t := by
    decide +kernel
  intro s t
  exact Subtype.ext (h s t)
private theorem evaluate_inv : ∀ s, evaluate (inverse s) = (evaluate s)⁻¹ := by
  have h : ∀ s : Coordinates,
      (evaluate (inverse s) : Equiv.Perm (Fin 24)) = (evaluate s : Equiv.Perm (Fin 24))⁻¹ := by
    decide +kernel
  intro s
  exact Subtype.ext (h s)
private theorem evaluate_injective : Function.Injective evaluate := by
  have h : Function.Injective (fun s => (evaluate s : Equiv.Perm (Fin 24))) := by
    decide +kernel
  exact fun _ _ he => h (congrArg Subtype.val he)
/-- The explicit 27-element Heisenberg subgroup of the Witt-design carrier. -/
public def m24Sylow3Subgroup : Subgroup M24 where
  carrier := Set.range evaluate
  one_mem' := ⟨(0,0,0), evaluate_one⟩
  mul_mem' := by
    rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩
    exact ⟨product s t, evaluate_mul s t⟩
  inv_mem' := by
    rintro _ ⟨s,rfl⟩
    exact ⟨inverse s, evaluate_inv s⟩
public theorem m24Sylow3Subgroup_card : Nat.card m24Sylow3Subgroup = 27 := by
  have he : Coordinates ≃ m24Sylow3Subgroup :=
    Equiv.ofBijective (fun s => ⟨evaluate s, ⟨s,rfl⟩⟩)
      ⟨fun _ _ h => evaluate_injective (congrArg Subtype.val h),
        fun ⟨_,s,hs⟩ => ⟨s, Subtype.ext hs⟩⟩
  rw [← Nat.card_congr he]
  simp

private theorem factorization_three : Nat.factorization 244823040 3 = 3 := by
  have hzero : padicValNat 3 9067520 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Nat.factorization_def 244823040 Nat.prime_three,
    show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]

/-- The concrete subgroup is Sylow by the 3-part of the established M24 order. -/
@[expose] public def m24Sylow3 : Sylow 3 M24 :=
  Sylow.ofCard m24Sylow3Subgroup (by
    rw [m24Sylow3Subgroup_card, m24_order, factorization_three]
    norm_num)

public theorem m24Sylow3_coe : (m24Sylow3 : Subgroup M24) = m24Sylow3Subgroup := rfl
public theorem m24Sylow3Subgroup_isNonabelian : ¬ IsMulCommutative m24Sylow3Subgroup := by
  intro h
  have hx : rankX ∈ m24Sylow3Subgroup := ⟨(1,0,0), by simp [evaluate]⟩
  have hy : rankY ∈ m24Sylow3Subgroup := ⟨(0,1,0), by simp [evaluate]⟩
  have he := (isMulCommutative_iff.mp h)
    (⟨rankX,hx⟩ : m24Sylow3Subgroup) ⟨rankY,hy⟩
  have hne : (rankX : Equiv.Perm (Fin 24)) * rankY ≠ rankY * rankX := by decide +kernel
  exact hne (congrArg (fun g : m24Sylow3Subgroup => (g.val : Equiv.Perm (Fin 24))) he)
end
end Sporadic.Mathieu
