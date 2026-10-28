module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy

/-!
# Involution fusion and noncommuting Sylow roots in even PSL₃

For every finite field of order 2^n, n>0, projective involutions form one
class. Place an involution in the actual unitriangular Sylow, then apply the
published special-linear root conjugacy. This also covers n=1 without a
new enumeration or exceptional-isomorphism argument.

The two unitriangular elements with coordinates (1,0,0) and (0,1,0) square
to one and do not commute: their products differ in the highest-root
coordinate. The projective embedding is injective, and Sylow conjugacy
transports this pair into any supplied Sylow.

Source: the type A2 part of Aschbacher--Smith 1.1.5(3)(a),(b), used in the
Bender inspection on printed pp.519--520 (1 March 2004 manuscript).
-/

public section
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Theory.GroupTheory.EvenCharacteristicInvolutionFusion
variable (F : Type*) [Field F] [Finite F]

private theorem char_two {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    ringChar F = 2 := by
  let := Fintype.ofFinite F
  apply FiniteField.even_card_iff_char_two.mpr
  rw [← Nat.card_eq_fintype_card, hF]
  simp [Nat.pow_mod, Nat.ne_of_gt hn]

private theorem psl3_isConj_root {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    IsConj t (Matrix.PSL3.EvenInnerCentralizers.root F) := by
  let : CharP F 2 := ringChar.of_eq (char_two F hn hF)
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have htn : t ≠ 1 := by intro h; simp [h] at ht
  obtain ⟨y, hty⟩ :=
    (Matrix.PSL3.LinearThree.unipotentSylow F hn hF).exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa only [pow_one] using ht)
  have hy : (y : PSL(3,F)) ∈ (projective F).range :=
    (Matrix.PSL3.LinearThree.projective_range F).ge y.property
  obtain ⟨u, hu⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp hty
  have hconj : MulAut.conj g t = projective F u := hg.trans hu.symm
  have hu2 : u ^ 2 = 1 := by
    apply projective_injective F
    rw [map_pow, ← hconj, ← map_pow, ht2, map_one, map_one]
  have hun : u ≠ 1 := by
    intro he
    apply htn
    apply (MulAut.conj g).injective
    rw [hconj, he, map_one, map_one]
  have hroot : IsConj (projective F u) (Matrix.PSL3.EvenInnerCentralizers.root F) :=
    (Matrix.PSL3.projection F).map_isConj
      (Matrix.PSL3.EvenInnerCentralizers.specialLinear_isConj_root F u hun hu2)
  exact hty.trans (hu ▸ hroot)

/-- Unique involution fusion in every even-field PSL₃, including PSL₃(2). -/
theorem psl3_involutions_isConj {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (a b : PSL(3,F)) (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b :=
  (psl3_isConj_root F hn hF a ha).trans (psl3_isConj_root F hn hF b hb).symm

/-- Every supplied Sylow of even-field PSL₃ contains noncommuting involutions. -/
theorem psl3_sylow_noncommuting_involutions {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (P : Sylow 2 PSL(3,F)) :
    ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b := by
  let : CharP F 2 := ringChar.of_eq (char_two F hn hF)
  let a : U F := ⟨1, 0, 0⟩
  let b : U F := ⟨0, 1, 0⟩
  have ha : orderOf a = 2 := orderOf_eq_prime
    ((square_eq_one_iff F a).mpr (Or.inr rfl)) (fun h => one_ne_zero (congrArg U.x h))
  have hb : orderOf b = 2 := orderOf_eq_prime
    ((square_eq_one_iff F b).mpr (Or.inl rfl)) (fun h => one_ne_zero (congrArg U.y h))
  have hab : ¬Commute a b := by
    intro hc
    have he := (mul_comm_iff F a b).mp hc.eq
    norm_num [a, b] at he
  let R := Matrix.PSL3.LinearThree.unipotentSylow F hn hF
  let e : U F ≃* P := (Matrix.PSL3.LinearThree.unipotentEquiv F).trans (R.equiv P)
  refine ⟨e a, e b, (e.orderOf_eq a).trans ha, (e.orderOf_eq b).trans hb, ?_⟩
  intro hc
  exact hab (e.injective (by simpa only [map_mul] using hc.eq))

end Theory.GroupTheory.EvenCharacteristicInvolutionFusion
