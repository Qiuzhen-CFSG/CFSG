module
public import Theory.SpecificGroups.SymplecticSix.BinarySylowFrattini
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.CharP.Lemmas

/-!
# Four Frattini generators for the binary symplectic six-space

Four explicit symplectic matrices and their first/fourth product lie in
one upper unitriangular two-group, in the basis e₁,e₂,e₃,f₃,f₂,f₁.
Their five squares have thirty-two distinct ordered products. Hence a
Sylow subgroup of order 512 has Frattini quotient of order at most sixteen.
The construction extends the four-square calculation in Chapter 11's
`OddNormalizer/BinarySixFrattini.lean`, using the same matrices and form.
Only the four form identities, upper-triangular memberships and thirty-two
square words are checked. No enumeration of the ambient group is used.

The exterior odd-normalizer consumer applies the literal field and central
quotient comparisons, then uses the missing prime divisor 31 in GL₄(2).
Source: Aschbacher--Smith 4.4.10--11, printed p.621, using I.3.1.
-/

open Subgroup Matrix
open Theory.SpecificGroups.SymplecticSix
namespace Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen
private def orderEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6 :=
  (Equiv.sumCongr (Equiv.refl _) (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩)).trans finSumFinEquiv
private def ordered : Sp (ZMod 2) →* Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) orderEquiv).toMonoidHom.comp
    (Matrix.symplecticGroup (Fin 3) (ZMod 2)).subtype
private theorem ordered_injective : Function.Injective ordered :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) orderEquiv).injective.comp Subtype.val_injective

private theorem strictly_upper_pow_entry (M : Matrix (Fin 6) (Fin 6) (ZMod 2))
    (hM : ∀ i j, j ≤ i → M i j = 0) (k : ℕ) :
    ∀ i j : Fin 6, j.val < i.val + k → (M ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j hij
    have hne : i ≠ j := by intro he; subst j; omega
    simp [hne]
  | succ k ih =>
    intro i j hij
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ≤ i
    · rw [hM i l hl, zero_mul]
    · rw [ih l j (by have := lt_of_not_ge hl; omega), mul_zero]

private def IsUpper (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1
private theorem upper_one : IsUpper 1 := ⟨Matrix.blockTriangular_one, by simp⟩
private theorem upper_mul {A B : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hA : IsUpper A) (hB : IsUpper B) : IsUpper (A*B) := by
  refine ⟨hA.1.mul hB.1, ?_⟩
  intro i
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2, hB.2, one_mul]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hA.1 hj, zero_mul]
    · rw [hB.1 hj, mul_zero]
  · simp
private theorem upper_pow {A : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hA : IsUpper A) (k : ℕ) : IsUpper (A^k) := by
  induction k with
  | zero => simpa using upper_one
  | succ k ih => simpa only [pow_succ] using upper_mul ih hA
private theorem upper_pow_eight {A : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hA : IsUpper A) : A ^ 8 = 1 := by
  have hstrict : ∀ i j, j ≤ i → (A - 1) i j = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le hij with he | he
    · subst j; simp [hA.2]
    · simp [hA.1 he, ne_of_gt he]
  have hnil : (A-1)^8 = 0 := by
    ext i j
    exact strictly_upper_pow_entry (A-1) hstrict 8 i j (by have := j.isLt; omega)
  let : CharP (Matrix (Fin 6) (Fin 6) (ZMod 2)) 2 := ⟨fun k => by
    simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
      CharP.cast_eq_zero_iff (ZMod 2) 2 k, forall_const]⟩
  have hp := add_pow_char_pow_of_commute 2 3 (Commute.one_right (A-1))
  norm_num only [sub_add_cancel, show 2^3 = (8 : ℕ) from rfl, hnil, one_pow, zero_add] at hp
  exact hp
private def upper : Subgroup (Sp (ZMod 2)) where
  carrier := {g | IsUpper (ordered g)}
  one_mem' := by change IsUpper (ordered 1); simpa only [map_one] using upper_one
  mul_mem' := by
    intro a b ha hb
    change IsUpper (ordered (a*b))
    rw [map_mul]
    exact upper_mul ha hb
  inv_mem' := by
    intro g hg
    have hp : g^8 = 1 := ordered_injective (by
      simpa only [map_pow, map_one] using upper_pow_eight hg)
    have he : g^7 = g⁻¹ := eq_inv_of_mul_eq_one_left (by rw [←pow_succ, hp])
    change IsUpper (ordered (g⁻¹))
    rw [←he, map_pow]
    exact upper_pow hg 7
private theorem upper_two : IsPGroup 2 upper := by
  intro g
  refine ⟨3, ?_⟩
  apply Subtype.ext
  apply ordered_injective
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one,
    show 2^3 = (8 : ℕ) from rfl] using upper_pow_eight g.property

private def coordinate : Fin 3 ⊕ Fin 3 → Fin 6 :=
  Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + 3, by omega⟩)
private def liftMatrix (k : Fin 4) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fun i j => (
    ![![![1,0,0,0,0,0],![0,1,1,0,0,1],![0,0,1,0,0,1],![0,0,0,1,0,0],![0,0,0,0,1,0],![0,0,0,0,1,1]],
      ![![1,0,0,0,0,1],![0,1,1,1,0,0],![0,0,1,1,0,0],![0,0,0,1,0,0],![0,0,0,0,1,0],![0,0,0,0,1,1]],
      ![![1,0,1,0,0,1],![0,1,0,0,0,0],![0,0,1,0,0,1],![0,0,0,1,0,0],![0,0,0,0,1,0],![0,0,0,1,0,1]],
      ![![1,1,0,0,0,1],![0,1,0,0,0,1],![0,0,1,0,1,0],![0,0,0,1,0,0],![0,0,0,1,1,0],![0,0,0,0,0,1]]] : Fin 4 → Fin 6 → Fin 6 → ZMod 2) k (coordinate i) (coordinate j)
private theorem liftMatrix_mem (k : Fin 4) :
    liftMatrix k ∈ Matrix.symplecticGroup (Fin 3) (ZMod 2) := by
  have h : ∀ k : Fin 4, liftMatrix k * Matrix.J _ _ * (liftMatrix k).transpose = Matrix.J _ _ := by
    decide +kernel
  exact h k
private def liftElement (k : Fin 4) : Sp (ZMod 2) := ⟨liftMatrix k, liftMatrix_mem k⟩
private theorem lift_upper (k : Fin 4) : liftElement k ∈ upper := by
  have h : ∀ k : Fin 4, IsUpper (ordered (liftElement k)) := by
    change ∀ k : Fin 4, (∀ i j : Fin 6, j < i → ordered (liftElement k) i j = 0) ∧
      ∀ i : Fin 6, ordered (liftElement k) i i = 1
    change ∀ k : Fin 4,
      (∀ i j : Fin 6, j < i → liftMatrix k (orderEquiv.symm i) (orderEquiv.symm j) = 0) ∧
      ∀ i : Fin 6, liftMatrix k (orderEquiv.symm i) (orderEquiv.symm i) = 1
    decide +kernel
  exact h k
private def squareWord (i : Fin 32) : Sp (ZMod 2) :=
  ((liftElement 0)^2)^(i.val%2) * ((liftElement 1)^2)^((i.val/2)%2) *
    ((liftElement 2)^2)^((i.val/4)%2) * ((liftElement 3)^2)^((i.val/8)%2) *
    ((liftElement 0 * liftElement 3)^2)^((i.val/16)%2)
private theorem squareWord_injective : Function.Injective squareWord := by
  have h : Function.Injective (fun i => (squareWord i).val) := by decide +kernel
  exact fun a b hab => h (congrArg Subtype.val hab)

/-- The five displayed squares force thirty-two elements in every Sylow Frattini subgroup. -/
public theorem frattini_card_le_sixteen (P : Sylow 2 (Sp (ZMod 2))) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  obtain ⟨Q,hQ⟩ := upper_two.exists_le_sylow
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (P.equiv Q)]
  let x : Fin 4 → Q := fun k => ⟨liftElement k,hQ (lift_upper k)⟩
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  have hx (k : Fin 4) : x k ^ 2 ∈ frattini Q :=
    pth_power_mem_frattini_of_isPGroup (p := 2) (x k)
  let w (i : Fin 32) : Q :=
    (x 0 ^ 2)^(i.val%2) * (x 1 ^ 2)^((i.val/2)%2) *
      (x 2 ^ 2)^((i.val/4)%2) * (x 3 ^ 2)^((i.val/8)%2) *
      ((x 0 * x 3)^2)^((i.val/16)%2)
  have hw (i : Fin 32) : w i ∈ frattini Q :=
    mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (hx 0) _) (pow_mem (hx 1) _))
      (pow_mem (hx 2) _)) (pow_mem (hx 3) _))
      (pow_mem (pth_power_mem_frattini_of_isPGroup (p := 2) (x 0 * x 3)) _)
  let f : Fin 32 → frattini Q := fun i => ⟨w i,hw i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply squareWord_injective
    exact congrArg (fun z : frattini Q => (z.val : Sp (ZMod 2))) he
  have h32 : 32 ≤ Nat.card (frattini Q) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have hcard : Nat.card Q ≤ 512 := by
    obtain ⟨k,hk⟩ := Q.isPGroup'.exists_card_eq
    have hd := (Q : Subgroup (Sp (ZMod 2))).card_subgroup_dvd_card
    rw [hk,card_sp_of_card_two (by simp)] at hd
    have hk9 : k ≤ 9 := by
      by_contra! h
      have hd' : 2 ^ 10 ∣ 1451520 := (pow_dvd_pow 2 (by omega : 10 ≤ k)).trans hd
      norm_num at hd'
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk9
  have hprod := card_eq_card_quotient_mul_card_subgroup (frattini Q)
  nlinarith

/-- Transport the bound through the actual binary field and projective marking. -/
public theorem frattini_card_le_sixteen_of_equiv {A F : Type*}
    [Group A] [Finite A] [Field F] [Finite F]
    (hF : Nat.card F = 2) (e : A ≃* PSp F) (P : Sylow 2 A) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  let a : A ≃* Sp (ZMod 2) :=
    (e.trans (pspFieldEquivZModTwo F hF)).trans EvenProjective.equiv.symm
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let b : P ≃* Q := a.subgroupMap (P : Subgroup A)
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr b]
  exact frattini_card_le_sixteen Q

end Theory.SpecificGroups.SymplecticSix.BinaryFrattiniSixteen
