module

public import Theory.SpecificGroups.Classical.LinearFundamental

/-!
# A rank-four rectangular subgroup in a linear involution centralizer

On four coordinates use the matrices with identity diagonal blocks and an
arbitrary 2-by-2 upper-right block. Their additive parameter group is F⁴.
Extend these matrices by the identity on d positive coordinates and use
minus the identity on the first four coordinates as the involution. The
existing faithful projective block embedding proves both noncentrality of
the involution and injectivity of the rectangle after the scalar quotient.
The index equivalence gives the literal PSL_(4+d)(F) matrix model.

For d > 0 this construction works in every odd characteristic, including
fields of orders 3 and 9, with no multiplier or dimension restriction.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.2.17, printed p.39.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup.LinearRankFourCentralizer
open LinearFundamental

variable (F : Type*) [Field F]

def rectangle : Multiplicative (Matrix (Fin 2) (Fin 2) F) →*
    SpecialLinearGroup (Fin 2 ⊕ Fin 2) F where
  toFun a := ⟨fromBlocks 1 a.toAdd 0 1, by simp⟩
  map_one' := Subtype.ext fromBlocks_one
  map_mul' a b := by
    apply Subtype.ext
    change fromBlocks 1 (a.toAdd + b.toAdd) 0 1 =
      fromBlocks 1 a.toAdd 0 1 * fromBlocks 1 b.toAdd 0 1
    simp [fromBlocks_multiply, add_comm]

theorem rectangle_injective : Function.Injective (rectangle F) := by
  intro a b h
  exact congrArg (fun g : SpecialLinearGroup (Fin 2 ⊕ Fin 2) F =>
    toBlocks₁₂ g.val) h

noncomputable def fourBlock (d : ℕ) : SpecialLinearGroup (Fin 2 ⊕ Fin 2) F →*
    PSL(4 + d, F) :=
  (projectiveReindex (F := F)
    ((Equiv.sumCongr (finSumFinEquiv (m := 2) (n := 2)) (Equiv.refl (Fin d))).trans
      (finSumFinEquiv (m := 4) (n := d)))).toMonoidHom.comp
    (projectLeft (m := Fin 2 ⊕ Fin 2) (n := Fin d))

theorem fourBlock_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (fourBlock F d) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact (projectiveReindex _).injective.comp projectLeft_injective

local instance : Fact (Even (Fintype.card (Fin 2 ⊕ Fin 2))) := ⟨by decide⟩

noncomputable def involution (d : ℕ) : PSL(4 + d, F) := fourBlock F d (-1)

theorem involution_order {d p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hd : 0 < d) : orderOf (involution F d) = 2 := by
  apply orderOf_eq_prime _ _
  · change fourBlock F d (-1) ^ 2 = 1
    rw [← map_pow]
    simp [pow_two]
  · intro he
    have hh := fourBlock_injective F hd (he.trans (map_one _).symm)
    have heq := congrArg (fun a : SpecialLinearGroup (Fin 2 ⊕ Fin 2) F =>
      a.val (Sum.inl 0) (Sum.inl 0)) hh
    have : Fact (2 < p) := ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)⟩
    exact CharP.neg_one_ne_one F p (by simpa using heq)

noncomputable def elementaryCentralizer (d : ℕ) :
    Multiplicative (Matrix (Fin 2) (Fin 2) F) →*
      Subgroup.centralizer ({involution F d} : Set PSL(4 + d, F)) :=
  ((fourBlock F d).comp (rectangle F)).codRestrict _ (fun a => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change fourBlock F d (rectangle F a) * fourBlock F d (-1) =
      fourBlock F d (-1) * fourBlock F d (rectangle F a)
    rw [← map_mul, ← map_mul]
    congr 1
    simp)

theorem elementaryCentralizer_injective {d : ℕ} (hd : 0 < d) :
    Function.Injective (elementaryCentralizer F d) := by
  intro a b h
  exact rectangle_injective F (fourBlock_injective F hd (congrArg Subtype.val h))

theorem elementary_exponent (p : ℕ) [CharP F p]
    (a : Multiplicative (Matrix (Fin 2) (Fin 2) F)) : a ^ p = 1 := by
  change p • a.toAdd = 0
  ext i j
  simp [nsmul_eq_mul]

omit [Field F] in
theorem elementary_card [Finite F] {p e : ℕ} (hF : Nat.card F = p ^ e) :
    Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) F)) = p ^ (4 * e) := by
  rw [Nat.card_congr Multiplicative.toAdd]
  change Nat.card (Fin 2 → Fin 2 → F) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, hF, ← pow_mul, ← pow_mul]
  congr 1
  omega

end Matrix.SpecialLinearGroup.LinearRankFourCentralizer
