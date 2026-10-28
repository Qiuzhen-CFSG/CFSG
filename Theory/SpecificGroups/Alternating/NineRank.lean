module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.ZMod.Basic

/-!
# A rank-three elementary abelian subgroup of A9

Independent translations on three blocks of three points embed C3^3 into A9.
The permutations are even because their cubes are trivial and the sign group
has exponent two. Faithfulness is checked on one point in each block. The
resulting elementary abelian subgroup of order 27 witnesses 3-rank at least
three. Two intersecting three-cycles also give explicit noncommuting elements.

This supplies the odd-prime rank obstruction needed in Aschbacher--Smith,
*The Classification of Quasithin Groups*, A.2.15(2) and A.2.19. The argument
uses actual permutations, without a group-family label or an assumed rank.
-/

public section
namespace Theory.AlternatingNine

private abbrev E27 := Multiplicative (Fin 3 → ZMod 3)

private theorem cube_eq_one (a : E27) : a ^ 3 = 1 := by
  change 3 • a.toAdd = 0
  ext i
  change 3 • a.toAdd i = 0
  simp only [nsmul_eq_mul]
  exact zero_mul _

private def blockShift (a : E27) : Equiv.Perm (Fin 3 × ZMod 3) where
  toFun x := (x.1, x.2 + a.toAdd x.1)
  invFun x := (x.1, x.2 - a.toAdd x.1)
  left_inv x := by simp
  right_inv x := by simp

private def blockShiftHom : E27 →* Equiv.Perm (Fin 3 × ZMod 3) where
  toFun := blockShift
  map_one' := by ext x <;> simp [blockShift]
  map_mul' a b := by
    ext x <;> simp [blockShift, add_comm, add_left_comm]

private theorem blockShiftHom_injective : Function.Injective blockShiftHom := by
  intro a b h
  apply Multiplicative.toAdd.injective
  funext i
  have hi := congrArg (fun p : Equiv.Perm (Fin 3 × ZMod 3) => (p (i, 0)).2) h
  simpa [blockShiftHom, blockShift] using hi

private theorem blockShift_even (a : E27) : blockShiftHom a ∈ alternatingGroup _ := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  have h3 : (Equiv.Perm.sign (blockShiftHom a)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, cube_eq_one, map_one, map_one]
  have h2 : (Equiv.Perm.sign (blockShiftHom a)) ^ 2 = 1 := by
    simp [pow_two, Int.units_mul_self]
  simpa only [pow_succ, h2, one_mul] using h3

private noncomputable def ninePoints : (Fin 3 × ZMod 3) ≃ Fin 9 :=
  (Fintype.equivFin _).trans (finCongr (by decide))

private noncomputable def embedding : E27 →* alternatingGroup (Fin 9) :=
  ninePoints.altCongrHom.toMonoidHom.comp
    (blockShiftHom.codRestrict (alternatingGroup _) blockShift_even)

private theorem embedding_injective : Function.Injective embedding := by
  intro a b h
  apply blockShiftHom_injective
  exact congrArg Subtype.val (ninePoints.altCongrHom.injective h)

/-- Three independent disjoint 3-cycles witness the lower bound. -/
theorem three_le_primeRank : 3 ≤ primeRank 3 (alternatingGroup (Fin 9)) := by
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 3) cube_eq_one ?_
    embedding embedding_injective
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
  norm_num [Nat.card_zmod]

/-- Two intersecting 3-cycles show that A9 is nonabelian. -/
theorem noncommuting : ∃ a b : alternatingGroup (Fin 9), a * b ≠ b * a := by
  let a : alternatingGroup (Fin 9) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩
  let b : alternatingGroup (Fin 9) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
  refine ⟨a, b, ?_⟩
  intro h
  have hh := congrArg (fun p : alternatingGroup (Fin 9) => (p : Equiv.Perm (Fin 9)) 0) h
  exact (by decide : (1 : Fin 9) ≠ 2) hh

end Theory.AlternatingNine
