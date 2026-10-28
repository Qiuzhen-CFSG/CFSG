module

public import Theory.SpecificGroups.G2Five.AtlasBoundLocalPresentation
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# An obstruction to the proposed local presentation bound

The seven relators of `AtlasBoundLocalPresentation` admit a quotient isomorphic
to the symmetric group on ten points. Consequently they cannot imply the
proposed finite order bound of 1500000.

The quotient sends the generators to the inverses of the permutations
`(1,2,3,4,5)(6,7,8,9,10)` and `(1,8,10,4,3,2,7,5,9,6)`. Inverting their GAP
right-action permutations implements Lean's left-action multiplication convention.
All seven relations are checked by kernel reduction. Explicit words for the nine
adjacent transpositions prove surjectivity, using Mathlib's generation theorem.
The cardinality of the quotient is `10! = 3628800`.

Source: an explicit counterexample found for the literal relators in
`AtlasBoundLocalPresentation.lean`. GAP supplied candidate permutations and words;
no GAP result is trusted in the proof below. This does not identify or assume
finiteness of the ambient ATLAS presentation.
-/

namespace G2Five.AtlasPresentation

private def counterX : Equiv.Perm (Fin 10) where
  toFun := ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8]
  invFun := ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5]
  left_inv := by decide
  right_inv := by decide

private def counterY : Equiv.Perm (Fin 10) where
  toFun := ![5, 2, 3, 9, 6, 8, 1, 0, 4, 7]
  invFun := ![7, 6, 1, 2, 8, 0, 4, 9, 5, 3]
  left_inv := by decide
  right_inv := by decide

private def counterGenerator : Bool → Equiv.Perm (Fin 10) :=
  fun b => if b then counterY else counterX

set_option maxRecDepth 4096 in
private theorem counterRelations (i : Fin 7) :
    FreeGroup.lift counterGenerator (boundLocalRelator i) = 1 := by
  fin_cases i <;>
    simp only [boundLocalRelator, map_pow, map_mul, map_inv,
      boundLocalX, boundLocalY, FreeGroup.lift_apply_of] <;> decide

private def counterHom : BoundLocalPresentation →* Equiv.Perm (Fin 10) :=
  PresentedGroup.toGroup (by rintro _ ⟨i, rfl⟩; exact counterRelations i)

private theorem counterHom_generator (b : Bool) :
    counterHom (boundLocalGenerator b) = counterGenerator b :=
  PresentedGroup.toGroup.of _


/-- Words for the adjacent transpositions in the quotient. -/
private def swapWord {G : Type*} [Group G] (x y : G) : Fin 9 → G := fun
  | 0 => x * y⁻¹ * x * y * x * y⁻¹ * x * y * (x ^ 2) * (y⁻¹ ^ 2) * x * y⁻¹ * (x⁻¹ ^ 2) * (y⁻¹ ^ 2)
      * x⁻¹
  | 1 => y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x * y * x * y * (x ^ 2) * y * x
      * y⁻¹ * x⁻¹ * y * x⁻¹ * y⁻¹ * x⁻¹ * y * x * (y⁻¹ ^ 2) * x * y⁻¹ * (x⁻¹ ^ 2) * (y⁻¹ ^ 2) *
      (x⁻¹ ^ 2) * y * x * (y⁻¹ ^ 2) * x * y⁻¹
  | 2 => y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x * y * x * y * (x ^ 2) * y *
      (x ^ 2) * y⁻¹ * x * y * x * (y⁻¹ ^ 2) * x⁻¹ * y⁻¹ * x * (y⁻¹ ^ 2) * x * y⁻¹ * (x⁻¹ ^ 2) *
      (y⁻¹ ^ 2) * x * y * (x ^ 2) * y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y * x * y
  | 3 => y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x * y * x⁻¹ * y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x⁻¹ *
      y⁻¹ * x⁻¹ * y * (x⁻¹ ^ 3) * y⁻¹ * (x ^ 2) * y⁻¹ * (x⁻¹ ^ 3) * y⁻¹ * x * y * (x ^ 2) * y⁻¹ *
      x⁻¹ * y⁻¹ * x⁻¹ * (y ^ 3) * x * (y ^ 2) * x⁻¹ * y⁻¹ * (x ^ 2) * y * x⁻¹ * y
  | 4 => y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x * y * x⁻¹ * y⁻¹ *
      (x⁻¹ ^ 3) * y * x * y * x * y * (x ^ 2) * y * x⁻¹ * (y ^ 2) * x⁻¹ * y⁻¹ * x * (y ^ 2) * x *
      y * x * y⁻¹
  | 5 => y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x * y * x * y * (x ^ 2) * y *
      (x ^ 2) * y⁻¹ * x * y * x * y⁻¹ * x * y * x⁻¹ * y * x * y * x * (y ^ 3) * x * y⁻¹ * x⁻¹ *
      (y⁻¹ ^ 3) * (x ^ 2) * (y⁻¹ ^ 2) * (x⁻¹ ^ 2)
  | 6 => (y ^ 2) * x * y * x * y * x * y⁻¹
  | 7 => y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * (y⁻¹ ^ 2) * x * y * x * y⁻¹ * x * y * (x⁻¹ ^ 2) * y⁻¹ * (x ^ 2) *
      y⁻¹ * (x⁻¹ ^ 3) * (y⁻¹ ^ 3) * x * y⁻¹ * (x ^ 2) * (y⁻¹ ^ 2) * x⁻¹
  | _ => y⁻¹ * (x⁻¹ ^ 2) * y⁻¹ * x⁻¹ * y * x * y * x⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * x * y * x * y⁻¹ * x * y
      * (x ^ 2) * (y⁻¹ ^ 2) * x * y⁻¹ * (x⁻¹ ^ 2) * (y⁻¹ ^ 2) * x⁻¹ * y * x⁻¹ * (y ^ 2) * x⁻¹ *
      y⁻¹ * (x ^ 2) * (y⁻¹ ^ 2) * x⁻¹ * y⁻¹ * x⁻¹

private theorem counterHom_swapWord (i : Fin 9) :
    counterHom (swapWord (boundLocalGenerator false) (boundLocalGenerator true) i) =
      swapWord (counterGenerator false) (counterGenerator true) i := by
  fin_cases i <;> simp [swapWord, counterHom_generator]

set_option maxRecDepth 4096 in
private theorem counterSwap (i : Fin 9) :
    swapWord (counterGenerator false) (counterGenerator true) i =
      Equiv.swap i.castSucc i.succ := by
  fin_cases i <;> decide

private theorem counterHom_surjective : Function.Surjective counterHom := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  have htop : Subgroup.closure
      (Set.range fun i : Fin 9 => Equiv.swap i.castSucc i.succ) = ⊤ :=
    Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 9)
  rw [← htop, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨swapWord (boundLocalGenerator false) (boundLocalGenerator true) i,
    (counterHom_swapWord i).trans (counterSwap i)⟩

/-- The exact seven-relator presentation cannot have the requested finite bound. -/
public theorem boundLocalPresentation_not_finite_card_le :
    ¬ (Finite BoundLocalPresentation ∧ Nat.card BoundLocalPresentation ≤ 1500000) := by
  rintro ⟨hfin, hcard⟩
  let := hfin
  have h := Nat.card_le_card_of_surjective counterHom counterHom_surjective
  have hn : Nat.card (Equiv.Perm (Fin 10)) = 3628800 := by
    rw [Nat.card_perm, Nat.card_fin]
    decide
  have : 3628800 ≤ 1500000 := hn ▸ h.trans hcard
  contradiction

end G2Five.AtlasPresentation
