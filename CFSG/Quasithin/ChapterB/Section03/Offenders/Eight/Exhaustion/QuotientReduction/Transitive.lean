module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.Full
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.QuotientReduction.CharacterBound

/-!
# The transitive branch of quotient necessity in degree eight

An abelian transitive permutation group has unique transporters. In degree
eight its order is eight; elementary abelian structure then makes every
nonidentity permutation a fixed-point-free involution, of positive sign.
The displacement bound excludes such a group from the deleted offenders.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(4),(6), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

open BinaryPermutation Representation.BinaryOffender
open BinaryPermutation.QuotientFixedSpace
open scoped IsMulCommutative

private theorem eval_injective_of_transitive
    {A : Subgroup (Equiv.Perm (Fin 8))} [IsMulCommutative A]
    (ht : ∀ x y : Fin 8, ∃ a : A, a.val x = y) (x : Fin 8) :
    Function.Injective (fun a : A => a.val x) := by
  intro a b hab
  apply Subtype.ext
  apply Equiv.ext
  intro y
  obtain ⟨c, rfl⟩ := ht x y
  calc
    a.val (c.val x) = c.val (a.val x) :=
      congrArg (fun g : A => g.val x) (mul_comm a c)
    _ = c.val (b.val x) := congrArg c.val hab
    _ = b.val (c.val x) :=
      congrArg (fun g : A => g.val x) (mul_comm c b)

/-- Transitivity supplies every clause of the degree-eight regular alternative. -/
theorem isRegularEight_of_transitive {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsElementaryTwo A) (ht : ∀ x y : Fin 8, ∃ a : A, a.val x = y) :
    IsRegularEight A := by
  classical
  let _ : IsElementaryAbelian 2 A := hA.2
  have hi := eval_injective_of_transitive ht
  have hc : Nat.card A = 8 := by
    have h := Nat.card_congr (Equiv.ofBijective (fun a : A => a.val (0 : Fin 8))
      ⟨hi 0, ht 0⟩)
    simpa using h
  refine ⟨hA, hc, ?_, ?_⟩
  · intro a ha
    rw [Equiv.Perm.mem_alternatingGroup]
    by_cases h1 : a = 1
    · simp [h1]
    have hn : ∀ x : Fin 8, a x ≠ x := by
      intro x hx
      have he := hi x (show (⟨a, ha⟩ : A).val x = (1 : A).val x from hx)
      exact h1 (congrArg Subtype.val he)
    have hf : IsEmpty (Function.fixedPoints a) := ⟨fun x => hn x.val x.property⟩
    rw [Equiv.Perm.sign_of_pow_two_eq_one (elemPow_eq_one_of_isElementaryAbelian a ha)]
    norm_num
    decide
  · intro x y
    obtain ⟨a, ha⟩ := ht x y
    exact ⟨a, ha, fun b hb => hi x (hb.trans ha.symm)⟩

theorem full_fixedCodim_eq_seven_of_transitive
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (ht : ∀ x y : Fin 8, ∃ a : A, a.val x = y) :
    fixedCodim (representation (Fin 8)) A = 7 := by
  have he : fixedSpace (representation (Fin 8)) A = constants (Fin 8) := by
    apply le_antisymm ?_ (constants_le_full_fixed A)
    intro v hv
    refine (mem_constants_iff v).mpr ⟨v 0, ?_⟩
    intro y
    obtain ⟨a, ha⟩ := ht 0 y
    have h := (mem_full_fixedSpace_iff A v).mp hv a.val a.property y
    rw [a.val.symm_apply_eq.mpr ha.symm] at h
    exact h.symm
  have h := fixedCodim_add_finrank (representation (Fin 8)) A
  rw [he, finrank_constants, finrank_full, Fintype.card_fin] at h
  omega

/-- Transitive elementary abelian groups cannot offend on the deleted module. -/
theorem not_isOffender_deleted_of_transitive {A : Subgroup (Equiv.Perm (Fin 8))}
    (ht : ∀ x y : Fin 8, ∃ a : A, a.val x = y) :
    ¬ IsOffender (deletedRepresentation (Fin 8)) A := by
  intro hA
  have hr := rank_eq_three_of_isRegularEight (isRegularEight_of_transitive hA.1 ht)
  have hb := displacementRank_le_rank hA.1 (0 : Fin 8)
  have hd := fixedCodim_deleted_add_displacementRank A (0 : Fin 8)
  rw [full_fixedCodim_eq_seven_of_transitive ht] at hd
  have ho := hA.2
  omega

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
