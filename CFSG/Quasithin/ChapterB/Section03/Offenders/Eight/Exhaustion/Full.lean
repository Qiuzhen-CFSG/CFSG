module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.PairNormalForm
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Exhaustion.CoreBound
public import Theory.GroupAction.AbelianPermutationOrbitBound
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace

/-!
# Necessity in the degree-eight offender classification

On the full permutation module the dimension of the fixed space is the number
of orbits. The abelian permutation-group bound makes the offender inequality
an equality. Its equality case forces independent swaps on two-point orbits,
and cycle-type conjugacy gives the actual disjoint-transposition normal form.

This establishes the full-module necessity direction of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Proposition B.3.2(4), printed
pp. 83–84 (1 March 2004 manuscript). The core and quotient necessity directions
are separate obligations; they do not follow by commuting fixed spaces with
quotients.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.EightExhaustion

open BinaryPermutation Representation.BinaryOffender

/-- The full permutation module has no strong elementary abelian offenders. -/
theorem rank_le_fixedCodim_full {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsElementaryTwo A) : rank A ≤ fixedCodim (representation (Fin 8)) A := by
  let _ : IsElementaryAbelian 2 A := hA.2
  apply (Nat.pow_le_pow_iff_right (a := 2) (by decide)).mp
  rw [← hA.card_eq_two_pow_rank, fixedCodim_full_eq_card_sub_card_orbits]
  exact AbelianPermutation.card_le_two_pow_degree_sub_orbits A

/-- Full-module offenders have independent singleton and pair orbits. -/
theorem pair_orbits_of_isOffender_full {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (representation (Fin 8)) A) :
    (∀ x : Fin 8, Nat.card (MulAction.orbit A x) ≤ 2) ∧
      (∀ x y : Fin 8, y ∈ MulAction.orbit A x → Equiv.swap x y ∈ A) := by
  let _ : IsElementaryAbelian 2 A := hA.1.2
  have heq := le_antisymm hA.2 (rank_le_fixedCodim_full hA.1)
  apply AbelianPermutation.pair_orbits_of_card_eq A
  rw [← fixedCodim_full_eq_card_sub_card_orbits, heq]
  exact hA.1.card_eq_two_pow_rank

/-- Every full-module offender is conjugate to an actual `A_m`, `1 ≤ m ≤ 4`. -/
theorem caseAFamily_of_isOffender_full {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (representation (Fin 8)) A) : CaseAFamily 8 A := by
  obtain ⟨hsmall, hswap⟩ := pair_orbits_of_isOffender_full hA
  exact caseAFamily_of_pair_orbits rfl A hA.1.1 hsmall hswap

/-- B.3.2(4), necessity on the full module in degree eight. -/
theorem caseAFamily_of_isBestOffender_full {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsBestOffender (representation (Fin 8)) A) : CaseAFamily 8 A :=
  caseAFamily_of_isOffender_full (hA.isOffender _)

/-- A core offender with a common fixed coordinate already belongs to case (a). -/
theorem caseAFamily_of_isOffender_core_of_fixed_point
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (coreRepresentation (Fin 8)) A)
    {x : Fin 8} (hx : ∀ a ∈ A, a x = x) : CaseAFamily 8 A := by
  apply caseAFamily_of_isOffender_full
  refine ⟨hA.1, ?_⟩
  rw [← fixedCodim_core_eq_full_of_fixed_point hx]
  exact hA.2

/-- Outside case (a), a core offender has no common fixed coordinate. -/
theorem no_fixed_point_of_isOffender_core_of_not_caseA
    {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsOffender (coreRepresentation (Fin 8)) A) (hn : ¬ CaseAFamily 8 A) :
    ∀ x : Fin 8, ∃ a ∈ A, a x ≠ x := by
  intro x
  by_contra! hx
  exact hn (caseAFamily_of_isOffender_core_of_fixed_point hA hx)

end CFSG.Quasithin.ChapterB.Offenders.EightExhaustion
