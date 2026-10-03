module

public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas

/-!
# Restricting a coprime commutator to a containing subgroup

For a coprime action on a finite solvable group `P`, suppose an invariant
subgroup `C` contains `[P,A]`. Then `[C,A]=[P,A]`, after mapping to `P`.
Indeed `[P,A]=[P,A,A] ≤ [C,A]`, and the reverse inclusion is immediate.
In particular the internal action commutator has normal image in `P`.

This is the coprime commutator identity, specialized to an intermediate
invariant subgroup. It separates ambient containment from internal structure
in the normal-subgroup construction of MacWilliams, Trans. AMS 150 (1970),
§3(ii)–(iv), pp.366–367.
-/

open Subgroup

/-- An invariant subgroup containing the full coprime commutator has the same
action commutator as the ambient group. -/
public theorem commutatorAction_map_eq_of_coprime_of_le
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [MulDistribMulAction A P] (C : Subgroup P) [IsInvariant A P C]
    (hsolv : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hcontain : commutatorAction A P ≤ C) :
    (commutatorAction A C).map C.subtype = commutatorAction A P := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, commutatorAction_eq_closure, closure_le]
    rintro x ⟨a, c, rfl⟩
    change (c : P)⁻¹ * (a • (c : P)) ∈ commutatorAction A P
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨a, (c : P), rfl⟩
  · rw [← commutatorAction₂_eq_commutatorAction_of_solvable_coprime hsolv hcop]
    change closure {x : P | ∃ a : A, ∃ g ∈ commutatorAction A P,
      x = g⁻¹ * (a • g)} ≤ _
    rw [closure_le]
    rintro x ⟨a, g, hg, rfl⟩
    let c : C := ⟨g, hcontain hg⟩
    refine ⟨c⁻¹ * (a • c), ?_, rfl⟩
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨a, c, rfl⟩

/-- Ambient containment of a coprime commutator supplies normality of its
internal realization. -/
public theorem commutatorAction_map_normal_of_coprime_of_le
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [MulDistribMulAction A P] (C : Subgroup P) [IsInvariant A P C]
    (hsolv : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hcontain : commutatorAction A P ≤ C) :
    ((commutatorAction A C).map C.subtype).Normal := by
  rw [commutatorAction_map_eq_of_coprime_of_le C hsolv hcop hcontain]
  exact commutatorAction_normal
