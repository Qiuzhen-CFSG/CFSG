module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.DualFiltration.Data

/-!
# Upper triangular blocks of the dual induced flag

The saved adapted matrices preserve the prefixes of lengths 45 and 51.
Their diagonal blocks equal the published 45-, 6-, and 15-dimensional
factor matrices. Bounds and entry identities are kernel checked.
Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16;
provenance: `../source/README.md`.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag
def cut : ℕ → ℕ
  | 0 => 0
  | 1 => 45
  | 2 => 51
  | _ => 66
lemma cut_zero : cut 0 = 0 := rfl
lemma cut_last : cut 3 = 66 := rfl
lemma cut_le (m : ℕ) : cut m ≤ 66 := by
  rcases m with _ | _ | _ | m <;> simp [cut]
lemma cut_step (t : Fin 3) : cut t.val < cut (t.val+1) ∧ cut (t.val+1) ≤ 66 := by
  fin_cases t <;> decide
lemma cut_dimension (t : Fin 3) : cut t.val + factorDimension t = cut (t.val+1) := by
  fin_cases t <;> decide
def blockIndex (t : Fin 3) (x : Fin (factorDimension t)) : Fin 66 :=
  ⟨cut t.val + x.val, by have := cut_dimension t; have := cut_le (t.val+1); omega⟩
private instance blockRow (t : Fin 3) (a : Fin 2) (j : Fin (factorDimension t)) :
    Decidable (∀ i : Fin (factorDimension t),
      adaptedMatrix a (blockIndex t i) (blockIndex t j) = factorMatrix t a i j) :=
  Fintype.decidableForallFintype
set_option Elab.async false in
lemma factor_block : ∀ (t : Fin 3) (a : Fin 2) (j i : Fin (factorDimension t)),
    adaptedMatrix a (blockIndex t i) (blockIndex t j) = factorMatrix t a i j := by decide +kernel
set_option Elab.async false in
lemma packed_upper : ∀ (m : Fin 3) (a : Fin 2) (j : Fin 66),
    j.val < cut m.val → adaptedColumns a j < 2^(2*cut m.val) := by decide +kernel
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.DualFiltration.FieldFlag
