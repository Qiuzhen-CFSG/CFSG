module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Evaluation
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Data
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Reduction

/-!
# Soundness of the second-class row certificates

The checks compare four points only after identifying the permutations with
actual Held words. Rejection uses a moved point of one literal source relator.
The source is HeG1-P1.M with the retained ATLAS degree-2058 generators.
-/

@[expose] public section

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB

def representative (i : Fin 11025) : He := word 5 (wordCode i)

def fastRepresentative (i : Fin 11025) : Equiv.Perm (Fin 2058) := fastWord 5 (wordCode i)

def fastRow (i : Fin 11025) (j : Fin 17) : Equiv.Perm (Fin 2058) :=
  MulAut.conj (powPerm j) (fastRepresentative i)

def exponent (k : Fin 2) : Fin 17 := if k = 0 then 1 else 3

def ClosedAt (i : Fin 11025) : Prop := ∀ (j : Fin 17) (t : Fin 4),
  (perm 17 * fastRow i j * (perm 17)⁻¹) ⟨t.val, by omega⟩ =
    fastRow (edgeIndex i j) (edgePower i j) ⟨t.val, by omega⟩

def RejectedAt (i : Fin 11025) : Prop := ∀ k : Fin 2,
  relationWord (fastRepresentative i) (fastRepresentative i * powPerm (exponent k))
    (rejectRelator i k) (rejectPoint i k) ≠ rejectPoint i k

instance (i : Fin 11025) : Decidable (ClosedAt i) := inferInstanceAs (Decidable (∀ _ _, _))
instance (i : Fin 11025) : Decidable (RejectedAt i) := inferInstanceAs (Decidable (∀ _, _))

theorem representation_representative (i : Fin 11025) :
    representation (representative i) = fastRepresentative i := representation_word _ _

theorem representation_row (i : Fin 11025) (j : Fin 17) :
    representation (row representative i j) = fastRow i j := by
  change representation ((a * b) ^ j.val * representative i * ((a * b) ^ j.val)⁻¹) =
    powPerm j * fastRepresentative i * (powPerm j)⁻¹
  simp only [map_mul, map_inv, map_pow,
    representation_representative, powPerm_eq]
  rfl

theorem closure_of_check (i : Fin 11025) (h : ClosedAt i) (j : Fin 17) :
    ∃ (i' : Fin 11025) (j' : Fin 17), ∀ t : Fin 4,
      representation (a * row representative i j * a⁻¹) ⟨t.val, by omega⟩ =
        representation (row representative i' j') ⟨t.val, by omega⟩ := by
  refine ⟨edgeIndex i j, edgePower i j, ?_⟩
  intro t
  simpa only [map_mul, map_inv, representation_row, perm_eq_17,
    show representation a = atlasA from rfl] using h j t

theorem rejection_of_check (i : Fin 11025) (h : RejectedAt i)
    (k : Fin 17) (hk : k = 1 ∨ k = 3) :
    ∃ (r : Fin 7) (p : Fin 2058),
      representation (relationWord (representative i)
        (representative i * (a * b) ^ k.val) r) p ≠ p := by
  have hp (e : Fin 2) : ∃ (r : Fin 7) (p : Fin 2058),
      representation (relationWord (representative i)
        (representative i * (a * b) ^ (exponent e).val) r) p ≠ p := by
    refine ⟨rejectRelator i e, rejectPoint i e, ?_⟩
    simpa only [map_relationWord, map_mul, map_pow, representation_representative,
      powPerm_eq, show representation a = atlasA from rfl,
      show representation b = atlasB from rfl] using h e
  rcases hk with rfl | rfl
  · exact hp 0
  · exact hp 1

def blockCheck (start count : Nat) : Bool :=
  (List.range count).all (fun j =>
    let i : Fin 11025 := ⟨(start + j) % 11025, Nat.mod_lt _ (by decide)⟩
    decide (ClosedAt i) && decide (RejectedAt i))

theorem blockCheck_sound {start count : Nat} (h : blockCheck start count = true)
    (i : Fin 11025) (hi : start ≤ i.val ∧ i.val < start + count) :
    ClosedAt i ∧ RejectedAt i := by
  have he : start + (i.val - start) = i.val := by omega
  have hh := List.all_eq_true.mp h (i.val - start) (List.mem_range.mpr (by omega))
  simpa only [he, Nat.mod_eq_of_lt i.isLt, Bool.and_eq_true, decide_eq_true_eq] using hh

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassB
