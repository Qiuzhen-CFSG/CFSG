module

public import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Eleven letters and their unordered pairs

These explicit even permutations are the proposed images of the two literal
Lyons local generators. They generate A₁₁: an eleven-cycle gives transitivity,
prime degree gives primitivity, and a short word is a three-cycle. Jordan's
three-cycle theorem then applies. The 55 pair permutations preserve the stated
incidence with the eleven letters.

The permutations were found from the ATLAS `LyG1-max4W1` matrix words. Their
connection to those matrices is a separate certificate, not an assumption of
this module. Source: GLS3, section 5.3, Lyons table, printed p.278.
-/

namespace Lyons.SimplicityCertificate.AlternatingQuotient

@[expose] public def letterA : Equiv.Perm (Fin 11) where
  toFun i := ![6, 0, 1, 2, 3, 4, 5, 7, 8, 9, 10] i
  invFun i := ![1, 2, 3, 4, 5, 6, 0, 7, 8, 9, 10] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] public def letterB : Equiv.Perm (Fin 11) where
  toFun i := ![4, 10, 6, 2, 8, 3, 9, 5, 0, 7, 1] i
  invFun i := ![8, 10, 3, 5, 0, 7, 2, 9, 4, 6, 1] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] public def pairA : Equiv.Perm (Fin 55) where
  toFun i := ![5, 14, 22, 29, 35, 40, 45, 46, 47, 48, 0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 49, 50, 51, 52, 53, 54] i
  invFun i := ![10, 11, 12, 13, 14, 0, 15, 16, 17, 18, 19, 20, 21, 22, 1, 23, 24, 25, 26, 27, 28, 29, 2, 30, 31, 32, 33, 34, 35, 3, 36, 37, 38, 39, 40, 4, 41, 42, 43, 44, 5, 45, 46, 47, 48, 6, 7, 8, 9, 49, 50, 51, 52, 53, 54] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] public def pairB : Equiv.Perm (Fin 55) where
  toFun i := ![39, 35, 20, 37, 27, 38, 34, 3, 36, 12, 48, 26, 53, 33, 54, 44, 9, 51, 18, 22, 46, 29, 47, 40, 5, 45, 14, 24, 19, 25, 21, 1, 23, 10, 31, 52, 42, 7, 49, 16, 32, 28, 2, 30, 11, 43, 8, 50, 17, 4, 41, 13, 6, 0, 15] i
  invFun i := ![53, 31, 42, 7, 49, 24, 52, 37, 46, 16, 33, 44, 9, 51, 26, 54, 39, 48, 18, 28, 2, 30, 19, 32, 27, 29, 11, 4, 41, 21, 43, 34, 40, 13, 6, 1, 8, 3, 5, 0, 23, 50, 36, 45, 15, 25, 20, 22, 10, 38, 47, 17, 35, 12, 14] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] public def leftLetter (i : Fin 55) : Fin 11 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 8, 8, 9] i

@[expose] public def rightLetter (i : Fin 55) : Fin 11 :=
  ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 2, 3, 4, 5, 6, 7, 8, 9, 10, 3, 4, 5, 6, 7, 8, 9, 10, 4, 5, 6, 7, 8, 9, 10, 5, 6, 7, 8, 9, 10, 6, 7, 8, 9, 10, 7, 8, 9, 10, 8, 9, 10, 9, 10, 10] i

/-- Incidence of a letter with an unordered pair. -/
@[expose] public def incident (i : Fin 11) (k : Fin 55) : Prop :=
  leftLetter k = i ∨ rightLetter k = i

public instance (i : Fin 11) (k : Fin 55) : Decidable (incident i k) :=
  inferInstanceAs (Decidable (_ ∨ _))

public theorem incident_pairA (i : Fin 11) (k : Fin 55) :
    incident (letterA i) (pairA k) ↔ incident i k := by
  revert i k
  decide +kernel

public theorem incident_pairB (i : Fin 11) (k : Fin 55) :
    incident (letterB i) (pairB k) ↔ incident i k := by
  revert i k
  decide +kernel

public theorem incidence_separates (i j : Fin 11) (h : i ≠ j) :
    ∃ k : Fin 55, incident i k ∧ ¬ incident j k := by
  revert h
  revert i j
  decide +kernel

public theorem letterA_even : letterA ∈ alternatingGroup (Fin 11) := by
  change Equiv.Perm.sign letterA = 1
  decide +kernel
public theorem letterB_even : letterB ∈ alternatingGroup (Fin 11) := by
  change Equiv.Perm.sign letterB = 1
  decide +kernel

/-- These two permutations generate the full alternating group. -/
public theorem closure_letters :
    Subgroup.closure {letterA, letterB} = alternatingGroup (Fin 11) := by
  let H := Subgroup.closure ({letterA, letterB} : Set (Equiv.Perm (Fin 11)))
  have ha : letterA ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : letterB ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc : letterA ^ 2 * letterB ∈ H := H.mul_mem (H.pow_mem ha 2) hb
  have trans : ∀ i j : Fin 11, ∃ n : Fin 11, ((letterA ^ 2 * letterB) ^ n.val) i = j := by
    decide +kernel
  have : MulAction.IsPretransitive H (Fin 11) := ⟨by
    intro i j
    obtain ⟨n, hn⟩ := trans i j
    exact ⟨⟨_, H.pow_mem hc n.val⟩, hn⟩⟩
  have prim : MulAction.IsPreprimitive H (Fin 11) :=
    MulAction.IsPreprimitive.of_prime_card (by simp; decide)
  have ht : (letterA * letterB * letterA ^ 6 * letterB) ^ 4 ∈ H :=
    H.pow_mem (H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.pow_mem ha 6)) hb) 4
  have h3 : ((letterA * letterB * letterA ^ 6 * letterB) ^ 4).IsThreeCycle := by
    change ((letterA * letterB * letterA ^ 6 * letterB) ^ 4).cycleType = {3}
    decide +kernel
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (by
      intro g hg
      rcases hg with rfl | rfl
      · exact letterA_even
      · exact letterB_even)
  · exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem prim h3 ht

end Lyons.SimplicityCertificate.AlternatingQuotient
