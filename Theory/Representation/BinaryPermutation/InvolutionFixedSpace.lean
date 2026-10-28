module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Involutions are determined by their fixed permutation functions

The indicator of the one- or two-point orbit of a point is fixed by an
involution. Inclusion of fixed spaces therefore forces preservation of each
such orbit. Applying this in both directions recovers the involution from its
fixed space. The action is the literal inverse-permutation action.

Source application: Aschbacher--Smith, B.3 and K.4, the binary eleven-point
augmentation module for M₁₁. No finiteness assumption on the point set is needed.
-/

public section
open Representation.BinaryOffender Subgroup

namespace BinaryPermutation
variable {Ω : Type*}

private theorem mem_pair_of_fixedSpace_le (a b : Equiv.Perm Ω) (ha : a ^ 2 = 1)
    (h : fixedSpace (representation Ω) (zpowers a) ≤
      fixedSpace (representation Ω) (zpowers b)) (i : Ω) :
    b i = i ∨ b i = a i := by
  classical
  have haa (j : Ω) : a (a j) = j := congrArg (fun p : Equiv.Perm Ω => p j) ha
  have hai : a.symm = a := by
    apply _root_.Equiv.ext
    intro j
    apply a.injective
    rw [a.apply_symm_apply, haa]
  let v : Full Ω := fun j => if j = i ∨ j = a i then 1 else 0
  have hv : v ∈ fixedSpace (representation Ω) (zpowers a) := by
    rw [mem_fixedSpace_zpowers_iff]
    ext j
    have haj : a j = i ↔ j = a i :=
      ⟨fun hj => by rw [← haa j, hj], fun hj => by rw [hj, haa]⟩
    simp only [representation_apply, hai, v, haj, a.injective.eq_iff, or_comm]
  have hb := congrFun ((mem_fixedSpace_zpowers_iff _ _ _).mp (h hv)) (b i)
  have he : v (b i) = 1 := by
    simpa only [representation_apply, b.symm_apply_apply, v, true_or, if_true]
      using hb.symm
  simpa only [v, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using he

/-- Involutory permutations are determined by their fixed functions. -/
theorem involution_eq_of_fixedSpace_eq (a b : Equiv.Perm Ω)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : fixedSpace (representation Ω) (zpowers a) =
      fixedSpace (representation Ω) (zpowers b)) : a = b := by
  apply _root_.Equiv.ext
  intro i
  rcases mem_pair_of_fixedSpace_le a b ha h.le i with hi | hi
  · rcases mem_pair_of_fixedSpace_le b a hb h.ge i with hj | hj
    · exact hj.trans hi.symm
    · exact hj
  · exact hi.symm
end BinaryPermutation
