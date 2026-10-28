module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.ActorGeometry

/-!
# Fixed planes for the alternating-five conjugate action

The pointwise stabilizer of the plane fixed by the two disjoint transpositions
is exactly their four-group. An exchange-invariant nontrivial subgroup of that
four-group is either the diagonal line or the whole group, and in both cases
its fixed plane has four vectors. In particular, normality excludes each lone
transposition without prematurely excluding the diagonal line.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.2(4),
printed pp.83–84, and the R-normal branch of C.5.6, printed p.157.
-/

public section


open Subgroup BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices

private def pairVector (i : Fin 2) : Vector :=
  if i = 0 then ⟨![1, 1, 0, 0, 0], by norm_num [BinaryPermutation.mem_core, Fin.sum_univ_succ]; decide⟩
  else ⟨![0, 0, 1, 1, 0], by norm_num [BinaryPermutation.mem_core, Fin.sum_univ_succ]; decide⟩

private theorem pairVector_fixed (i : Fin 2) :
    pairVector i ∈ fixedSpace (coreRepresentation (Fin 5)) (ChapterB.Offenders.D 5) := by
  rw [mem_fixed_actor]
  fin_cases i <;> decide

/-- The pointwise stabilizer of the fixed plane of the two pair swaps is the pair-swap group. -/
theorem fixed_plane_stabilizer (p : Perm)
    (hp : ∀ v ∈ fixedSpace (coreRepresentation (Fin 5)) (ChapterB.Offenders.D 5),
      coreRepresentation (Fin 5) p v = v) : p ∈ ChapterB.Offenders.D 5 := by
  have h0 := hp _ (pairVector_fixed 0)
  have h1 := hp _ (pairVector_fixed 1)
  have htest : ∀ p : Perm,
      (∀ k, (pairVector 0).val (p.symm k) = (pairVector 0).val k) →
      (∀ k, (pairVector 1).val (p.symm k) = (pairVector 1).val k) →
      p = 1 ∨ p = transposition 0 ∨ p = transposition 1 ∨ p = doubleSwap := by
    decide +kernel
  exact (mem_actor p).mpr (htest p
    (fun k => congrArg (fun v : Vector => v.val k) h0)
    (fun k => congrArg (fun v : Vector => v.val k) h1))

/-- An exchange-invariant nontrivial subgroup of D has the same fixed plane as D.
The diagonal line remains possible; it too has fixed codimension two. -/
theorem fixed_card_of_normal_image (B : Subgroup Perm)
    (hB : B ≤ ChapterB.Offenders.D 5) (hne : B ≠ ⊥)
    (hn : exchange ∈ normalizer (B : Set Perm)) :
    Nat.card (fixedSpace (coreRepresentation (Fin 5)) B) = 4 := by
  have he : B.map (MulAut.conj exchange).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp hn
  rcases subgroup_cases B hB with h | h | h | h | h
  · exact (hne h).elim
  · rw [h, exchange_line_zero] at he
    exact (line_zero_ne_one he.symm).elim
  · rw [h, exchange_line_one] at he
    exact (line_zero_ne_one he).elim
  · rw [h, fixed_diagonal_card]
  · rw [h, fixed_actor_card]

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.AlternatingIndices

end
