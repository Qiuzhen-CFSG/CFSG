module

public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Two inner conjugates of a rank-three elementary subgroup of S₇

Each of the two elementary subgroups of order eight contains a transposition.
For the three-pair group, the product of (01)(23)(45) with its conjugate by
(0123456) is a seven-cycle. For the four-plus-two group, use (02)(13)(45)
and conjugate by (0123456)³. A seven-cycle and any transposition generate S₇.
The exhaustive elementary-subgroup geometry transports these two calculations
to every rank-three subgroup. Both conjugators are even, and remain even under
transport, so they lift through any marked component isomorphic to A₇.

Together with the fixed-space codimension inequality, this excludes degree
fourteen under the original ambient cubic bound two in Aschbacher–Smith K.1.2,
printed p.452/PDF p.463. Only the explicit seven-point identities use finite
kernel reduction; no representation catalogue or module model is used.
-/

open Equiv Subgroup
namespace Representation.AlternatingSevenConjugatePair.ElementaryGeometry
open BinaryOffender

private theorem generate_of_cycle (E : Subgroup S7) (t q : S7)
    (ht : t ∈ E) (hswap : swap45 ∈ E)
    (hc : (t * (q * t * q⁻¹)).IsCycle)
    (hs : (t * (q * t * q⁻¹)).support = Finset.univ) :
    E ⊔ E.map (MulAut.conj q).toMonoidHom = ⊤ := by
  apply top_unique
  rw [← Perm.closure_prime_cycle_swap (by decide : (Fintype.card (Fin 7)).Prime)
    hc hs (show Perm.IsSwap swap45 from ⟨4, 5, by decide, rfl⟩)]
  apply (closure_le _).mpr
  rintro x (rfl | rfl)
  · exact (E ⊔ E.map (MulAut.conj q).toMonoidHom).mul_mem
      (mem_sup_left ht) (mem_sup_right ⟨t, ht, rfl⟩)
  · exact mem_sup_left hswap

private def pairTriple : S7 := swap01 * swap23 * swap45
private def fourTriple : S7 := crossSwap * swap45
private def pairConjugator : S7 := finRotate 7
private def fourConjugator : S7 := finRotate 7 ^ 3

private theorem pair_generates :
    ∃ q : S7, q ∈ alternatingGroup (Fin 7) ∧
      pairElementary ⊔ pairElementary.map (MulAut.conj q).toMonoidHom = ⊤ := by
  refine ⟨pairConjugator, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup]
    decide +kernel
  · apply generate_of_cycle pairElementary pairTriple pairConjugator
    · exact pairElementary.mul_mem
        (pairElementary.mul_mem pairElementary_generators.1 pairElementary_generators.2.1)
        pairElementary_generators.2.2
    · exact swap45_mem_pairElementary
    · exact Perm.card_cycleType_eq_one.mp (by decide +kernel)
    · decide +kernel

private theorem four_generates :
    ∃ q : S7, q ∈ alternatingGroup (Fin 7) ∧
      fourTwoElementary ⊔ fourTwoElementary.map (MulAut.conj q).toMonoidHom = ⊤ := by
  refine ⟨fourConjugator, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup]
    decide +kernel
  · apply generate_of_cycle fourTwoElementary fourTriple fourConjugator
    · exact fourTwoElementary.mul_mem fourTwoElementary_generators.2.1
        fourTwoElementary_generators.2.2
    · exact swap45_mem_fourTwoElementary
    · exact Perm.card_cycleType_eq_one.mp (by decide +kernel)
    · decide +kernel

private theorem transport_generation (A : Subgroup S7) (g q : S7)
    (hq : q ∈ alternatingGroup (Fin 7))
    (hgen : A.map (MulAut.conj g).toMonoidHom ⊔
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom = ⊤) :
    ∃ r : S7, r ∈ alternatingGroup (Fin 7) ∧
      A ⊔ A.map (MulAut.conj r).toMonoidHom = ⊤ := by
  let r := g⁻¹ * q * g
  refine ⟨r, ?_, ?_⟩
  · simpa only [inv_inv] using
      (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem q hq g⁻¹
  · apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]
    have he : (A.map (MulAut.conj r).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, r, mul_assoc]
    rw [he]
    exact hgen

/-- Every elementary subgroup of rank three in S₇ generates S₇ with one
conjugate by an even permutation. -/
public theorem rank_three_two_even_conjugates (A : Subgroup S7)
    (hA : IsElementaryTwo A) (hr : rank A = 3) :
    ∃ q : S7, q ∈ alternatingGroup (Fin 7) ∧
      A ⊔ A.map (MulAut.conj q).toMonoidHom = ⊤ := by
  obtain ⟨g, hg | hg⟩ := elementary_rank_three_conjugacy A hA hr
  · obtain ⟨q, hq, hgen⟩ := pair_generates
    apply transport_generation A g q hq
    simpa only [hg] using hgen
  · obtain ⟨q, hq, hgen⟩ := four_generates
    apply transport_generation A g q hq
    simpa only [hg] using hgen

end Representation.AlternatingSevenConjugatePair.ElementaryGeometry
