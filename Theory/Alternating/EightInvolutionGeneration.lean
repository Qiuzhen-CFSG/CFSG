module

public import Theory.Alternating.theorem_5_2_1_2
public import Theory.Alternating.Aut
public import Theory.GroupTheory.InvolutionAutomorphismGeneration
import Mathlib.Tactic.FinCases

/-!
# Seven conjugates of involutory automorphisms of A₈

Every nonidentity involution in S₈ has one of four cycle types: one, two,
three or four disjoint transpositions. For each representative, seven even
conjugators are given below. Short words in the conjugate involutions produce
all six star three-cycles `(01)(0i)`, so their closure contains A₈. The explicit
permutation, parity, cycle-type and word identities are checked by the kernel;
no computed subgroup order is used.

Conjugation transports the construction to every involution of S₈. An
arbitrary symmetric-group conjugator preserves evenness of the seven
conjugators. The actual isomorphism S₈ ≃ Aut(A₈) then gives the inner-conjugator
contract, including both inner and outer involutions.

This constructive auxiliary lemma supplies the seven-conjugate bound in the
binary SL₄ full-support argument associated with Guralnick–Malle,
*Classification of 2F-modules, II*, author manuscript Proposition 4.8(3B).
The automorphism identification is GLS, Volume 3, Theorem 5.2.1, proved in
`Theory.Alternating.Aut`; star generation is proved in
`Theory.Alternating.theorem_5_2_1_2`.
-/

open Equiv Subgroup
namespace alternatingGroup.EightInvolutionGeneration
private abbrev P := Perm (Fin 8)
private abbrev A := alternatingGroup (Fin 8)
private def seed : Fin 4 → P :=
  ![swap 0 1, swap 0 1 * swap 2 3,
    swap 0 1 * swap 2 3 * swap 4 5, swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7]

private def conjugator : Fin 4 → Fin 7 → P :=
  ![![⟨![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 2, 3, 1, 4, 5, 6, 7], ![0, 3, 1, 2, 4, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 3, 1, 2, 4, 5, 6, 7], ![0, 2, 3, 1, 4, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 4, 1, 3, 2, 5, 6, 7], ![0, 2, 4, 3, 1, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 5, 1, 3, 4, 2, 6, 7], ![0, 2, 5, 3, 4, 1, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 6, 1, 3, 4, 5, 2, 7], ![0, 2, 6, 3, 4, 5, 1, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 7, 1, 3, 4, 5, 6, 2], ![0, 2, 7, 3, 4, 5, 6, 1],
        by decide +kernel, by decide +kernel⟩],
    ![⟨![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![5, 7, 2, 6, 0, 1, 4, 3], ![4, 5, 2, 7, 6, 0, 3, 1],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 5, 3, 1, 2, 7, 4, 6], ![0, 3, 4, 2, 6, 1, 7, 5],
        by decide +kernel, by decide +kernel⟩,
      ⟨![3, 6, 0, 7, 1, 4, 5, 2], ![2, 4, 7, 0, 5, 6, 1, 3],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 7, 5, 2, 4, 1, 6, 3], ![0, 5, 3, 7, 4, 2, 6, 1],
        by decide +kernel, by decide +kernel⟩,
      ⟨![6, 5, 7, 4, 3, 0, 2, 1], ![5, 7, 6, 4, 3, 1, 0, 2],
        by decide +kernel, by decide +kernel⟩,
      ⟨![7, 5, 2, 1, 6, 0, 3, 4], ![5, 3, 2, 6, 7, 1, 4, 0],
        by decide +kernel, by decide +kernel⟩],
    ![⟨![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![5, 6, 7, 1, 3, 2, 4, 0], ![7, 3, 5, 4, 6, 0, 1, 2],
        by decide +kernel, by decide +kernel⟩,
      ⟨![1, 5, 4, 6, 0, 3, 2, 7], ![4, 0, 6, 5, 2, 1, 3, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![1, 3, 4, 0, 2, 7, 6, 5], ![3, 0, 4, 1, 2, 7, 6, 5],
        by decide +kernel, by decide +kernel⟩,
      ⟨![5, 2, 1, 7, 4, 6, 0, 3], ![6, 2, 1, 7, 4, 0, 5, 3],
        by decide +kernel, by decide +kernel⟩,
      ⟨![2, 7, 4, 3, 0, 6, 5, 1], ![4, 7, 0, 3, 2, 6, 5, 1],
        by decide +kernel, by decide +kernel⟩,
      ⟨![4, 0, 5, 1, 3, 2, 6, 7], ![1, 3, 5, 4, 0, 2, 6, 7],
        by decide +kernel, by decide +kernel⟩],
    ![⟨![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![7, 4, 5, 3, 2, 0, 1, 6], ![5, 6, 4, 3, 1, 2, 7, 0],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 6, 5, 2, 4, 7, 1, 3], ![0, 6, 3, 7, 4, 2, 1, 5],
        by decide +kernel, by decide +kernel⟩,
      ⟨![4, 5, 6, 0, 2, 3, 1, 7], ![3, 6, 4, 5, 0, 1, 2, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 1, 2, 5, 6, 3, 4, 7], ![0, 1, 2, 5, 6, 3, 4, 7],
        by decide +kernel, by decide +kernel⟩,
      ⟨![0, 1, 7, 5, 6, 2, 4, 3], ![0, 1, 5, 7, 6, 3, 4, 2],
        by decide +kernel, by decide +kernel⟩,
      ⟨![4, 7, 2, 1, 6, 3, 5, 0], ![7, 3, 2, 5, 0, 6, 4, 1],
        by decide +kernel, by decide +kernel⟩]]

private theorem conjugator_even (k : Fin 4) (i : Fin 7) :
    conjugator k i ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]
  fin_cases k <;> fin_cases i <;> decide +kernel

private def word (k : Fin 4) : List (Fin 7) → P
  | [] => 1
  | i :: w => (conjugator k i * seed k * (conjugator k i)⁻¹) * word k w

private def words : Fin 4 → Fin 6 → List (Fin 7) :=
  ![![[0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6]],
    ![[2, 4, 2, 6], [2, 1, 3, 1, 0], [0, 5, 2, 6, 2, 5], [0, 1, 3, 1], [1, 2, 6, 3, 0], [0, 2, 6, 2]],
    ![[2, 4, 6, 3, 2, 4], [2, 4, 3, 6, 3, 6], [0, 1, 0, 3, 0, 6, 5, 1], [3, 4, 6, 4, 5, 3], [2, 4, 6, 4, 2, 5], [0, 1, 0, 6, 3, 4, 3, 6]],
    ![[1, 5, 3, 2, 4, 0, 1, 5], [1, 2, 3, 5, 0, 2, 6, 0], [1, 6, 3, 2, 5, 2], [0, 2, 5, 2, 3, 6, 1, 0], [1, 0, 2, 4, 3, 1], [0, 1, 3, 4, 0, 2, 1]]]

private theorem word_eq (k : Fin 4) (j : Fin 6) :
    word k (words k j) = swap 0 1 * swap 0 ⟨j.val + 2, by omega⟩ := by
  fin_cases k <;> fin_cases j <;> decide +kernel

private theorem seed_cycleType (k : Fin 4) :
    (seed k).cycleType = Multiset.replicate (k.val + 1) 2 := by
  fin_cases k <;> decide +kernel

private theorem involution_isConj (t : P) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ k : Fin 4, IsConj (seed k) t := by
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hbound := t.sum_cycleType_le
  rw [hk] at hbound
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hbound
  refine ⟨⟨k, by omega⟩, Perm.isConj_iff_cycleType_eq.mpr ?_⟩
  exact (seed_cycleType ⟨k, by omega⟩).trans hk.symm

private theorem word_mem (k : Fin 4) (w : List (Fin 7)) :
    word k w ∈ closure (Set.range fun i =>
      conjugator k i * seed k * (conjugator k i)⁻¹) := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih => exact mul_mem (subset_closure ⟨i, rfl⟩) ih

private theorem alternating_le_of_star (H : Subgroup P)
    (hstar : ∀ i : Fin 8, i ≠ 0 → i ≠ 1 → swap 0 1 * swap 0 i ∈ H) :
    alternatingGroup (Fin 8) ≤ H := by
  have ht : H.comap (alternatingGroup (Fin 8)).subtype = ⊤ := by
    apply top_unique
    rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top (a := (0 : Fin 8))
      (b := 1) (by decide)]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, hi0, hi1, hi⟩
    change (x : P) ∈ H
    rw [hi]
    exact hstar i hi0 hi1
  intro x hx
  have h : (⟨x, hx⟩ : A) ∈ H.comap (alternatingGroup (Fin 8)).subtype := by
    rw [ht]
    trivial
  exact h

private theorem seed_generates (k : Fin 4) :
    alternatingGroup (Fin 8) ≤ closure (Set.range fun i =>
      conjugator k i * seed k * (conjugator k i)⁻¹) := by
  apply alternating_le_of_star
  intro i hi0 hi1
  have h (j : Fin 6) := word_mem k (words k j)
  simp only [word_eq] at h
  fin_cases i
  · exact (hi0 rfl).elim
  · exact (hi1 rfl).elim
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h 5

private theorem conjugate_generation (a t : P) (q : P) (hqt : q * a * q⁻¹ = t)
    (c : Fin 7 → A)
    (hc : alternatingGroup (Fin 8) ≤ closure
      (Set.range fun i => (c i : P) * a * (c i : P)⁻¹)) :
    ∃ d : Fin 7 → A, alternatingGroup (Fin 8) ≤ closure
      (Set.range fun i => (d i : P) * t * (d i : P)⁻¹) := by
  let e := MulAut.conj q
  let d : Fin 7 → A := fun i => MulAut.conjNormal q (c i)
  refine ⟨d, ?_⟩
  let H := closure (Set.range fun i => (d i : P) * t * (d i : P)⁻¹)
  have hmap : (closure (Set.range fun i => (c i : P) * a * (c i : P)⁻¹)).map
      e.toMonoidHom ≤ H := by
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    have he : e a = t := hqt
    change e ((c i : P) * a * (c i : P)⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv, he]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  intro x hx
  let y : A := MulAut.conjNormal q⁻¹ ⟨x, hx⟩
  apply hmap
  refine ⟨(y : P), hc y.property, ?_⟩
  change q * (q⁻¹ * x * (q⁻¹)⁻¹) * q⁻¹ = x
  group

/-- Seven even conjugators suffice for every nonidentity involution in S₈,
including the odd permutations inducing outer automorphisms of A₈. -/
public theorem seven_conjugates_generate (t : Perm (Fin 8)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ c : Fin 7 → alternatingGroup (Fin 8), alternatingGroup (Fin 8) ≤ closure
      (Set.range fun i => (c i : Perm (Fin 8)) * t * (c i : Perm (Fin 8))⁻¹) := by
  obtain ⟨k, hk⟩ := involution_isConj t ht ht2
  obtain ⟨q, hq⟩ := isConj_iff.mp hk
  exact conjugate_generation (seed k) t q hq
    (fun i => ⟨conjugator k i, conjugator_even k i⟩) (seed_generates k)

private theorem automorphism_generation
    (hg : ∀ t : P, t ≠ 1 → t ^ 2 = 1 → ∃ c : Fin 7 → A,
      alternatingGroup (Fin 8) ≤ closure
        (Set.range fun i => (c i : P) * t * (c i : P)⁻¹)) :
    Theory.GroupTheory.InvolutionInnerConjugateGenerationBound A 7 := by
  let f : P →* MulAut A := MulAut.conjNormal
  have hf := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    8 (by decide) (by decide)
  intro t ht ht2
  obtain ⟨s, rfl⟩ := hf.2 t
  have hs : s ≠ 1 := by
    intro he
    apply ht
    rw [he, map_one]
  have hs2 : s ^ 2 = 1 := hf.1 (by rw [map_pow, ht2, map_one])
  obtain ⟨c, hc⟩ := hg s hs hs2
  refine ⟨c, ?_⟩
  have hmap := Subgroup.map_mono (f := f) hc
  rw [MonoidHom.map_closure] at hmap
  have he (a : A) : f (a : P) = MulAut.conj a := MulAut.conjNormal_val
  have hset : f '' (Set.range fun i => (c i : P) * s * (c i : P)⁻¹) =
      Set.range (fun i => MulAut.conj (c i) * f s * (MulAut.conj (c i))⁻¹) := by
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, map_mul, map_inv, he]
  rw [hset] at hmap
  apply le_trans ?_ hmap
  rintro x ⟨a, rfl⟩
  exact ⟨(a : P), a.property, he a⟩

/-- Every nonidentity involutory automorphism of A₈ admits seven inner conjugates whose
closure contains all inner automorphisms. -/
public theorem seven_inner_conjugates :
    Theory.GroupTheory.InvolutionInnerConjugateGenerationBound
      (alternatingGroup (Fin 8)) 7 :=
  automorphism_generation seven_conjugates_generate

end alternatingGroup.EightInvolutionGeneration
