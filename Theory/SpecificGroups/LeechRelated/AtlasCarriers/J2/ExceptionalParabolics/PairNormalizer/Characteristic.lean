module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.SylowOrder
import Mathlib.Tactic.FinCases

/-!
# The characteristic radical in the fixed Hall--Janko two-subgroup

The radical has exponent four. For any index-two subgroup of exponent four,
three explicit products of the fixed generators cannot belong to it: their
fourth powers are nonidentity. The index-two membership rule then fixes the
membership of three generators, and six short words place all radical
generators in that subgroup. Applying this to automorphic images proves
relative characteristicity in `Seed.s`.

This argument uses the actual degree-100 carrier and proves the intrinsic
invariance, without assuming Sylow or automorphism coverage. Source: GLS3,
Table 5.3g, and Aschbacher--Smith, printed p.511 (PDF p.528).
-/

@[expose] public section

open Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open GeneratorPair Seed RadicalData SylowData GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000 in
private theorem q_four_check : ∀ i, (qTable i) ^ 4 = 1 := by
  apply allFin
  decide +kernel

theorem q₂_exponent_four (x : Carrier) (hx : x ∈ q₂) : x ^ 4 = 1 := by
  obtain ⟨i, rfl⟩ := exists_qElement hx
  apply inclusion_injective
  rw [map_pow, map_one, qElement_inclusion]
  exact q_four_check i

def tripleGenerator (i : Fin 3) : s :=
  ⟨sGenerator (![1, 2, 3] i), Subgroup.subset_closure ⟨_, rfl⟩⟩

def qTripleWords : Fin 6 → List (Fin 3) :=
  ![[1], [0], [1, 0, 2, 1, 2, 0], [1, 2, 1, 0, 2, 0],
    [2, 1, 2, 0, 2, 1, 2, 0], [2, 0, 2, 0, 2, 0, 2, 0]]

private theorem tripleWord_inclusion (w : List (Fin 3)) :
    inclusion (evalWord tripleGenerator w : s) =
      evalWord (fun i => sGenTable (![1, 2, 3] i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion ((tripleGenerator i : Carrier) * (evalWord tripleGenerator w : s)) = _
    rw [map_mul, ih]
    exact congrArg (fun x => x * _) (sGenerator_inclusion _)

set_option maxRecDepth 100000 in
private theorem q_triple_check : ∀ i,
    qGenTable i = evalWord (fun j => sGenTable (![1, 2, 3] j)) (qTripleWords i) := by
  apply allFin
  decide +kernel

theorem q₂Generator_eq_triple (i : Fin 6) :
    q₂Generator i = (evalWord tripleGenerator (qTripleWords i) : s) := by
  apply inclusion_injective
  rw [q₂Generator_inclusion, tripleWord_inclusion]
  exact q_triple_check i

private theorem triple_inclusion (i : Fin 3) :
    inclusion (tripleGenerator i : Carrier) = sGenTable (![1, 2, 3] i) :=
  sGenerator_inclusion _

set_option maxRecDepth 100000 in
private theorem triple_bad :
    (tripleGenerator 2 * tripleGenerator 0) ^ 4 ≠ 1 ∧
    (tripleGenerator 2 * tripleGenerator 1) ^ 4 ≠ 1 ∧
    (tripleGenerator 2 * (tripleGenerator 1 * tripleGenerator 0)) ^ 4 ≠ 1 := by
  have h :
      (sGenTable 3 * sGenTable 1) ^ 4 ≠ 1 ∧
      (sGenTable 3 * sGenTable 2) ^ 4 ≠ 1 ∧
      (sGenTable 3 * (sGenTable 2 * sGenTable 1)) ^ 4 ≠ 1 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro hh
    have hv := congrArg (fun x : s => inclusion (x : Carrier)) hh
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one,
      map_pow, map_mul, map_one, triple_inclusion] at hv
  · exact h.1 hv
  · exact h.2.1 hv
  · exact h.2.2 hv

theorem q₂_le_of_index_two_exponent_four (H : Subgroup s)
    (hi : H.index = 2) (hfour : ∀ x ∈ H, x ^ 4 = 1) : q₂.subgroupOf s ≤ H := by
  have htx : tripleGenerator 2 * tripleGenerator 0 ∉ H :=
    fun h => triple_bad.1 (hfour _ h)
  have hty : tripleGenerator 2 * tripleGenerator 1 ∉ H :=
    fun h => triple_bad.2.1 (hfour _ h)
  have htyx : tripleGenerator 2 * (tripleGenerator 1 * tripleGenerator 0) ∉ H :=
    fun h => triple_bad.2.2 (hfour _ h)
  simp only [H.mul_mem_iff_of_index_two hi] at htx hty htyx
  have hm : tripleGenerator 0 ∈ H ∧ tripleGenerator 1 ∈ H ∧ tripleGenerator 2 ∉ H := by
    classical
    have ht : tripleGenerator 2 ∉ H := by
      intro ht
      have hx : tripleGenerator 0 ∉ H := fun hx => htx (iff_of_true ht hx)
      have hy : tripleGenerator 1 ∉ H := fun hy => hty (iff_of_true ht hy)
      exact htyx (iff_of_true ht (iff_of_false hy hx))
    have hx : tripleGenerator 0 ∈ H := by
      by_contra hx
      exact htx (iff_of_false ht hx)
    have hy : tripleGenerator 1 ∈ H := by
      by_contra hy
      exact hty (iff_of_false ht hy)
    exact ⟨hx, hy, ht⟩
  have hgen (i : Fin 6) : evalWord tripleGenerator (qTripleWords i) ∈ H := by
    fin_cases i <;>
      simp [qTripleWords, evalWord, H.mul_mem_iff_of_index_two hi, hm.1, hm.2.1, hm.2.2]
  have hle : q₂ ≤ H.map s.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_map.mpr ⟨_, hgen i, (q₂Generator_eq_triple i).symm⟩
  intro x hx
  obtain ⟨y, hy, he⟩ := hle hx
  exact (Subtype.ext he : y = x) ▸ hy

theorem q₂_characteristic : (q₂.subgroupOf s).Characteristic := by
  apply Subgroup.characteristic_iff_le_map.mpr
  intro f
  apply q₂_le_of_index_two_exponent_four
  · exact (Subgroup.index_map_of_bijective f.bijective _).trans q₂_relIndex_s
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h : y ^ 4 = 1 := Subtype.ext (q₂_exponent_four y hy)
    rw [← map_pow, h, map_one]

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
