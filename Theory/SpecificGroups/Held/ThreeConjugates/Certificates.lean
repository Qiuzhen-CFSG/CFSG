module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalizer

/-!
# Checked Held generating triples

For each of the two inner involution representatives and the outer
representative, two explicit conjugators give a triple containing both
original ATLAS generators. Six short signed word identities are checked
on the certified four-point base of the full permutation normalizer.
Thus the triple contains the entire embedded Held group. GAP only found
candidate words; all equalities and containments below are kernel checked.

Source: Revin–Zavarnitsine, arXiv:2505.05173v2, Theorems 1–2 and the Held
case of Proposition 2. The retained words, conventions and ATLAS attribution
are explained in `ThreeConjugates/Source/README.md`.
-/

@[expose] public section
namespace Held.ThreeConjugates
open Subgroup LocalPairs

/-- The two inner representatives and the existing outer representative. -/
def seed : Fin 3 → PermutationNormalizer
  | 0 => innerEmbedding a
  | 1 => innerEmbedding ((a * b ^ 3) ^ 4)
  | 2 => OuterInvolution.representative

/-- Inverse of the first GAP right-conjugation witness. -/
def leftConjugator (r : Fin 3) : He :=
  if r = 1 then ((a * b) * b)⁻¹ else ((a * b) ^ 6 * b ^ 2)⁻¹

/-- Inverse of the second GAP right-conjugation witness. -/
def rightConjugator (r : Fin 3) : He :=
  if r = 1 then ((a * b) ^ 7 * b)⁻¹ else ((a * b) ^ 4 * b ^ 3)⁻¹

private def generator (r : Fin 3) : Fin 3 → PermutationNormalizer
  | 0 => seed r
  | 1 => innerEmbedding (leftConjugator r) * seed r *
      (innerEmbedding (leftConjugator r))⁻¹
  | 2 => innerEmbedding (rightConjugator r) * seed r *
      (innerEmbedding (rightConjugator r))⁻¹

private def word (r : Fin 3) (w : List ℤ) : PermutationNormalizer :=
  (w.map (fun k => if k < 0 then (generator r (Fin.ofNat 3 (k.natAbs - 1)))⁻¹
    else generator r (Fin.ofNat 3 (k.natAbs - 1)))).prod

private def recoveryA : Fin 3 → List ℤ
  | 0 => [-1]
  | 1 => [-3, -2, -3, -2, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2, -3, -2, -1, -2, -1, -3, -1, -2, -1, -3, -2, -3, -1, -2, -1, -3, -2, -3, -2, -1, -2, -3, -1, -3, 1, 3, 2, 3, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3, -2]
  | 2 => [1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, -2, -1, -2, -1, -3, -2, -1, -3, -2, -3, -2, -1, -3, -2, -1, -2, -1, -3, -2, -3, -1, -2, -3, -2, -1, -2, -3, -1, -2, -1, 2, 1, 2, 1, 2, -1, -2, -1, -3, -2, -1, -2]

set_option maxRecDepth 16384 in
private theorem recoveryA_eq (r : Fin 3) :
    word r (recoveryA r) = innerEmbedding a := by
  fin_cases r <;> apply OuterInvolution.Fusion.normalizer_ext_four <;> decide +kernel

private def recoveryB : Fin 3 → List ℤ
  | 0 => [2, -3, -2, -3, -2, -1, -2, -1, -3, -1, -2, -1, -3, -2, -1, -3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2, 3, 1, 3, 2, 3, 2, 1, 2, -3, -2, -3, -2, -1, -3, -2, -3, -1, -2, -3, -2, -3, -2, -1, -2, -3, -2, -3, 1, 2]
  | 1 => [2, 1, 2, -3, -2, -3, -2, -1, -2, -1, -3, -1, -2, -3, -1, -2, -3, 2, 1, 2, 3, 2, 3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2, -3, -1, -2, -1, -3, -2, -1, -2, -1, -3, -2, -3, -1, -2, -1, -3, -2, -1, -2, -1, -3, -2, -3, -1, -2, -1, -3, -2, -3, -1, -2, -1, -3, -1, -2, -1, -2, -3, -2, -3, -2, -1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 3, -1, -2, -1, 2, 3]
  | 2 => [2, 1, 3, 1, 3, 1, 3, 1, 2, 3, -2, -1, -3, -1, -2, -3, -1, -2, -1, -3, -2, -1, -3, -1, -3, -1, -2, -3, -2, -3, 1, 2, 1, 3, 2, 3, 2, 1, 3, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, -1, -3, -1, -2, -3, -2, -1, -2, -3, -2, -1, -2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, -2, -3, -2, -1, -3, -2, -1, 2, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 2, 3]

set_option maxRecDepth 16384 in
private theorem recoveryB_eq (r : Fin 3) :
    word r (recoveryB r) = innerEmbedding b := by
  fin_cases r <;> apply OuterInvolution.Fusion.normalizer_ext_four <;> decide +kernel

private def triple (r : Fin 3) : Subgroup PermutationNormalizer :=
  zpowers (seed r) ⊔
    zpowers (innerEmbedding (leftConjugator r) * seed r *
      (innerEmbedding (leftConjugator r))⁻¹) ⊔
    zpowers (innerEmbedding (rightConjugator r) * seed r *
      (innerEmbedding (rightConjugator r))⁻¹)

private theorem generator_mem (r i : Fin 3) : generator r i ∈ triple r := by
  fin_cases i
  · exact mem_sup_left (mem_sup_left (mem_zpowers _))
  · exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · exact mem_sup_right (mem_zpowers _)

private theorem word_mem (r : Fin 3) (w : List ℤ) : word r w ∈ triple r := by
  apply list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact inv_mem (generator_mem _ _)
  · exact generator_mem _ _

/-- Each of the three explicit triples contains the entire original Held group. -/
theorem seed_generates (r : Fin 3) :
    innerEmbedding.range ≤
      zpowers (seed r) ⊔
        zpowers (innerEmbedding (leftConjugator r) * seed r *
          (innerEmbedding (leftConjugator r))⁻¹) ⊔
        zpowers (innerEmbedding (rightConjugator r) * seed r *
          (innerEmbedding (rightConjugator r))⁻¹) := by
  change innerEmbedding.range ≤ triple r
  rw [MonoidHom.range_eq_map, ← closure_pair, map_le_iff_le_comap, closure_le]
  rintro x (rfl | hx)
  · change innerEmbedding a ∈ triple r
    rw [← recoveryA_eq r]
    exact word_mem _ _
  · rw [Set.mem_singleton_iff.mp hx]
    change innerEmbedding b ∈ triple r
    rw [← recoveryB_eq r]
    exact word_mem _ _

end Held.ThreeConjugates
