module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Extensions.Basic

/-!
# The literal Held row-3 order-three extension

The published max5 word centralizes row 3 and conjugates each of the eight
literal core generators to the listed product of those same generators.
All equalities are checked on the faithful four-point base. The extra word
[2] centralizes the row, but its conjugate sends point one to 1318, outside
all 1024 representative words' point-one images. Word [1] does not centralize
the row. These checks give both the intersection order and its displacement.

Source: original ATLAS HeG1-p2058B0/max5 words; GLS3 Table 5.3p and quasithin
condition E. The script in `source/discover.py` proposes the product words;
every finite assertion below is checked by the Lean kernel.
-/

@[expose] public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.ExtensionCertificates
open Subgroup LocalPairs.SylowGeometry.Calculations SpanCertificates
open IntrinsicEnumeration IntrinsicEnumeration.ExtensionChecks

-- Bound memory by elaborating the kernel computations serially.
set_option Elab.async false
namespace RowThree

private def witness : He := x⁻¹ * y * x
private def witnessPerm : Equiv.Perm (Fin 2058) := representation witness
private theorem witnessPerm_eq : witnessPerm = representation witness := rfl

private def images : Fin 8 → List (Fin 8)
  | 0 => [0, 1, 3, 4, 5]
  | 1 => [0, 2, 3, 4, 5]
  | 2 => [4]
  | 3 => [3]
  | 4 => [2, 3, 4, 5]
  | 5 => [5]
  | 6 => [7, 1]
  | _ => [0, 1, 2, 7, 4, 6]

set_option maxRecDepth 8192 in
private theorem cube_check : ∀ v : Fin 4,
    (witnessPerm ^ 3) ⟨v.val, by omega⟩ = (1 : Equiv.Perm (Fin 2058)) ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem nontrivial_check : witnessPerm 0 ≠ 0 := by decide +kernel

private theorem order_three : orderOf witness = 3 := by
  apply orderOf_eq_prime
  · apply Held.eq_of_four_point_images
    rw [map_pow, map_one]
    exact cube_check
  · intro h
    apply nontrivial_check
    change representation witness 0 = 0
    rw [h, map_one]
    rfl

set_option maxRecDepth 8192 in
private theorem commute_check : ∀ a : Fin (generatorWords 3).length, ∀ v : Fin 4,
    (wordPerm (generatorWords 3) a * witnessPerm) ⟨v.val, by omega⟩ =
      (witnessPerm * wordPerm (generatorWords 3) a) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem centralizes : witness ∈ centralizer (ambient 3 : Set He) := by
  apply centralizes_of_generators
  intro a
  apply Held.eq_of_four_point_images
  rw [map_mul, map_mul, ← wordPerm_eq]
  rw [← witnessPerm_eq]
  exact commute_check a

set_option maxRecDepth 8192 in
private theorem normalization_check : ∀ a : Fin 8, ∀ v : Fin 4,
    (witnessPerm * wordPerm (spanWords 3) a * witnessPerm⁻¹) ⟨v.val, by omega⟩ =
      productPerm (spanWords 3) (images a) ⟨v.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem normalizes : witness ∈ normalizer (coreCandidate 3 : Set He) := by
  apply normalizes_of_generators
  intro a
  have he : witness * wordGenerator (spanWords 3) a * witness⁻¹ =
      eval (wordGenerator (spanWords 3)) (images a) := by
    apply Held.eq_of_four_point_images
    rw [map_mul, map_mul, map_inv, ← wordPerm_eq (spanWords 3) a,
      ← productPerm_eq (spanWords 3) (images a)]
    rw [← witnessPerm_eq]
    exact normalization_check a
  rw [he]
  exact product_mem_core _ _

set_option maxRecDepth 8192 in
private theorem extra_check : ∀ a : Fin (generatorWords 3).length, ∀ v : Fin 4,
    (wordPerm (generatorWords 3) a * fastWord [2]) ⟨v.val, by omega⟩ =
      (fastWord [2] * wordPerm (generatorWords 3) a) ⟨v.val, by omega⟩ := by
  decide +kernel

private theorem extra_mem : (word [2] : He) ∈ centralizerTwoCandidate 3 := by
  refine ⟨(word [2]).property, centralizes_of_generators 3 _ ?_⟩
  intro a
  apply Held.eq_of_four_point_images
  rw [map_mul, map_mul, ← wordPerm_eq, ← fastWord_eq]
  exact extra_check a

set_option maxRecDepth 8192 in
private theorem displacement_check :
    (witnessPerm * fastWord [2] * witnessPerm⁻¹) 1 = 1318 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem exclusion_check : ∀ i : Fin 1024, normalFormAction i 1 ≠ 1318 := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem displacement : witness * (word [2] : He) * witness⁻¹ ∉ representative := by
  apply not_mem_representative_of_image _ 1 1318 _ exclusion_check
  rw [map_mul, map_mul, map_inv, ← fastWord_eq]
  rw [← witnessPerm_eq]
  exact displacement_check

private theorem outside_check :
    (wordPerm (generatorWords 3) ⟨0, by decide⟩ * fastWord [1]) 0 ≠
      (fastWord [1] * wordPerm (generatorWords 3) ⟨0, by decide⟩) 0 := by decide +kernel

private theorem outside : (word [1] : He) ∉ centralizer (ambient 3 : Set He) := by
  apply not_centralizes_of_generator 3 _ ⟨0, by decide⟩
  rw [← fastWord_eq]
  exact outside_check

theorem card : Nat.card (centralizerTwoCandidate 3) = 512 :=
  card_of_displacement 3 (Or.inr rfl) witness (word [2]) (word [1])
    normalizes extra_mem displacement (word [1]).property outside

theorem extension : ∃ t : He,
    t ∈ centralizer (ambient 3 : Set He) ∧ orderOf t = 3 ∧
    t ∈ normalizer (coreCandidate 3 : Set He) ∧
    t ∉ normalizer (centralizerTwoCandidate 3 : Set He) := by
  refine ⟨witness, centralizes, order_three, normalizes, ?_⟩
  intro h
  exact displacement ((mem_normalizer_iff.mp h _).mp extra_mem).1

end RowThree
end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates.ExtensionCertificates
