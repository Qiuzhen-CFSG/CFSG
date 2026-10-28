module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixCertificate
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel

/-!
# Identification of the literal Held rows with the local two-cores

Each catalogue generator is a checked product of the conjugated intrinsic core
words, and conversely each core word is a checked product of catalogue generators.
The certified four-point base turns these permutation calculations into actual
Held identities. Equality of the generated subgroups then transports the existing
intrinsic O₂ calculation, with exactly the published max4 conjugator and the
identity max3 conjugator.

Source: GLS3 Table 5.3p and the literal ATLAS max3/max4 and catalogue words.
The word discovery script in `source/` is diagnostic; Lean checks every identity.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Subgroup
open LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry

private def coreGen (k : Fin 2) (i : Fin 7) : He :=
  (MulAut.conj (conjugator (index k))) (CoreKernel.coreGenerator (k == 0) i).val

private def corePerm (k : Fin 2) (i : Fin 7) : Equiv.Perm (Fin 2058) :=
  (MulAut.conj (representation (conjugator (index k)))) (CoreKernel.corePerm (k == 0) i)

private theorem corePerm_eq (k : Fin 2) (i : Fin 7) :
    corePerm k i = representation (coreGen k i) := by
  simp only [corePerm, coreGen, MulAut.conj_apply, map_mul, map_inv,
    CoreKernel.representation_coreGenerator]

private def product {n : ℕ} (f : Fin n → He) (w : List (Fin n)) : He :=
  (w.map f).prod

private def permProduct {n : ℕ} (f : Fin n → Equiv.Perm (Fin 2058))
    (w : List (Fin n)) : Equiv.Perm (Fin 2058) := (w.map f).prod

private theorem representation_product {n : ℕ} (f : Fin n → He) (w : List (Fin n)) :
    representation (product f w) = permProduct (representation ∘ f) w := by
  simp only [product, permProduct, map_list_prod, List.map_map]

private def rowToCore : Fin 2 → Fin 6 → List (Fin 7)
  | 0, 0 => [2, 3]
  | 0, 1 => [0, 3]
  | 0, 2 => [0, 2, 3, 5]
  | 0, 3 => [1, 2, 3]
  | 0, 4 => [0, 1, 4, 5]
  | 0, 5 => [0, 1, 2, 4, 5]
  | 1, 0 => [0, 1, 3, 4]
  | 1, 1 => [4, 5]
  | 1, 2 => [1, 2, 3, 4]
  | 1, 3 => [0, 3]
  | 1, 4 => [0, 1, 3, 4, 5]
  | 1, 5 => [3, 4, 5]

private def coreToRow : Fin 2 → Fin 7 → List (Fin 6)
  | 0, 0 => [0, 1, 4, 5]
  | 0, 1 => [0, 3]
  | 0, 2 => [4, 5]
  | 0, 3 => [0, 4, 5]
  | 0, 4 => [2, 3, 4]
  | 0, 5 => [1, 2, 4, 5]
  | 0, 6 => []
  | 1, 0 => [1, 3, 5]
  | 1, 1 => [1, 3, 4]
  | 1, 2 => [0, 1, 2, 3, 5]
  | 1, 3 => [1, 5]
  | 1, 4 => [0, 1, 4]
  | 1, 5 => [0, 4]
  | 1, 6 => []

set_option maxRecDepth 16384 in
private theorem row_to_core_check : ∀ k : Fin 2, ∀ i : Fin 6, ∀ x : Fin 4,
    perm k i ⟨x.val, by omega⟩ =
      permProduct (corePerm k) (rowToCore k i) ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem core_to_row_check : ∀ k : Fin 2, ∀ i : Fin 7, ∀ x : Fin 4,
    corePerm k i ⟨x.val, by omega⟩ =
      permProduct (perm k) (coreToRow k i) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem row_to_core (k : Fin 2) (i : Fin 6) :
    gen k i = product (coreGen k) (rowToCore k i) := by
  apply eq_of_four_point_images
  rw [representation_product]
  simp only [Function.comp_def, ← corePerm_eq, ← perm_eq]
  exact row_to_core_check k i

private theorem core_to_row (k : Fin 2) (i : Fin 7) :
    coreGen k i = product (gen k) (coreToRow k i) := by
  apply eq_of_four_point_images
  rw [representation_product]
  simp only [Function.comp_def, ← corePerm_eq, ← perm_eq]
  exact core_to_row_check k i

private theorem product_mem_closure {n : ℕ} (f : Fin n → He) (w : List (Fin n)) :
    product f w ∈ closure (Set.range f) := by
  apply list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact subset_closure (Set.mem_range_self i)

private theorem ambient_eq_core_closure (k : Fin 2) :
    ambient (row k) = closure (Set.range (coreGen k)) := by
  rw [ambient_eq_closure]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [row_to_core]
    exact product_mem_closure _ _
  · apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    rw [core_to_row]
    exact product_mem_closure _ _

/-- Row 20 is the specified conjugate of O₂(max4); row 21 is O₂(max3).
The two-cores are intrinsic to their local groups and are mapped by actual
subtype embeddings before the published ambient conjugation. -/
theorem ambient_eq_conjugated_pCore (k : Fin 2) :
    ambient (row k) =
      ((pCore 2 (subgroup (candidate (index k)))).map
        (subgroup (candidate (index k))).subtype).map
          (MulAut.conj (conjugator (index k))).toMonoidHom := by
  have he : ambient (row k) = (CoreKernel.ambientWordCore (k == 0)).map
      (MulAut.conj (conjugator (index k))).toMonoidHom := by
    rw [ambient_eq_core_closure, CoreKernel.ambientWordCore_eq_closure,
      MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [he, CoreKernel.ambientWordCore, CoreKernel.wordCore_eq_pCore]
  fin_cases k <;> rfl

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
