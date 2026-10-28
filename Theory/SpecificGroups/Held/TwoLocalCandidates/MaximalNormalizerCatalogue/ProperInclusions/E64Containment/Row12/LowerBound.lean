module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Row12.Geometry
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer

/-!
# A common normalizing subgroup of order at least 9216

Adjoin the first max4 witness to the four published representative generators.
Checked conjugation identities place this subgroup in both required normalizers.
Nine short words lie in distinct right cosets of the representative: for each
pair, a checked orbit-size color change witnesses nonmembership. Multiplication
therefore injects nine copies of the already certified 1024-element subgroup.
No enumeration of the ambient Held group is used.

Source: the literal ATLAS words and degree-2058 action, GLS3 Table 5.3p.
The companion discovery script proposes the finite tables; the Lean kernel
checks every identity used below.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12
open Subgroup LocalPairs.SylowGeometry.Calculations ProperInclusions

@[expose] public def actor : Fin 5 → He
  | 0 => generator 0
  | 1 => generator 1
  | 2 => generator 2
  | 3 => generator 3
  | _ => witness 1

/-- The exhibited subgroup, defined by its five actual Held generators. -/
@[expose] public def wordSubgroup : Subgroup He := closure (Set.range actor)

private def actorTable : Fin 5 → Equiv.Perm (Fin 2058)
  | 0 => tableGen 0
  | 1 => tableGen 1
  | 2 => tableGen 2
  | 3 => tableGen 3
  | _ => representation (witness 1)

private theorem actorTable_eq (i : Fin 5) : actorTable i = representation (actor i) := by
  fin_cases i
  · exact tableGen_eq 0
  · exact tableGen_eq 1
  · exact tableGen_eq 2
  · exact tableGen_eq 3
  · rfl

private def rowPerm (j : Fin 22) (i : ℕ) : Equiv.Perm (Fin 2058) :=
  tableWord ((generatorWords j)[i]?.getD [])

private theorem rowPerm_eq (j : Fin 22) (i : ℕ) :
    rowPerm j i = representation (rowElement j i) := tableWord_eq _

private def rowPermProduct (j : Fin 22) (is : List ℕ) : Equiv.Perm (Fin 2058) :=
  (is.map (rowPerm j)).prod

private theorem rowPermProduct_eq (j : Fin 22) (is : List ℕ) :
    rowPermProduct j is = representation (rowProduct j is) := by
  simp only [rowPermProduct, rowProduct, map_list_prod, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i _
  exact rowPerm_eq j i

private def conjugateWords12 (a : Fin 5) (i : Fin 4) : List ℕ :=
  (([[[0, 1, 3], [1], [2, 3], [3]], [[0], [1], [2], [3]], [[0, 1, 2], [1, 3], [2, 3], [3]], [[0, 1, 2], [1, 3], [2, 3], [3]], [[2], [0, 2, 3], [0], [0, 1, 2]]] : List (List (List ℕ)))[a.val]?.getD [])[i.val]?.getD []

set_option maxRecDepth 8192 in
private theorem conjugation_check12 : ∀ a : Fin 5, ∀ i : Fin 4, ∀ x : Fin 4,
    (actorTable a * rowPerm 12 i.val * (actorTable a)⁻¹) ⟨x.val, by omega⟩ =
      rowPermProduct 12 (conjugateWords12 a i) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem conjugation12 (a : Fin 5) (i : Fin 4) :
    actor a * rowElement 12 i.val * (actor a)⁻¹ =
      rowProduct 12 (conjugateWords12 a i) := by
  apply eq_of_four_point_images
  simpa only [actorTable_eq, rowPerm_eq, rowPermProduct_eq, map_mul, map_inv] using
    conjugation_check12 a i

private theorem actor_normalizes12 (a : Fin 5) :
    actor a ∈ normalizer (ambient 12 : Set He) := by
  apply mem_normalizer_of_words
  intro w hw
  change w ∈ [[-4, -1, -2, -4, -2, -1], [-3, -4, 2, 1, 2, -4, -2, -1, -3, -2], [-4, 2, 1, 2, -4, -2, -1, -2], [-3, 2, 1, 2, 3, -2, -1, -2]] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · change actor a * rowElement 12 0 * (actor a)⁻¹ ∈ ambient 12
    rw [conjugation12 a ⟨0, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 12 1 * (actor a)⁻¹ ∈ ambient 12
    rw [conjugation12 a ⟨1, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 12 2 * (actor a)⁻¹ ∈ ambient 12
    rw [conjugation12 a ⟨2, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 12 3 * (actor a)⁻¹ ∈ ambient 12
    rw [conjugation12 a ⟨3, by omega⟩]
    exact rowProduct_mem _ _

public theorem wordSubgroup_le_normalizer12 :
    wordSubgroup ≤ normalizer (ambient 12 : Set He) := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact actor_normalizes12 i

private def conjugateWords20 (a : Fin 5) (i : Fin 6) : List ℕ :=
  (([[[0, 4, 5], [1, 2, 5], [2], [3, 5], [4], [5]], [[0, 1, 3, 4, 5], [1, 2, 3, 5], [2], [3], [2, 3, 4, 5], [5]], [[0, 4, 5], [1, 2, 3], [2, 5], [3, 5], [4], [5]], [[0, 4, 5], [1, 2, 3], [2, 5], [3, 5], [4], [5]], [[0], [0, 3, 4, 5], [1, 3, 4], [1, 4, 5], [0, 1, 2, 3], [1, 2, 3, 4, 5]]] : List (List (List ℕ)))[a.val]?.getD [])[i.val]?.getD []

set_option maxRecDepth 8192 in
private theorem conjugation_check20 : ∀ a : Fin 5, ∀ i : Fin 6, ∀ x : Fin 4,
    (actorTable a * rowPerm 20 i.val * (actorTable a)⁻¹) ⟨x.val, by omega⟩ =
      rowPermProduct 20 (conjugateWords20 a i) ⟨x.val, by omega⟩ := by
  decide +kernel

private theorem conjugation20 (a : Fin 5) (i : Fin 6) :
    actor a * rowElement 20 i.val * (actor a)⁻¹ =
      rowProduct 20 (conjugateWords20 a i) := by
  apply eq_of_four_point_images
  simpa only [actorTable_eq, rowPerm_eq, rowPermProduct_eq, map_mul, map_inv] using
    conjugation_check20 a i

private theorem actor_normalizes20 (a : Fin 5) :
    actor a ∈ normalizer (ambient 20 : Set He) := by
  apply mem_normalizer_of_words
  intro w hw
  change w ∈ [[-3, -4], [-4, -4, -4, -1, -2, -4, -2, -1], [-3, -4, 2, 1, 2, -4, -2, -1, -3, -2], [-4, 2, 1, 2, -4, -2, -1, -2], [-3, -4, -4, 2, 1, 2, 3, -2, -1, -2], [-3, 2, 1, 2, 3, -2, -1, -2]] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · change actor a * rowElement 20 0 * (actor a)⁻¹ ∈ ambient 20
    rw [conjugation20 a ⟨0, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 20 1 * (actor a)⁻¹ ∈ ambient 20
    rw [conjugation20 a ⟨1, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 20 2 * (actor a)⁻¹ ∈ ambient 20
    rw [conjugation20 a ⟨2, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 20 3 * (actor a)⁻¹ ∈ ambient 20
    rw [conjugation20 a ⟨3, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 20 4 * (actor a)⁻¹ ∈ ambient 20
    rw [conjugation20 a ⟨4, by omega⟩]
    exact rowProduct_mem _ _
  · change actor a * rowElement 20 5 * (actor a)⁻¹ ∈ ambient 20
    rw [conjugation20 a ⟨5, by omega⟩]
    exact rowProduct_mem _ _

public theorem wordSubgroup_le_normalizer20 :
    wordSubgroup ≤ normalizer (ambient 20 : Set He) := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact actor_normalizes20 i

public theorem representative_le_wordSubgroup : representative ≤ wordSubgroup := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  have he : generator i = actor ⟨i.val, by omega⟩ := by fin_cases i <;> rfl
  rw [he]
  exact subset_closure (Set.mem_range_self _)

private def cosetWord : Fin 9 → List (Fin 5)
  | 0 => []
  | 1 => [4]
  | 2 => [4, 0]
  | 3 => [4, 2]
  | 4 => [4, 0, 2]
  | 5 => [4, 2, 4]
  | 6 => [4, 0, 2, 4]
  | 7 => [4, 2, 4, 0]
  | _ => [4, 0, 2, 4, 0]

private def cosetElement (i : Fin 9) : He := ((cosetWord i).map actor).prod
private def cosetPerm (i : Fin 9) : Equiv.Perm (Fin 2058) :=
  ((cosetWord i).map actorTable).prod

private theorem cosetPerm_eq (i : Fin 9) : cosetPerm i = representation (cosetElement i) := by
  simp only [cosetPerm, cosetElement, map_list_prod, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro j _
  exact actorTable_eq j

private theorem cosetElement_mem (i : Fin 9) : cosetElement i ∈ wordSubgroup := by
  apply list_prod_mem
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact subset_closure (Set.mem_range_self _)

private def testVertex (i j : Fin 9) : Fin 2058 :=
  ⟨((([[0, 1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 3, 1, 1, 1, 1, 1, 1], [3, 3, 0, 1, 1, 1, 1, 1, 1], [1, 1, 1, 0, 3, 2, 1, 3, 1], [3, 1, 1, 3, 0, 3, 1, 2, 1], [1, 1, 2, 2, 1, 0, 3, 1, 3], [1, 3, 1, 3, 1, 3, 0, 1, 2], [1, 2, 1, 1, 2, 1, 3, 0, 3], [2, 1, 3, 1, 3, 1, 2, 3, 0]] : List (List ℕ))[i.val]?.getD [])[j.val]?.getD 0) % 2058,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
private theorem coset_separation_check : ∀ i j : Fin 9, i ≠ j →
    InnerNormalizer.orbitSizeLabel ((cosetPerm i * (cosetPerm j)⁻¹) (testVertex i j)) ≠
      InnerNormalizer.orbitSizeLabel (testVertex i j) := by
  decide +kernel

private theorem coset_separation (i j : Fin 9) (hij : i ≠ j) :
    cosetElement i * (cosetElement j)⁻¹ ∉ representative := by
  intro h
  have hc := InnerNormalizer.normalizer_mem_evenColoredGraphGroup
    InnerNormalizer.orbitSizeLabel_eq_card_orbit _ (le_normalizer h)
  have he := hc.1.2 (testVertex i j)
  apply coset_separation_check i j hij
  simpa only [cosetPerm_eq, map_mul, map_inv] using he

private def cosetEmbedding (x : Fin 9 × representative) : wordSubgroup :=
  ⟨x.2.val * cosetElement x.1,
    mul_mem (representative_le_wordSubgroup x.2.property) (cosetElement_mem x.1)⟩

private theorem cosetEmbedding_injective : Function.Injective cosetEmbedding := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have he : p.val * cosetElement i = q.val * cosetElement j :=
    congrArg Subtype.val h
  have hm : cosetElement i * (cosetElement j)⁻¹ ∈ representative := by
    have hc : cosetElement i * (cosetElement j)⁻¹ = p.val⁻¹ * q.val := by
      calc
        cosetElement i * (cosetElement j)⁻¹ =
            p.val⁻¹ * (p.val * cosetElement i) * (cosetElement j)⁻¹ := by
          simp only [inv_mul_cancel_left]
        _ = p.val⁻¹ * q.val := by
          rw [he]
          simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [hc]
    exact mul_mem (inv_mem p.property) q.property
  have hij : i = j := by
    by_contra hn
    exact coset_separation i j hn hm
  subst j
  have hpq : p = q := Subtype.ext (mul_right_cancel he)
  subst q
  rfl

/-- Nine disjoint copies of the representative give the required lower bound. -/
public theorem wordSubgroup_card_ge : 9216 ≤ Nat.card wordSubgroup := by
  have hP : 1024 ≤ Nat.card representative :=
    InnerNormalizer.representative_card_ge_of_orbit_labels
      InnerNormalizer.orbitSizeLabel_eq_card_orbit
  have h := Nat.card_le_card_of_injective _ cosetEmbedding_injective
  rw [Nat.card_prod, Nat.card_fin] at h
  exact (Nat.mul_le_mul_left 9 hP).trans h

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Row12
