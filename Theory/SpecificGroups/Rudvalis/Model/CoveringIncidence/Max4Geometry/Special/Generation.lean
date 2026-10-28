module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Structure
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Generation.Separation
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.PcComparison

/-!
# The eleven fixed words generate the Rudvalis max4 core

The existing coordinate-permutation comparison identifies the structural
point evaluator with the literal words, preserving multiplication order and
the inverse point-action convention. A checked left inverse on the images
of points 0 and 1 distinguishes their 2048 ascending binary products.
All products lie in the generated subgroup, which Structure places inside
the core. The already proved core order of 2048 forces equality.

This discharges the generation premise of the derived/Frattini assembly in
Structure. The center equality and final special-group assembly remain
separate mathematics. Source: GLS3 Table 5.3r, pp.291--292, and
Aschbacher--Smith I.2.2(7), printed pp.412--413.
-/

namespace Rudvalis.CoveringIncidence.Max4Special
open SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate
open Generation

private theorem pc_smul (i : Fin 14) (x : Fin 4060) :
    pcGenerator i • x = pcPermutation i x :=
  congrArg (fun p : Equiv.Perm (Fin 4060) => p x) (pcPermutation_eq i).symm

private theorem word_smul (w : List (Fin 14)) (x : Fin 4060) :
    Collection.eval w • x = wordMap w x := by
  induction w generalizing x with
  | nil => exact one_smul Model x
  | cons i w ih =>
    change (pcGenerator i * Collection.eval w) • x = pcPermutation i (wordMap w x)
    rw [mul_smul, ih, pc_smul]

private theorem generator_smul (i : Fin 11) (x : Fin 4060) :
    Max4Words.generator i • x = generatorMap i x := by
  rw [generator_eq]
  exact word_smul _ _

private theorem generator_pow_smul (i : Fin 11) (n : ℕ) (x : Fin 4060) :
    Max4Words.generator i ^ n • x = (generatorMap i)^[n] x := by
  induction n generalizing x with
  | zero => exact one_smul Model x
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, generator_smul, Function.iterate_succ_apply']

private theorem prod_smul (n : Fin 2048) (l : List (Fin 11)) (x : Fin 4060) :
    (l.map (fun i => Max4Words.generator i ^ (n.val / 2 ^ i.val % 2))).prod • x =
      l.foldr (fun i y => (generatorMap i)^[n.val / 2 ^ i.val % 2] y) x := by
  induction l generalizing x with
  | nil => exact one_smul Model x
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, mul_smul, List.foldr_cons,
      ih, generator_pow_smul]

public theorem binaryProduct_smul (n : Fin 2048) (x : Fin 4060) :
    binaryProduct n • x = binaryMap n x := by
  simpa only [binaryProduct, binaryMap, List.map_ofFn, Function.comp_def] using
    prod_smul n (List.ofFn (fun i : Fin 11 => i)) x

/-- The ascending binary products in the exact eleven published words are distinct. -/
public theorem binaryProduct_injective : Function.Injective binaryProduct := by
  intro i j h
  apply Fin.ext
  have h0 := congrArg (fun g : Model => g • (0 : Fin 4060)) h
  have h1 := congrArg (fun g : Model => g • (1 : Fin 4060)) h
  rw [binaryProduct_smul, binaryProduct_smul] at h0 h1
  rw [← decode_binaryMap i, ← decode_binaryMap j, h0, h1]

public theorem generated_card_lower :
    2048 ≤ Nat.card (Subgroup.closure (Set.range Max4Words.generator)) := by
  let f : Fin 2048 → Subgroup.closure (Set.range Max4Words.generator) :=
    fun n => ⟨binaryProduct n, binaryProduct_mem_generated n⟩
  have hf : Function.Injective f := fun _ _ h =>
    binaryProduct_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The fixed eleven words generate the literal two-core in the original model. -/
public theorem closure_generators_eq_core :
    Subgroup.closure (Set.range Max4Words.generator) = max4Core := by
  apply Subgroup.eq_of_le_of_card_ge closure_generators_le_core
  rw [max4Core_card]
  exact generated_card_lower

end Rudvalis.CoveringIncidence.Max4Special
