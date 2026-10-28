module

public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.AlternatingQuotient
public import Theory.GroupTheory.CommutingCubicTriple
public import Mathlib.Tactic.FinCases

/-!
# Literal cubic words and independent permutation images for Thompson

The three words lie in the published involution-centralizer numerator.
Their images under the actual alternating quotient are disjoint three-cycles,
so coordinate powers are independent. Cube and commutation identities in
matrices remain separate finite obligations; they are not inferred from the
permutation images. The conditional embedding below consumes exactly those
identities and is used by Chapter I's Lyons--Thompson rank filter.

Source: GLS3's Lyons involution table and Table 5.3x, as used in
Aschbacher--Smith A.2.19 and I.1.3. Original ATLAS attribution and reproducible
candidate replay are retained in `source/README.md`.
-/

namespace Thompson.InvolutionCentralizer.ElementaryThree

@[expose] public def x : Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup := AlternatingQuotient.generatorX
@[expose] public def y : Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup := AlternatingQuotient.generatorY

/-- The base cubic candidate, evaluated in the actual source word subgroup. -/
@[expose] public def base : Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup :=
  (x * y⁻¹ * x * y⁻¹ * x * y * x * y * x * y * y * x * y * x * y⁻¹ * x * y) ^ 4

/-- The three fixed conjugators. -/
@[expose] public def conjugator : Fin 3 → Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup :=
  ![1, y * x * y * y * y * y * y, x * y * x * y * x * y * y * x * y * x * y * y * y * y * x * y * x]

/-- The three literal candidates, with conjugation convention w⁻¹zw. -/
@[expose] public def triple (i : Fin 3) : Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup :=
  (conjugator i)⁻¹ * base * conjugator i

private noncomputable def permutationHom : Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup →* Equiv.Perm (Fin 9) :=
  (alternatingGroup (Fin 9)).subtype.comp Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom

private theorem image_x : permutationHom x = AlternatingQuotient.permA := by
  exact AlternatingQuotient.quotientHom_generatorX

private theorem image_y : permutationHom y = AlternatingQuotient.permB := by
  exact AlternatingQuotient.quotientHom_generatorY

/-- The three left-action permutation images, inverse to GAP's right point maps. -/
@[expose] public def image (i : Fin 3) : Equiv.Perm (Fin 9) where
  toFun j := ![![1, 2, 0, 3, 4, 5, 6, 7, 8],
    ![0, 1, 2, 8, 4, 3, 6, 7, 5],
    ![0, 1, 2, 3, 7, 5, 4, 6, 8]] i j
  invFun j := ![![2, 0, 1, 3, 4, 5, 6, 7, 8],
    ![0, 1, 2, 5, 4, 8, 6, 7, 3],
    ![0, 1, 2, 3, 6, 5, 7, 4, 8]] i j
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem permutation_triple (i : Fin 3) : permutationHom (triple i) = image i := by
  fin_cases i <;> dsimp only [triple, conjugator] <;>
    simp only [base, Matrix.cons_val_zero', Matrix.cons_val_succ',
      map_mul, map_pow, map_inv, map_one, image_x, image_y] <;> decide +kernel

/-- Each actual word has its displayed image under the published quotient map. -/
public theorem quotient_triple (i : Fin 3) :
    (Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (triple i) : Equiv.Perm (Fin 9)) = image i :=
  permutation_triple i

private theorem image_independent : Function.Injective
    (fun a : Fin 3 → Multiplicative (ZMod 3) =>
      image 0 ^ (a 0).toAdd.val * (image 1 ^ (a 1).toAdd.val * image 2 ^ (a 2).toAdd.val)) := by
  decide +kernel

/-- Independence is detected in the actual alternating quotient, without a kernel hypothesis. -/
public theorem quotient_independent : Function.Injective
    (fun a : Fin 3 → Multiplicative (ZMod 3) =>
      Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (triple 0) ^ (a 0).toAdd.val *
        (Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (triple 1) ^ (a 1).toAdd.val *
          Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (triple 2) ^ (a 2).toAdd.val)) := by
  intro a c h
  apply image_independent
  have h' := congrArg (alternatingGroup (Fin 9)).subtype h
  simp only [map_mul, map_pow] at h'
  change permutationHom (triple 0) ^ (a 0).toAdd.val *
      (permutationHom (triple 1) ^ (a 1).toAdd.val * permutationHom (triple 2) ^ (a 2).toAdd.val) =
    permutationHom (triple 0) ^ (c 0).toAdd.val *
      (permutationHom (triple 1) ^ (c 1).toAdd.val * permutationHom (triple 2) ^ (c 2).toAdd.val) at h'
  simpa only [permutation_triple] using h'

/-- It suffices to certify the base cube; all three candidates are its conjugates. -/
public theorem triple_cube_of_base_cube (hb : base ^ 3 = 1) (i : Fin 3) : triple i ^ 3 = 1 := by
  have h := @conj_pow _ _ 3 ((conjugator i)⁻¹) base
  simpa only [triple, inv_inv, hb, mul_one, inv_mul_cancel] using h

/-- The remaining matrix relations construct the actual elementary embedding. -/
public def embeddingOfRelations (hb : base ^ 3 = 1)
    (hc : ∀ i j, Commute (triple i) (triple j)) :
    (Fin 3 → Multiplicative (ZMod 3)) →* Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup :=
  Theory.GroupTheory.CommutingCubicTriple.hom triple (triple_cube_of_base_cube hb) hc

/-- No further independence premise is needed after certifying the matrix relations. -/
public theorem embeddingOfRelations_injective (hb : base ^ 3 = 1)
    (hc : ∀ i j, Commute (triple i) (triple j)) :
    Function.Injective (embeddingOfRelations hb hc) :=
  Theory.GroupTheory.CommutingCubicTriple.hom_injective_of_images triple
    (triple_cube_of_base_cube hb) hc Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom quotient_independent

end Thompson.InvolutionCentralizer.ElementaryThree
