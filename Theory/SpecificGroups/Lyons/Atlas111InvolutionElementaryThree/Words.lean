module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionAlternatingQuotient
public import Theory.GroupTheory.CommutingCubicTriple
public import Mathlib.Tactic.FinCases

/-!
# Literal cubic words and independent permutation images for Lyons

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

namespace Lyons.SimplicityCertificate.InvolutionElementaryThree

@[expose] public def x : Lyons.SimplicityCertificate.involutionLocalSubgroup := ⟨Lyons.SimplicityCertificate.involutionLocalA,
  Lyons.SimplicityCertificate.involutionLocalA_mem⟩
@[expose] public def y : Lyons.SimplicityCertificate.involutionLocalSubgroup := ⟨Lyons.SimplicityCertificate.involutionLocalB,
  Lyons.SimplicityCertificate.involutionLocalB_mem⟩

/-- The base cubic candidate, evaluated in the actual source word subgroup. -/
@[expose] public def base : Lyons.SimplicityCertificate.involutionLocalSubgroup :=
  (x * y * x * x * x * x * x * x * y) ^ 4

/-- The three fixed conjugators. -/
@[expose] public def conjugator : Fin 3 → Lyons.SimplicityCertificate.involutionLocalSubgroup :=
  ![1, y, y * x * x * y * x]

/-- The three literal candidates, with conjugation convention w⁻¹zw. -/
@[expose] public def triple (i : Fin 3) : Lyons.SimplicityCertificate.involutionLocalSubgroup :=
  (conjugator i)⁻¹ * base * conjugator i

private noncomputable def permutationHom : Lyons.SimplicityCertificate.involutionLocalSubgroup →* Equiv.Perm (Fin 11) :=
  (alternatingGroup (Fin 11)).subtype.comp Lyons.SimplicityCertificate.AlternatingQuotient.quotient

private theorem image_x : permutationHom x = Lyons.SimplicityCertificate.AlternatingQuotient.letterA := by
  exact congrArg Subtype.val Lyons.SimplicityCertificate.AlternatingQuotient.quotient_A

private theorem image_y : permutationHom y = Lyons.SimplicityCertificate.AlternatingQuotient.letterB := by
  exact congrArg Subtype.val Lyons.SimplicityCertificate.AlternatingQuotient.quotient_B

/-- The three left-action permutation images, inverse to GAP's right point maps. -/
@[expose] public def image (i : Fin 3) : Equiv.Perm (Fin 11) where
  toFun j := ![![0, 1, 2, 3, 4, 8, 6, 7, 10, 9, 5],
    ![0, 7, 2, 3, 1, 5, 6, 4, 8, 9, 10],
    ![0, 1, 2, 6, 4, 5, 9, 7, 8, 3, 10]] i j
  invFun j := ![![0, 1, 2, 3, 4, 10, 6, 7, 5, 9, 8],
    ![0, 4, 2, 3, 7, 5, 6, 1, 8, 9, 10],
    ![0, 1, 2, 9, 4, 5, 3, 7, 8, 6, 10]] i j
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem permutation_triple (i : Fin 3) : permutationHom (triple i) = image i := by
  fin_cases i <;> dsimp only [triple, conjugator] <;>
    simp only [base, Matrix.cons_val_zero', Matrix.cons_val_succ',
      map_mul, map_pow, map_inv, map_one, image_x, image_y] <;> decide +kernel

/-- Each actual word has its displayed image under the published quotient map. -/
public theorem quotient_triple (i : Fin 3) :
    (Lyons.SimplicityCertificate.AlternatingQuotient.quotient (triple i) : Equiv.Perm (Fin 11)) = image i :=
  permutation_triple i

private theorem image_independent : Function.Injective
    (fun a : Fin 3 → Multiplicative (ZMod 3) =>
      image 0 ^ (a 0).toAdd.val * (image 1 ^ (a 1).toAdd.val * image 2 ^ (a 2).toAdd.val)) := by
  decide +kernel

/-- Independence is detected in the actual alternating quotient, without a kernel hypothesis. -/
public theorem quotient_independent : Function.Injective
    (fun a : Fin 3 → Multiplicative (ZMod 3) =>
      Lyons.SimplicityCertificate.AlternatingQuotient.quotient (triple 0) ^ (a 0).toAdd.val *
        (Lyons.SimplicityCertificate.AlternatingQuotient.quotient (triple 1) ^ (a 1).toAdd.val *
          Lyons.SimplicityCertificate.AlternatingQuotient.quotient (triple 2) ^ (a 2).toAdd.val)) := by
  intro a c h
  apply image_independent
  have h' := congrArg (alternatingGroup (Fin 11)).subtype h
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
    (Fin 3 → Multiplicative (ZMod 3)) →* Lyons.SimplicityCertificate.involutionLocalSubgroup :=
  Theory.GroupTheory.CommutingCubicTriple.hom triple (triple_cube_of_base_cube hb) hc

/-- No further independence premise is needed after certifying the matrix relations. -/
public theorem embeddingOfRelations_injective (hb : base ^ 3 = 1)
    (hc : ∀ i j, Commute (triple i) (triple j)) :
    Function.Injective (embeddingOfRelations hb hc) :=
  Theory.GroupTheory.CommutingCubicTriple.hom_injective_of_images triple
    (triple_cube_of_base_cube hb) hc Lyons.SimplicityCertificate.AlternatingQuotient.quotient quotient_independent

end Lyons.SimplicityCertificate.InvolutionElementaryThree
