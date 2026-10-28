module
public import Theory.LinearAlgebra.ThreeBlockProduct
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter.Size
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter.Certificates

/-!
# The center of the literal J₄ max4 two-core

Every core element has a unique fifteen-bit word expression. Three-step
triangularity makes its commutation equations linear in those bits. Twelve
checked commutator coordinates force the first twelve bits to vanish for a
central element; injection into the remaining three bits bounds the center
by eight. All word matrices and the actual core identification are imported
from their independent checked certificates.

Source: the J₄ local of Aschbacher–Smith A.3.12(17), used in source 10.2.9.
The literal ATLAS max4 provenance is in `SymmetricLinear.Model`.
-/

public section
open Theory.LinearAlgebra.ThreeBlockProduct
namespace Janko4.LocalStructure.SymmetricLinear.CoreCenter
open Janko4.LocalStructure.SymmetricLinear
open CharacteristicTwo SylowTwoPart KernelCardinality
open scoped BigOperators Matrix
attribute [local irreducible] difference block coeff inverse detector row column
  seedRepresentation pivotWord binaryProduct

 theorem image_binaryProduct (bits : Fin 15 → Fin 2) :
    seedRepresentation (binaryProduct bits) =
      (List.ofFn (fun i => 1 + ((bits i).val : ZMod 2) • difference i)).prod := by
  rw [binaryProduct, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  change seedRepresentation (pivotWord i ^ (bits i).val) = _
  rw [map_pow, image_pivotWord seedConjugate_coordinates]
  generalize bits i = b
  fin_cases b
  · simp
  · simp only [pow_one, Nat.cast_one, one_smul, difference]
    abel

 theorem central_bits_zero (bits : Fin 15 → Fin 2)
    (hz : binaryProduct bits ∈ Subgroup.center seedNormalClosure) :
    ∀ i : Fin 12, bits (Fin.castAdd 3 i) = 0 := by
  let v : Fin 12 → ZMod 2 := fun i => (bits (Fin.castAdd 3 i)).val
  have hv : coeff *ᵥ v = 0 := by
    funext k
    let z := difference (detector k)
    let L := List.ofFn (fun i => ((bits i).val : ZMod 2) • difference i)
    have hs : ∀ a ∈ L, ∀ i j, block i ≤ block j → a i j = 0 := by
      intro a ha i j hij
      obtain ⟨l,rfl⟩ := List.mem_ofFn.mp ha
      simp [Matrix.smul_apply, strict l i j hij]
    have hc : Commute (L.map (1 + ·)).prod z := by
      have hc0 : Commute (binaryProduct bits) (pivotWord (detector k)) :=
        (Subgroup.mem_center_iff.mp hz _).symm
      have hc1 : Commute (seedRepresentation (binaryProduct bits))
          (seedRepresentation (pivotWord (detector k))) := hc0.map seedRepresentation
      have hh : Commute (seedRepresentation (binaryProduct bits))
          (seedRepresentation (pivotWord (detector k)) - 1) :=
        by
          change _ * (_ - 1) = (_ - 1) * _
          rw [mul_sub, sub_mul, mul_one, one_mul, hc1.eq]
      have hdet : seedRepresentation (pivotWord (detector k)) - 1 = z := by
        rw [image_pivotWord seedConjugate_coordinates]
        dsimp only [z]
        rw [difference]
      rw [hdet, image_binaryProduct] at hh
      simpa only [L, List.map_ofFn, Function.comp_def] using hh
    have he : (L.map (fun a => a * z - z * a)).sum = 0 := prod_commutation L z
      (fun a ha b hb => triple_zero block a b z (hs a ha) (hs b hb) (strict _))
      (fun a ha b hb => triple_zero block z a b (strict _) (hs a ha) (hs b hb)) hc
    have hh : (L.map (fun a => a * z - z * a)).sum (row k) (column k) = 0 :=
      congrFun (congrFun he (row k)) (column k)
    simp only [L, List.map_ofFn, List.sum_ofFn, Matrix.sum_apply,
      Function.comp_def, z, smul_mul_assoc, mul_smul_comm, ← smul_sub,
      Matrix.smul_apply, smul_eq_mul, coefficient] at hh
    rw [Fin.sum_univ_add (a := 12) (b := 3)] at hh
    have hfirst (i : Fin 12) : (Fin.castAdd 3 i).val < 12 := i.isLt
    have hlast (i : Fin 3) : ¬ (Fin.natAdd 12 i).val < 12 := by simp
    simp only [hfirst, dif_pos, hlast, dite_false, mul_zero, Finset.sum_const_zero,
      add_zero] at hh
    have hcast (i : Fin 12) : (⟨(Fin.castAdd 3 i).val, hfirst i⟩ : Fin 12) = i :=
      Fin.ext rfl
    simpa only [hcast, Matrix.mulVec, dotProduct, v, mul_comm, Pi.zero_apply] using hh
  have hv0 : v = 0 := by
    have hh : inverse *ᵥ (coeff *ᵥ v) = inverse *ᵥ (0 : Fin 12 → ZMod 2) :=
      congrArg (fun x => inverse *ᵥ x) hv
    rw [Matrix.mulVec_mulVec, inverse_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact hh
  intro i
  have hb := congrFun hv0 i
  change ((bits (Fin.castAdd 3 i)).val : ZMod 2) = 0 at hb
  apply Fin.ext
  have hh := congrArg ZMod.val hb
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (bits (Fin.castAdd 3 i)).isLt,
    ZMod.val_zero, Fin.val_zero] using hh

 theorem center_seed_card_le : Nat.card (Subgroup.center seedNormalClosure) ≤ 8 := by
  let e : (Fin 15 → Fin 2) ≃ seedNormalClosure :=
    Equiv.ofBijective binaryProduct binaryProduct_bijective
  let f : Subgroup.center seedNormalClosure → (Fin 3 → Fin 2) := fun z i =>
    e.symm z (Fin.natAdd 12 i)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    have he (z : seedNormalClosure) : binaryProduct (e.symm z) = z := e.apply_symm_apply z
    have hx := central_bits_zero (e.symm x) (by rw [he]; exact x.property)
    have hy := central_bits_zero (e.symm y) (by rw [he]; exact y.property)
    funext i
    refine Fin.addCases (m := 12) (n := 3) (fun j => ?_) (fun j => ?_) i
    · rw [hx j, hy j]
    · exact congrFun hxy j
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fun, Nat.card_fin, show 2 ^ 3 = 8 by decide] using hh

end Janko4.LocalStructure.SymmetricLinear.CoreCenter

namespace Janko4.LocalStructure.SymmetricLinear
/-- The center of the actual max4 two-core has at most eight elements. -/
theorem max4_twoCore_center_card_le_eight :
    Nat.card (Subgroup.center (pCore 2 max4Subgroup)) ≤ 8 := by
  rw [← seedNormalClosure_eq_twoCore]
  exact CoreCenter.center_seed_card_le
end Janko4.LocalStructure.SymmetricLinear
