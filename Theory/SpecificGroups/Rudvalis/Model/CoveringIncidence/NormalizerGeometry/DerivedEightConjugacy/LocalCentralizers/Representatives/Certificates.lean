module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.PointTests
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
import Mathlib.Data.List.FinRange

/-!
# Finite certificates for three Rudvalis centralizers

The marked three-generator eight-group and five explicit quotient lifts give
256 distinct products centralizing each representative. Point zero separates
these products; two-point rigidity proves the centralizing and commutator
identities on the original model. The commutator masks give the upper derived
bound, while explicit products of commutators recover every marked generator.

The lifts and masks were discovered with `LocalCentralizers/source/Explore.g`;
that untrusted script is not used as proof evidence. Every finite assertion
below is checked by the Lean kernel using the already compared permutations.
No new permutation tables or centralizer-order calculation are introduced.
Source motivation: GLS3 Table 5.3r and pp.291–292. The underlying ATLAS
word attribution and inverse-action convention are preserved in that source
README and `ElementaryCatalogue.PcComparison`.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers.Representatives
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover CatalogueCertificate
open RankOneEightCharacteristic
open scoped commutatorElement
set_option maxRecDepth 30000
set_option Elab.async false

-- Fix the domain instance to the derived `Group Model` instance, so that the
-- homomorphism laws can be rewritten without unfolding the large carrier.
private def toPermutation : Model →* Equiv.Perm (Fin 4060) where
  toFun := modelSubgroup.subtype
  map_one' := rfl
  map_mul' _ _ := rfl

-- The first three entries are the marked basis; the last five are quotient lifts.
private def liftIndex : Fin 3 → Fin 5 → Fin 16384 :=
  ![![11, 13, 182, 222, 310], ![6, 11, 149, 275, 624], ![35, 149, 176, 379, 595]]

/-- Eight actual model words used to generate the representative centralizer. -/
public def generator (r : Fin 3) : Fin 8 → Model :=
  ![basis 0, basis 1, basis 2, normalForm (liftIndex r 0),
    normalForm (liftIndex r 1), normalForm (liftIndex r 2),
    normalForm (liftIndex r 3), normalForm (liftIndex r 4)]
private def permutation (r : Fin 3) : Fin 8 → Equiv.Perm (Fin 4060) :=
  ![elementaryPermutation 0, elementaryPermutation 1, elementaryPermutation 2,
    normalFormPermutation (liftIndex r 0), normalFormPermutation (liftIndex r 1),
    normalFormPermutation (liftIndex r 2), normalFormPermutation (liftIndex r 3),
    normalFormPermutation (liftIndex r 4)]
private def binaryWord (r : Fin 3) (n : Fin 256) : Model :=
  (List.ofFn (fun i : Fin 8 => generator r i ^ (n.val / 2 ^ i.val % 2))).prod
private def binaryPermutation (r : Fin 3) (n : Fin 256) : Equiv.Perm (Fin 4060) :=
  (List.ofFn (fun i : Fin 8 => permutation r i ^ (n.val / 2 ^ i.val % 2))).prod
/-- Every certificate word belongs to the original local subgroup. -/
public theorem generator_mem (r : Fin 3) (i : Fin 8) : generator r i ∈ localP := by
  fin_cases i
  · exact elementary_le_localP 2 (basis_mem 0)
  · exact elementary_le_localP 2 (basis_mem 1)
  · exact elementary_le_localP 2 (basis_mem 2)
  all_goals exact normalForm_mem _

private theorem permutation_eq (r : Fin 3) (i : Fin 8) :
    permutation r i = toPermutation (generator r i) := by
  fin_cases i
  · exact elementaryPermutation_eq 0
  · exact elementaryPermutation_eq 1
  · exact elementaryPermutation_eq 2
  all_goals exact normalFormPermutation_eq _

private theorem binaryPermutation_eq (r : Fin 3) (n : Fin 256) :
    binaryPermutation r n = toPermutation (binaryWord r n) := by
  simp only [binaryPermutation, binaryWord, map_list_prod, List.map_ofFn,
    Function.comp_def, map_pow, ← permutation_eq]

private def commutatorMask : Fin 3 → Fin 8 → Fin 8 → Fin 8 :=
  ![![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 7, 5, 2],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 7, 0, 0, 6, 6],
      ![0, 0, 0, 5, 0, 6, 0, 6],
      ![0, 0, 0, 2, 0, 6, 6, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 3, 6, 5],
      ![0, 0, 0, 0, 0, 3, 6, 5],
      ![0, 0, 0, 3, 3, 0, 2, 2],
      ![0, 0, 0, 6, 6, 2, 0, 2],
      ![0, 0, 0, 5, 5, 2, 2, 0]],
    ![![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0, 2, 6, 0],
      ![0, 0, 0, 0, 0, 2, 6, 0],
      ![0, 0, 0, 2, 2, 0, 3, 0],
      ![0, 0, 0, 6, 6, 3, 0, 0],
      ![0, 0, 0, 0, 0, 0, 0, 0]]]

private def reverseWitness : Fin 3 → Fin 3 → (Fin 8 × Fin 8) × (Fin 8 × Fin 8) :=
  ![![((3, 5), (5, 6)), ((3, 7), (3, 3)), ((5, 6), (3, 7))],
    ![((3, 5), (5, 6)), ((5, 6), (3, 3)), ((3, 6), (5, 6))],
    ![((5, 6), (3, 5)), ((3, 5), (3, 3)), ((3, 6), (3, 5))]]
private def markedWord (n : Fin 8) : Model :=
  (List.ofFn (fun i : Fin 3 => basis i ^ (n.val / 2 ^ i.val % 2))).prod
private def markedPermutation (n : Fin 8) : Equiv.Perm (Fin 4060) :=
  (List.ofFn (fun i : Fin 3 => elementaryPermutation i.castSucc.castSucc.castSucc ^
    (n.val / 2 ^ i.val % 2))).prod

private theorem markedWord_mem (n : Fin 8) : markedWord n ∈ elementary 2 := by
  apply (elementary 2).list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (elementary 2).pow_mem (basis_mem i) _

private theorem basis_toPermutation (i : Fin 3) :
    toPermutation (basis i) = elementaryPermutation i.castSucc.castSucc.castSucc :=
  (elementaryPermutation_eq _).symm

private theorem markedPermutation_eq (n : Fin 8) :
    markedPermutation n = toPermutation (markedWord n) := by
  simp only [markedPermutation, markedWord, map_list_prod, List.map_ofFn,
    Function.comp_def, map_pow, basis_toPermutation]

private def reverseWord (r i : Fin 3) : Model :=
  let w := reverseWitness r i
  ⁅generator r w.1.1, generator r w.1.2⁆ *
    ⁅generator r w.2.1, generator r w.2.2⁆
private def reversePermutation (r i : Fin 3) : Equiv.Perm (Fin 4060) :=
  let w := reverseWitness r i
  ⁅permutation r w.1.1, permutation r w.1.2⁆ *
    ⁅permutation r w.2.1, permutation r w.2.2⁆

private theorem reversePermutation_eq (r i : Fin 3) :
    reversePermutation r i = toPermutation (reverseWord r i) := by
  simp only [reversePermutation, reverseWord, map_mul, map_commutatorElement,
    ← permutation_eq]

private theorem commutator_mem_local {x y : Model} (hx : x ∈ localP) (hy : y ∈ localP) :
    ⁅x, y⁆ ∈ localP :=
  localP.mul_mem (localP.mul_mem (localP.mul_mem hx hy) (localP.inv_mem hx))
    (localP.inv_mem hy)

private theorem centralizes : ∀ (r : Fin 3) (j : Fin 8),
    (permutation r j * normalFormPermutation (representativeIndex r)) 0 =
      (normalFormPermutation (representativeIndex r) * permutation r j) 0 ∧
    (permutation r j * normalFormPermutation (representativeIndex r)) 1 =
      (normalFormPermutation (representativeIndex r) * permutation r j) 1 := by
  decide +kernel

private theorem commutator_points : ∀ (r : Fin 3) (i j : Fin 8),
    (⁅permutation r i, permutation r j⁆) 0 = markedPermutation (commutatorMask r i j) 0 ∧
    (⁅permutation r i, permutation r j⁆) 1 = markedPermutation (commutatorMask r i j) 1 := by
  decide +kernel

private theorem reverse_points : ∀ (r i : Fin 3),
    reversePermutation r i 0 = elementaryPermutation i.castSucc.castSucc.castSucc 0 ∧
    reversePermutation r i 1 = elementaryPermutation i.castSucc.castSucc.castSucc 1 := by
  decide +kernel

private theorem separated0 :
    (List.ofFn (fun n : Fin 256 => binaryPermutation 0 n 0)).Nodup := by
  decide +kernel

private theorem separated1 :
    (List.ofFn (fun n : Fin 256 => binaryPermutation 1 n 0)).Nodup := by
  decide +kernel

private theorem separated2 :
    (List.ofFn (fun n : Fin 256 => binaryPermutation 2 n 0)).Nodup := by
  decide +kernel

private theorem separated (r : Fin 3) :
    Function.Injective (fun n : Fin 256 => binaryPermutation r n 0) := by
  apply List.nodup_ofFn.mp
  fin_cases r
  · exact separated0
  · exact separated1
  · exact separated2

/-- The pairwise commutators of the eight generators lie in the marked group. -/
public theorem generator_commutator_mem (r : Fin 3) (i j : Fin 8) :
    ⁅generator r i, generator r j⁆ ∈ elementary 2 := by
  have he : ⁅generator r i, generator r j⁆ = markedWord (commutatorMask r i j) := by
    apply eq_of_two_points
      (commutator_mem_local (generator_mem r i) (generator_mem r j))
      (elementary_le_localP 2 (markedWord_mem _))
    · change toPermutation ⁅generator r i, generator r j⁆ 0 =
        toPermutation (markedWord (commutatorMask r i j)) 0
      simpa only [map_commutatorElement, ← permutation_eq, ← markedPermutation_eq]
        using (commutator_points r i j).1
    · change toPermutation ⁅generator r i, generator r j⁆ 1 =
        toPermutation (markedWord (commutatorMask r i j)) 1
      simpa only [map_commutatorElement, ← permutation_eq, ← markedPermutation_eq]
        using (commutator_points r i j).2
  rw [he]
  exact markedWord_mem _

private theorem reverse_eq (r i : Fin 3) : reverseWord r i = basis i := by
  apply eq_of_two_points
    (localP.mul_mem
      (commutator_mem_local (generator_mem r _) (generator_mem r _))
      (commutator_mem_local (generator_mem r _) (generator_mem r _)))
    (elementary_le_localP 2 (basis_mem i))
  · change toPermutation (reverseWord r i) 0 = modelSubgroup.subtype (basis i) 0
    simpa only [← reversePermutation_eq, basis, ← elementaryPermutation_eq]
      using (reverse_points r i).1
  · change toPermutation (reverseWord r i) 1 = modelSubgroup.subtype (basis i) 1
    simpa only [← reversePermutation_eq, basis, ← elementaryPermutation_eq]
      using (reverse_points r i).2
private theorem generator_mem_centralizer (r : Fin 3) (i : Fin 8) :
    generator r i ∈ centralizerAt (representative r) := by
  refine ⟨generator_mem r i, mem_centralizer_singleton_iff.mpr ?_⟩
  apply commute_of_two_points (generator_mem r i) (representative_mem r)
  · change toPermutation (generator r i) (modelSubgroup.subtype (representative r) 0) =
      modelSubgroup.subtype (representative r) (toPermutation (generator r i) 0)
    simpa only [representative, ← normalFormPermutation_eq, Equiv.Perm.mul_apply, permutation_eq] using
      (centralizes r i).1
  · change toPermutation (generator r i) (modelSubgroup.subtype (representative r) 1) =
      modelSubgroup.subtype (representative r) (toPermutation (generator r i) 1)
    simpa only [representative, ← normalFormPermutation_eq, Equiv.Perm.mul_apply, permutation_eq] using
      (centralizes r i).2

/-- The subgroup generated by the certified eight words. -/
@[expose] public def generated (r : Fin 3) : Subgroup Model := closure (Set.range (generator r))

private theorem generator_mem_generated (r : Fin 3) (i : Fin 8) :
    generator r i ∈ generated r := subset_closure ⟨i, rfl⟩

/-- All eight generators centralize the literal representative. -/
public theorem generated_le (r : Fin 3) : generated r ≤ centralizerAt (representative r) := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact generator_mem_centralizer r i

private theorem binaryWord_mem (r : Fin 3) (n : Fin 256) : binaryWord r n ∈ generated r := by
  apply (generated r).list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (generated r).pow_mem (generator_mem_generated r i) _

/-- Point zero separates 256 binary products of the certified generators. -/
public theorem generated_card (r : Fin 3) : 256 ≤ Nat.card (generated r) := by
  let f : Fin 256 → generated r := fun n => ⟨binaryWord r n, binaryWord_mem r n⟩
  have hf : Function.Injective f := by
    intro i j h
    apply separated r
    simpa only [binaryPermutation_eq] using congrArg
      (fun z : generated r => toPermutation z.val 0) h
  simpa using Nat.card_le_card_of_injective f hf

/-- Products of commutators recover the three original marked generators. -/
public theorem le_derived (r : Fin 3) : elementary 2 ≤ ⁅generated r, generated r⁆ := by
  rw [← closure_basis]
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [← reverse_eq r i]
  exact (⁅generated r, generated r⁆).mul_mem
    (commutator_mem_commutator (generator_mem_generated r _) (generator_mem_generated r _))
    (commutator_mem_commutator (generator_mem_generated r _) (generator_mem_generated r _))

end Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers.Representatives
