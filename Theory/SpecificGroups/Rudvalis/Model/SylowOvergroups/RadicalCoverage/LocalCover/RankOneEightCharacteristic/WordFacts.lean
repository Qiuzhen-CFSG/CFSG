module
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementaryComparison
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Coset.Card

/-!
# Word facts for the marked Rudvalis eight-subgroup

The first three marked words are commuting involutions. Their conjugates by
all four local generators are short products of those same words. Eight
products are separated at point zero, and the next marked generator is
separated from them by points zero and one. Every equality is checked on
all 4060 points and transferred through the existing word comparisons.

Source: the ATLAS words and attribution in `LocalCover.Data` and its checked
`ElementaryCatalogue.Tables`. These calculations support Aschbacher--Smith
15.3.43, printed p.1140, and the local structure in GLS3 Table 5.3r.
-/
namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
open Subgroup CatalogueCertificate
set_option maxRecDepth 30000
set_option Elab.async false

/-- The three original words generating the marked eight-subgroup. -/
@[expose] public def basis (i : Fin 3) : Model :=
  elementaryGenerator i.castSucc.castSucc.castSucc

public theorem basis_mem (i : Fin 3) : basis i ∈ elementary 2 := by
  fin_cases i <;> exact subset_closure (by simp [basis])

public theorem closure_basis : closure (Set.range basis) = elementary 2 := by
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [basis]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

public theorem basis_square (i : Fin 3) : basis i * basis i = 1 := by
  have hi : (elementaryPermutation i.castSucc.castSucc.castSucc)⁻¹ =
      elementaryPermutation i.castSucc.castSucc.castSucc := by
    fin_cases i <;> rfl
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (basis i) * modelSubgroup.subtype (basis i) = 1
  simp only [basis, ← elementaryPermutation_eq]
  exact (congrArg (fun p => p * elementaryPermutation i.castSucc.castSucc.castSucc) hi).symm.trans
    (inv_mul_cancel _)

private theorem commute01 : elementaryPermutation 0 * elementaryPermutation 1 =
    elementaryPermutation 1 * elementaryPermutation 0 := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem commute02 : elementaryPermutation 0 * elementaryPermutation 2 =
    elementaryPermutation 2 * elementaryPermutation 0 := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem commute12 : elementaryPermutation 1 * elementaryPermutation 2 =
    elementaryPermutation 2 * elementaryPermutation 1 := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

public theorem basis_commute (i j : Fin 3) : Commute (basis i) (basis j) := by
  have h (a b : Fin 3) (he : elementaryPermutation a.castSucc.castSucc.castSucc *
      elementaryPermutation b.castSucc.castSucc.castSucc =
      elementaryPermutation b.castSucc.castSucc.castSucc *
      elementaryPermutation a.castSucc.castSucc.castSucc) : Commute (basis a) (basis b) := by
    apply modelSubgroup.subtype_injective
    change modelSubgroup.subtype (basis a) * modelSubgroup.subtype (basis b) =
      modelSubgroup.subtype (basis b) * modelSubgroup.subtype (basis a)
    simpa only [basis, ← elementaryPermutation_eq] using he
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact h 0 1 commute01
  · exact h 0 2 commute02
  · exact h 1 0 commute01.symm
  · exact Commute.refl _
  · exact h 1 2 commute12
  · exact h 2 0 commute02.symm
  · exact h 2 1 commute12.symm
  · exact Commute.refl _

private def eightWords : Fin 8 → Model :=
  ![1, basis 0, basis 1, basis 0 * basis 1, basis 2,
    basis 0 * basis 2, basis 1 * basis 2, basis 0 * basis 1 * basis 2]

private def eightPerms : Fin 8 → Equiv.Perm (Fin 4060) :=
  ![1, elementaryPermutation 0, elementaryPermutation 1,
    elementaryPermutation 0 * elementaryPermutation 1, elementaryPermutation 2,
    elementaryPermutation 0 * elementaryPermutation 2,
    elementaryPermutation 1 * elementaryPermutation 2,
    elementaryPermutation 0 * elementaryPermutation 1 * elementaryPermutation 2]

private theorem eight_eq (i : Fin 8) : eightPerms i = modelSubgroup.subtype (eightWords i) := by
  fin_cases i <;> simp only [eightPerms, eightWords, basis, elementaryPermutation_eq] <;> rfl

private theorem eight_mem (i : Fin 8) : eightWords i ∈ elementary 2 := by
  fin_cases i
  · exact (elementary 2).one_mem
  · exact basis_mem 0
  · exact basis_mem 1
  · exact (elementary 2).mul_mem (basis_mem 0) (basis_mem 1)
  · exact basis_mem 2
  · exact (elementary 2).mul_mem (basis_mem 0) (basis_mem 2)
  · exact (elementary 2).mul_mem (basis_mem 1) (basis_mem 2)
  · exact (elementary 2).mul_mem ((elementary 2).mul_mem (basis_mem 0) (basis_mem 1)) (basis_mem 2)

private theorem eight_separated : Function.Injective (fun i => eightPerms i 0) := by
  decide +kernel

public theorem eight_le_card : 8 ≤ Nat.card (elementary 2) := by
  let f : Fin 8 → elementary 2 := fun i => ⟨eightWords i, eight_mem i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply eight_separated
    simpa only [eight_eq] using congrArg
      (fun z : elementary 2 => modelSubgroup.subtype z.val 0) h
  simpa using Nat.card_le_card_of_injective f hf

private def nineWords : Fin 9 → Model := Fin.lastCases (elementaryGenerator 3) eightWords
private def ninePerms : Fin 9 → Equiv.Perm (Fin 4060) :=
  Fin.lastCases (elementaryPermutation 3) eightPerms

private theorem nine_eq (i : Fin 9) : ninePerms i = modelSubgroup.subtype (nineWords i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact elementaryPermutation_eq 3
  · simpa [ninePerms, nineWords] using eight_eq j

private theorem nine_mem (i : Fin 9) : nineWords i ∈ elementary 3 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change elementaryGenerator 3 ∈ elementary 3
    exact subset_closure (by simp)
  · have h : elementary 2 ≤ elementary 3 := closure_mono (by simp [Set.subset_def])
    simpa [nineWords] using h (eight_mem j)

private theorem nine_separated : Function.Injective (fun i => (ninePerms i 0, ninePerms i 1)) := by
  decide +kernel

public theorem nine_le_card : 9 ≤ Nat.card (elementary 3) := by
  let f : Fin 9 → elementary 3 := fun i => ⟨nineWords i, nine_mem i⟩
  have hf : Function.Injective f := by
    intro i j h
    apply nine_separated
    simpa only [nine_eq] using congrArg
      (fun z : elementary 3 => (modelSubgroup.subtype z.val 0, modelSubgroup.subtype z.val 1)) h
  simpa using Nat.card_le_card_of_injective f hf

private def conjugateIndex : Fin 4 → Fin 3 → Fin 8 :=
  ![![1, 2, 5], ![1, 3, 5], ![1, 2, 6], ![1, 3, 6]]

private theorem conj00 : localPermutation 0 * elementaryPermutation 0 *
    (localPermutation 0)⁻¹ = eightPerms (conjugateIndex 0 0) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj01 : localPermutation 0 * elementaryPermutation 1 *
    (localPermutation 0)⁻¹ = eightPerms (conjugateIndex 0 1) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj02 : localPermutation 0 * elementaryPermutation 2 *
    (localPermutation 0)⁻¹ = eightPerms (conjugateIndex 0 2) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj10 : localPermutation 1 * elementaryPermutation 0 *
    (localPermutation 1)⁻¹ = eightPerms (conjugateIndex 1 0) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj11 : localPermutation 1 * elementaryPermutation 1 *
    (localPermutation 1)⁻¹ = eightPerms (conjugateIndex 1 1) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj12 : localPermutation 1 * elementaryPermutation 2 *
    (localPermutation 1)⁻¹ = eightPerms (conjugateIndex 1 2) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj20 : localPermutation 2 * elementaryPermutation 0 *
    (localPermutation 2)⁻¹ = eightPerms (conjugateIndex 2 0) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj21 : localPermutation 2 * elementaryPermutation 1 *
    (localPermutation 2)⁻¹ = eightPerms (conjugateIndex 2 1) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj22 : localPermutation 2 * elementaryPermutation 2 *
    (localPermutation 2)⁻¹ = eightPerms (conjugateIndex 2 2) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj30 : localPermutation 3 * elementaryPermutation 0 *
    (localPermutation 3)⁻¹ = eightPerms (conjugateIndex 3 0) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj31 : localPermutation 3 * elementaryPermutation 1 *
    (localPermutation 3)⁻¹ = eightPerms (conjugateIndex 3 1) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

private theorem conj32 : localPermutation 3 * elementaryPermutation 2 *
    (localPermutation 3)⁻¹ = eightPerms (conjugateIndex 3 2) := by
  apply Equiv.ext
  apply Rudvalis.OrderCertificate.allFin
  decide +kernel

public theorem conjugate_basis_mem (i : Fin 4) (j : Fin 3) :
    localGenerators i * basis j * (localGenerators i)⁻¹ ∈ elementary 2 := by
  have h : localPermutation i * elementaryPermutation j.castSucc.castSucc.castSucc *
      (localPermutation i)⁻¹ = eightPerms (conjugateIndex i j) := by
    fin_cases i <;> fin_cases j
    · exact conj00
    · exact conj01
    · exact conj02
    · exact conj10
    · exact conj11
    · exact conj12
    · exact conj20
    · exact conj21
    · exact conj22
    · exact conj30
    · exact conj31
    · exact conj32
  have he : localGenerators i * basis j * (localGenerators i)⁻¹ =
      eightWords (conjugateIndex i j) := by
    apply modelSubgroup.subtype_injective
    change modelSubgroup.subtype (localGenerators i) * modelSubgroup.subtype (basis j) *
      (modelSubgroup.subtype (localGenerators i))⁻¹ = modelSubgroup.subtype _
    simpa only [basis, ← elementaryPermutation_eq,
      ← localPermutation_eq, ← eight_eq] using h
  rw [he]
  exact eight_mem _
end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
