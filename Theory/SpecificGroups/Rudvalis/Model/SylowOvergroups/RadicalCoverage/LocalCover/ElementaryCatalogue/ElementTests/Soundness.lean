module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue.ElementTests.Data

/-!
# Soundness of the elementary-element certificates

Membership follows from a product in the candidate's defining generators.
Permutation equality and conjugacy transfer through the injective map to the
original degree-4060 action. A single separating point refutes a square or
commutation equality. Thus no order, Sylow, or normal-form coverage premise
is needed. See `ElementTests.Data` for the witnesses and source conventions.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate.ElementChecks

public theorem basis_mem (i j : Fin 6) (h : j ∈ basis i) : elementaryGenerator j ∈ elementary i := by
  fin_cases i <;> fin_cases j <;> simp [basis] at h
  all_goals apply Subgroup.subset_closure; simp

public theorem product_mem (i : Fin 6) (v : List (Fin 6)) (h : ∀ j ∈ v, j ∈ basis i) :
    (v.map elementaryGenerator).prod ∈ elementary i := by
  apply (elementary i).list_prod_mem
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact basis_mem i j (h j hj)

public theorem product_eq (v : List (Fin 6)) :
    (v.map elementaryPermutation).prod =
      modelSubgroup.subtype ((v.map elementaryGenerator).prod) := by
  induction v with
  | nil => rfl
  | cons j v ih =>
    change elementaryPermutation j * (v.map elementaryPermutation).prod =
      modelSubgroup.subtype (elementaryGenerator j * (v.map elementaryGenerator).prod)
    rw [elementaryPermutation_eq, ih]
    rfl

public theorem positive_result (n : Fin 16384) (i : Fin 6) (v : List (Fin 6))
    (w : List (Fin 8)) (hv : ∀ j ∈ v, j ∈ basis i)
    (hp : normalFormPermutation n = (v.map elementaryPermutation).prod)
    (hw : wordPermutation w * normalFormPermutation n * (wordPermutation w)⁻¹ =
      elementaryPermutation i) : ElementTestResult (normalForm n) := by
  refine Or.inr ⟨i, w, ?_, ?_⟩
  · have he : normalForm n = (v.map elementaryGenerator).prod := by
      apply modelSubgroup.subtype_injective
      rw [← normalFormPermutation_eq, ← product_eq]
      exact hp
    rw [he]
    exact product_mem i v hv
  · apply modelSubgroup.subtype_injective
    change modelSubgroup.subtype (localWord w) * modelSubgroup.subtype (normalForm n) *
      (modelSubgroup.subtype (localWord w))⁻¹ = modelSubgroup.subtype (elementaryGenerator i)
    simpa only [← normalFormPermutation_eq, ← wordPermutation_eq,
      ← elementaryPermutation_eq] using hw

public theorem reject_square (n : Fin 16384) (p : Fin 4060)
    (h : (normalFormPermutation n ^ 2) p ≠ p) :
    ¬ PassesElementTest (normalForm n) := by
  intro ht
  apply h
  have he := congrArg modelSubgroup.subtype ht.1
  change modelSubgroup.subtype (normalForm n) ^ 2 = 1 at he
  rw [← normalFormPermutation_eq] at he
  exact congrArg (fun q : Equiv.Perm (Fin 4060) => q p) he

public theorem reject_commute (n : Fin 16384) (j : Fin 4) (p : Fin 4060)
    (h : (normalFormPermutation n *
      (localPermutation j * normalFormPermutation n * (localPermutation j)⁻¹)) p ≠
      ((localPermutation j * normalFormPermutation n * (localPermutation j)⁻¹) *
        normalFormPermutation n) p) :
    ¬ PassesElementTest (normalForm n) := by
  intro ht
  have he := congrArg modelSubgroup.subtype (ht.2 j).eq
  change modelSubgroup.subtype (normalForm n) *
      (modelSubgroup.subtype (localGenerators j) * modelSubgroup.subtype (normalForm n) *
        (modelSubgroup.subtype (localGenerators j))⁻¹) =
    (modelSubgroup.subtype (localGenerators j) * modelSubgroup.subtype (normalForm n) *
        (modelSubgroup.subtype (localGenerators j))⁻¹) *
      modelSubgroup.subtype (normalForm n) at he
  simp only [← normalFormPermutation_eq, ← localPermutation_eq] at he
  exact h (congrArg (fun q : Equiv.Perm (Fin 4060) => q p) he)

/-- Every accepted row is justified by its checked positive witness or by
contradiction with a necessary elementary-subgroup condition. -/
public theorem result_of_rowCheck
    (positive : ∀ r, ElementTestResult (normalForm (positiveRows r).form))
    (n : Fin 16384) (h : RowCheck n) (ht : PassesElementTest (normalForm n)) :
    ElementTestResult (normalForm n) := by
  unfold RowCheck at h
  split at h
  · subst n
    exact Or.inl (by simp [normalForm])
  · split at h
    · exact False.elim (reject_square n (witnessPoint n) h ht)
    · split at h
      · exact False.elim (reject_commute n (witnessGenerator n) (witnessPoint n) h ht)
      · rw [h]
        exact positive (witnessPositive n)

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate.ElementChecks
