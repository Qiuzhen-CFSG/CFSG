module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
/-!
# Squarefree multiplication of the literal seed operators

Commutativity makes the increasing product independent of ordering. A repeated
index annihilates a product by the certified square-zero relation. These facts
prove degree-compatible multiplication for the published homogeneous spaces,
and the saved basis expansions show that their supremum is the whole algebra.
See `IntrinsicAlgebra/source/README.md` for the coordinate and source conventions.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open MultiplicationCertificate

lemma operatorMonomial_empty : operatorMonomial ∅ = 1 := by
  simp [operatorMonomial]

set_option maxRecDepth 10000 in
lemma operatorMonomial_insert (i : Fin 10) (s : Finset (Fin 10)) (hi : i ∉ s) :
    operatorMonomial (insert i s) = operator i * operatorMonomial s := by
  have hp : ((insert i s).sort (· ≤ ·)).Perm (i :: s.sort (· ≤ ·)) := by
    apply List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (by simp [hi]) |>.mpr
    intro a
    simp
  have hc : (((insert i s).sort (· ≤ ·)).map operator).Pairwise Commute := by
    apply List.pairwise_map.mpr
    exact List.pairwise_of_forall (fun i j => operator_mul_comm i j)
  change (((insert i s).sort (· ≤ ·)).map operator).prod = _
  calc
    _ = ((i :: s.sort (· ≤ ·)).map operator).prod :=
      List.Perm.prod_eq' (M := SmallMatrix) (hp.map operator) hc
    _ = operator i * operatorMonomial s := rfl

lemma operator_mul_monomial_of_mem (i : Fin 10) (s : Finset (Fin 10)) (hi : i ∈ s) :
    operator i * operatorMonomial s = 0 := by
  conv_lhs => rw [← Finset.insert_erase hi, operatorMonomial_insert _ _ (Finset.notMem_erase _ _)]
  rw [← mul_assoc, operator_mul_self, zero_mul]

lemma operatorMonomial_mul_of_disjoint (s t : Finset (Fin 10)) (h : Disjoint s t) :
    operatorMonomial s * operatorMonomial t = operatorMonomial (s ∪ t) := by
  induction s using Finset.induction_on with
  | empty => simp [operatorMonomial_empty]
  | @insert i s hi ih =>
    obtain ⟨hit, hst⟩ := Finset.disjoint_insert_left.mp h
    rw [operatorMonomial_insert _ _ hi, mul_assoc, ih hst,
      Finset.insert_union, operatorMonomial_insert _ _ (by simp [hi, hit])]

lemma operatorMonomial_mul_of_not_disjoint (s t : Finset (Fin 10)) (h : ¬ Disjoint s t) :
    operatorMonomial s * operatorMonomial t = 0 := by
  obtain ⟨i, his, hit⟩ := Finset.not_disjoint_iff.mp h
  conv_lhs => lhs; rw [← Finset.insert_erase his,
    operatorMonomial_insert _ _ (Finset.notMem_erase _ _)]
  rw [(generatedAlgebra_commute (operator_mem_generatedAlgebra i)
    (operatorMonomial_mem_generatedAlgebra (s.erase i))).eq,
    mul_assoc, operator_mul_monomial_of_mem _ _ hit, mul_zero]

lemma operatorMonomial_mem_homogeneousSpace (s : Finset (Fin 10)) :
    operatorMonomial s ∈ homogeneousSpace s.card :=
  Submodule.subset_span ⟨s, rfl, rfl⟩

lemma homogeneousSpace_mul_mem {d e : ℕ} {A B : SmallMatrix}
    (hA : A ∈ homogeneousSpace d) (hB : B ∈ homogeneousSpace e) :
    A * B ∈ homogeneousSpace (d + e) := by
  induction hA using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, hs, rfl⟩ := ha
    induction hB using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨t, ht, rfl⟩ := hb
      by_cases h : Disjoint s t
      · rw [operatorMonomial_mul_of_disjoint _ _ h, ← hs, ← ht,
          ← Finset.card_union_of_disjoint h]
        exact operatorMonomial_mem_homogeneousSpace _
      · rw [operatorMonomial_mul_of_not_disjoint _ _ h]
        exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_mul] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c hx

lemma homogeneousSpace_zero : homogeneousSpace 0 = Submodule.span (ZMod 2) {1} := by
  apply congrArg (Submodule.span (ZMod 2))
  ext a
  simp only [Set.mem_ofPred, Finset.card_eq_zero, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, rfl, rfl⟩
    exact operatorMonomial_empty
  · rintro rfl
    exact ⟨∅, rfl, operatorMonomial_empty⟩

lemma homogeneousSpace_one : homogeneousSpace 1 = operatorSpace := by
  apply congrArg (Submodule.span (ZMod 2))
  ext a
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    exact ⟨i, by simp [operatorMonomial]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨{i}, by simp, by simp [operatorMonomial]⟩

lemma homogeneousSpace_le_algebraSpan (d : ℕ) : homogeneousSpace d ≤ algebraSpan := by
  rw [← generatedAlgebra_toSubmodule_eq]
  exact Submodule.span_le.mpr fun _ ⟨s, _, hs⟩ => hs ▸ operatorMonomial_mem_generatedAlgebra s

lemma iSup_homogeneousSpace : (⨆ d, homogeneousSpace d) = algebraSpan := by
  apply le_antisymm (iSup_le homogeneousSpace_le_algebraSpan)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [algebraBasis_expansion]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [gradedBasis_eq_monomial]
  exact (le_iSup homogeneousSpace (basisSet j).card) (operatorMonomial_mem_homogeneousSpace _)

lemma iSup_homogeneousSpace_eq_generatedAlgebra :
    (⨆ d, homogeneousSpace d) = generatedAlgebra.toSubmodule := by
  rw [iSup_homogeneousSpace, generatedAlgebra_toSubmodule_eq]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
