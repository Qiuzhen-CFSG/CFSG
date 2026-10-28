module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Classes
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedPoints

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.CentralizerReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.OddWitnesses
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FixedClasses
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction.FreeClasses

/-!
# Assembly of the marked normalizer conjugacy classes

The fixed-vector branch reduces internally to the supplied Case II centralizer.
The other branch has actual witnesses of orders three and five, constructed
from local analysis. Nonidentity fixed-vector existence is invariant under
internal conjugacy, so the two branches cannot fuse. Reindexing their nine and
three representatives recovers exactly the twelve published table columns.

The final theorem combines the proved coverage and separation of the nine
fixed representatives with those of the three fixed-point-free representatives.
It constructs `NormalizerClassData` from the local analysis alone, discharging
the class-data input of the subsequent character-table assembly.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 5–6, pp.9–11.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

private def normalizerClassData_of_fixed_and_free
    (c₁ μ : normalizer (CaseII.E D k : Set G))
    (hc₁ : orderOf c₁ = 3) (hμ : orderOf μ = 5)
    (hfixedDistinct : Function.Injective
      (fun i => ConjClasses.mk (normalizerFixedRepresentative D k i)))
    (hfixedCovers : ∀ x, normalizerHasFixedVector D k x →
      ∃ i, IsConj x (normalizerFixedRepresentative D k i))
    (hfree : ∀ i, ¬ normalizerHasFixedVector D k (normalizerFreeRepresentative D k c₁ μ i))
    (hfreeDistinct : Function.Injective
      (fun i => ConjClasses.mk (normalizerFreeRepresentative D k c₁ μ i)))
    (hfreeCovers : ∀ x, ¬ normalizerHasFixedVector D k x →
      ∃ i, IsConj x (normalizerFreeRepresentative D k c₁ μ i)) :
    NormalizerClassData D k := by
  classical
  refine ⟨c₁, μ, hc₁, hμ, ?_, ?_⟩
  · intro i j hij
    obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ := normalizerIndex_cases i <;>
      obtain ⟨j, rfl⟩ | ⟨j, rfl⟩ := normalizerIndex_cases j
    · simp only [normalizerFullRepresentative_fixed] at hij
      exact congrArg normalizerFixedIndex (hfixedDistinct hij)
    · simp only [normalizerFullRepresentative_fixed, normalizerFullRepresentative_free] at hij
      have hconj := ConjClasses.mk_eq_mk_iff_isConj.mp hij
      exact (hfree j ((normalizerHasFixedVector_isConj D k hconj).mp
        (normalizerFixedRepresentative_hasFixedVector D k i))).elim
    · simp only [normalizerFullRepresentative_fixed, normalizerFullRepresentative_free] at hij
      have hconj := ConjClasses.mk_eq_mk_iff_isConj.mp hij
      exact (hfree i ((normalizerHasFixedVector_isConj D k hconj).mpr
        (normalizerFixedRepresentative_hasFixedVector D k j))).elim
    · simp only [normalizerFullRepresentative_free] at hij
      exact congrArg normalizerFreeIndex (hfreeDistinct hij)
  · intro x
    by_cases hx : normalizerHasFixedVector D k x
    · obtain ⟨i, hi⟩ := hfixedCovers x hx
      exact ⟨normalizerFixedIndex i, (normalizerFullRepresentative_fixed D k c₁ μ i).symm ▸ hi⟩
    · obtain ⟨i, hi⟩ := hfreeCovers x hx
      exact ⟨normalizerFreeIndex i, (normalizerFullRepresentative_free D k c₁ μ i).symm ▸ hi⟩

/-- Construct the actual twelve marked classes once the two independent
class calculations are supplied. The odd-order elements themselves and all
cross-branch separation are proved here, not included in the branch premises. -/
public theorem nonempty_normalizerClassData_of_class_branches (L : LocalAnalysisData D k)
    (hfixedDistinct : Function.Injective
      (fun i => ConjClasses.mk (normalizerFixedRepresentative D k i)))
    (hfixedCovers : ∀ t : TwistedModel,
      ∃ i, IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k i))
    (hfreeClasses : ∀ c₁ μ : normalizer (CaseII.E D k : Set G),
      orderOf c₁ = 3 → ¬ normalizerHasFixedVector D k c₁ → orderOf μ = 5 →
      Function.Injective (fun i => ConjClasses.mk (normalizerFreeRepresentative D k c₁ μ i)) ∧
        ∀ x, ¬ normalizerHasFixedVector D k x →
          ∃ i, IsConj x (normalizerFreeRepresentative D k c₁ μ i)) :
    Nonempty (NormalizerClassData D k) := by
  obtain ⟨c₁, hc₁, hc₁free⟩ := exists_normalizer_fixedPointFree_three D k L
  obtain ⟨μ, hμ, hμfree, hμ2free⟩ := exists_normalizer_fixedPointFree_five D k L
  obtain ⟨hfreeDistinct, hfreeCovers⟩ := hfreeClasses c₁ μ hc₁ hc₁free hμ
  refine ⟨normalizerClassData_of_fixed_and_free D k c₁ μ hc₁ hμ hfixedDistinct
    ?_ ?_ hfreeDistinct hfreeCovers⟩
  · intro x hx
    obtain ⟨t, ht⟩ := (normalizerHasFixedVector_iff_conjugate_centralizer D k L x).mp hx
    obtain ⟨i, hi⟩ := hfixedCovers t
    exact ⟨i, ht.trans hi⟩
  · intro i
    fin_cases i
    · exact hc₁free
    · exact hμfree
    · exact hμ2free

/-- Janko's twelve marked representatives cover and distinguish the conjugacy
classes of the actual normalizer of E. The odd-order witnesses and both class
branches are constructed from the supplied local analysis. -/
public theorem nonempty_normalizerClassData (L : LocalAnalysisData D k) :
    Nonempty (NormalizerClassData D k) :=
  nonempty_normalizerClassData_of_class_branches D k L
    (normalizerFixedRepresentative_distinct D k L)
    (normalizerCentralizer_fixedRepresentative_covers D k L)
    (normalizer_free_classes D k L)

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
