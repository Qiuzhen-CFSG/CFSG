module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Representatives
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.WordEvaluation
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.CommuteProducts
public import Theory.GroupTheory.InvolutionOddProduct

/-!
# Transporting concrete max2 fusion certificates

The words below are the original ATLAS max2 words before the certified
conjugation into the centralizer of `a`. The distinguished translate is
multiplication by the square of the source seed. We transport genuine
conjugacies in `Model` along this conjugation; an odd product of square-one
words supplies each remaining conjugacy by the elementary dihedral argument.

Source motivation: Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65,
A.6.1--4. The ATLAS word attribution is retained in `Representatives` and
`TwoCoreCentralizer/source/README.md`.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Coordinates
open Janko4.GeneratorCertificates
open Janko4.Cardinality.KernelCount Janko4.Cardinality.KernelCount.Relations

/-- The prescribed representative in the original ATLAS subgroup. -/
def sourceRepresentative (i : Fin 11) : sourceSubgroup :=
  kernelProduct (kernelIndex i) * sourceLift (fiberIndex i)

/-- Its prescribed translate before conjugation into the literal centralizer. -/
def sourceTranslated (i : Fin 11) : sourceSubgroup :=
  sourceRepresentative i * sourceSeed ^ 2

theorem representative_eq (i : Fin 11) :
    representative i = sourceSubgroupEquivLocal (sourceRepresentative i) := by
  rw [sourceRepresentative, map_mul]
  rfl

theorem translated_eq (i : Fin 11) :
    representative i * zH = sourceSubgroupEquivLocal (sourceTranslated i) := by
  rw [sourceTranslated, map_mul, ← representative_eq, sourceEquiv_seed_sq]

/-- A source-word conjugacy remains a conjugacy after the actual max2 bridge. -/
theorem transport {v : Model} {u : sourceSubgroup} (hv : IsConj v (u : Model)) :
    IsConj v (eH (sourceSubgroupEquivLocal u)) := by
  apply hv.trans
  rw [eH_sourceSubgroupEquivLocal]
  exact isConj_iff.mpr ⟨h⁻¹, by rw [inv_inv]⟩

theorem eval_target : toMatrix t = decodeRows e0Rows :=
  representation_seed matrixA_mul_self matrixB_pow_four

theorem target_sq : t ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, eval_target, pow_two, decoded_product product_square0,
    decode_packedOne]

/-- The odd-product witness constructs conjugacy in the group itself. -/
theorem of_odd_product (u v w : Model) (n : ℕ)
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hn : Odd n)
    (hp : (u * (w * v * w⁻¹)) ^ n = 1) : IsConj v u := by
  have hw : (w * v * w⁻¹) ^ 2 = 1 := by
    calc
      _ = w * v ^ 2 * w⁻¹ := by simp only [pow_two, mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [hv, mul_one, mul_inv_cancel]
  have hc := isConj_of_involutions_odd_product u (w * v * w⁻¹) hu hw
    (hn.of_dvd_nat (orderOf_dvd_of_pow_eq_one hp))
  exact (isConj_iff.mpr ⟨w, rfl⟩).trans hc.symm

end Janko4.Cardinality.LocalInvolutionCensus.FusionCertificates
