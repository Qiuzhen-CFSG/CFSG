module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer

/-!
# Applying the split index reduction to the literal triality residual

The elementary pullback theorems supply exactly the normality and index inputs
of `residual_mem_complement_range_of_elementary_index`. Quotient faithfulness
then also discharges the central-kernel coprimality used by that theorem.
The alternative unipotent-factorization consumer derives normality and index
together. Its matrix-factorization premise remains explicit until the split
geometry is established; these are conditional consumers, including q = 3.

Source: Aschbacher–Smith A.2.17, printed p.39, especially (*) and the triality
case; GLS3 §§2.4, 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups

namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
open Parabolics

/-- The split geometric inputs imply the required reverse residual containment
for the original complement map and the original central quotient. -/
theorem residual_mem_complement_range_of_split {P : Parameters} (hp : Odd P.prime)
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hnormal : splitCentralizer D ≤ Subgroup.normalizer (splitComplementSubgroup D C))
    (hindex : Nat.Coprime P.prime
      ((splitComplementSubgroup D C).subgroupOf (splitCentralizer D)).index)
    (hj : Function.Injective (complementHom D C)) (x : residual P) :
    x.val.val ∈ (complementHom D C).range :=
  residual_mem_complement_range_of_elementary_index D C hcomm
    (elementaryCentralizerHom_normal_of_split D C hp hcomm hnormal)
    (elementaryCentralizerHom_coprime_index_of_split D C hp hcomm hnormal hindex) hj x

/-- Highest-root unipotent factorization supplies the elementary normality and
index, then the original quotient theorem gives the literal residual containment.
Only complementary quotient faithfulness remains besides the geometric premise. -/
theorem residual_mem_complement_range_of_highest_factorization
    {P : Parameters} (hp : Odd P.prime)
    (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)
    (hcomm : ∀ a b, Commute (D.centralFixedEmbedding a) (splitComplementHom D C b))
    (hf : HighestUnipotentFactorization D C)
    (hj : Function.Injective (complementHom D C)) (x : residual P) :
    x.val.val ∈ (complementHom D C).range := by
  obtain ⟨hnormal, hindex⟩ :=
    elementaryCentralizerHom_normal_coprime_of_highest_factorization D C hp hcomm hf
  exact residual_mem_complement_range_of_elementary_index D C hcomm hnormal hindex hj x

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex
