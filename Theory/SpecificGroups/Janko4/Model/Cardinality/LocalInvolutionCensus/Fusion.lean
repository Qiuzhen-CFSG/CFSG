module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Representatives
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_5
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_6
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_7
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_8
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_9
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation0_10
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation1_2
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation1_3
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation1_4
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation1_7
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion.Relation1_8
import Mathlib.Tactic.FinCases

/-!
# Ambient fusion of the eleven max2 census representatives

Each prescribed representative and its translate by the marked involution
is conjugate in `Janko4.Model` to the displayed target. For noncentral words,
checked square-one and odd-product identities give explicit dihedral
conjugators, using only the literal generators a, b and the max1 kernel seed.
The certified max2 bridge transports these conjugacies to the actual subgroup H.

The four lifts and eleven masks are exactly those in `Representatives`.
No local census, orbit table, simplicity, or order bound is a premise.
Source motivation: Aschbacher--Smith, `refs/quasithin.pdf`, printed pp.64--65,
A.6.1--4. ATLAS representation and word attribution, and the reproducible
certificate generator, are in `Fusion/source/README.md`.
-/

set_option backward.isDefEq.respectTransparency true

public section
namespace Janko4.Cardinality.LocalInvolutionCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation Coordinates FusionCertificates
open Janko4.GeneratorCertificates

private theorem sourceRepresentative_zero : sourceRepresentative 0 = 1 := by
  apply Subtype.ext
  apply toMatrix_injective
  rw [eval_rep_0, Subgroup.coe_one, map_one, decode_packedOne]

private theorem sourceRepresentative_one : sourceRepresentative 1 = sourceSeed ^ 2 := by
  apply Subtype.ext
  apply toMatrix_injective
  change toMatrix (sourceRepresentative 1 : Model) = toMatrix (kernelFactor 0 : Model)
  rw [eval_rep_1, eval_factor]

private theorem sourceTranslated_zero : sourceTranslated 0 = sourceSeed ^ 2 := by
  rw [sourceTranslated, sourceRepresentative_zero, one_mul]

private theorem sourceTranslated_one : sourceTranslated 1 = 1 := by
  apply Subtype.ext
  apply toMatrix_injective
  rw [eval_translated_1, Subgroup.coe_one, map_one, decode_packedOne]

attribute [local irreducible] sourceRepresentative sourceTranslated

/-- The first target is genuinely conjugate to each prescribed representative. -/
theorem firstTarget_isConj_representative (i : Fin 11) :
    IsConj (firstTarget i) (eH (representative i)) := by
  rw [representative_eq]
  fin_cases i
  · change IsConj (1 : Model) (eH (sourceSubgroupEquivLocal (sourceRepresentative 0)))
    rw [sourceRepresentative_zero, map_one, map_one]
  · change IsConj z (eH (sourceSubgroupEquivLocal (sourceRepresentative 1)))
    rw [sourceRepresentative_one, sourceEquiv_seed_sq]
    exact IsConj.refl z
  · exact transport (fuse_0_2 eval_rep_2)
  · exact transport (fuse_0_3 eval_rep_3)
  · exact transport (fuse_0_4 eval_rep_4)
  · exact transport (fuse_0_5 eval_rep_5)
  · exact transport (fuse_0_6 eval_rep_6)
  · exact transport (fuse_0_7 eval_rep_7)
  · exact transport (fuse_0_8 eval_rep_8)
  · exact transport (fuse_0_9 eval_rep_9)
  · exact transport (fuse_0_10 eval_rep_10)

/-- The second target is genuinely conjugate to the prescribed central translate. -/
theorem secondTarget_isConj_representative_mul_zH (i : Fin 11) :
    IsConj (secondTarget i) (eH (representative i * zH)) := by
  rw [translated_eq]
  fin_cases i
  · change IsConj z (eH (sourceSubgroupEquivLocal (sourceTranslated 0)))
    rw [sourceTranslated_zero, sourceEquiv_seed_sq]
    exact IsConj.refl z
  · change IsConj (1 : Model) (eH (sourceSubgroupEquivLocal (sourceTranslated 1)))
    rw [sourceTranslated_one, map_one, map_one]
  · exact transport (fuse_1_2 eval_translated_2)
  · exact transport (fuse_1_3 eval_translated_3)
  · exact transport (fuse_1_4 eval_translated_4)
  · exact transport (fuse_0_6 eval_translated_5)
  · exact transport (fuse_0_5 eval_translated_6)
  · exact transport (fuse_1_7 eval_translated_7)
  · exact transport (fuse_1_8 eval_translated_8)
  · exact transport (fuse_0_10 eval_translated_9)
  · exact transport (fuse_0_9 eval_translated_10)

/-- The complete positive ambient fusion certificate consumed by the census. -/
theorem representative_fusion (i : Fin 11) :
    IsConj (firstTarget i) (eH (representative i)) ∧
      IsConj (secondTarget i) (eH (representative i * zH)) :=
  ⟨firstTarget_isConj_representative i, secondTarget_isConj_representative_mul_zH i⟩

end Janko4.Cardinality.LocalInvolutionCensus
