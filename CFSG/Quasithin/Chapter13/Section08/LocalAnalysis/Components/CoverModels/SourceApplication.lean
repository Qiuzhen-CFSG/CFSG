module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels.ClassicalParameters
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic

/-!
# Source application of the component-cover catalogue

The finite quasisimple parameter comparison supplies the last intrinsic input
to `lift_classified_of_source`. Triple-cover recognition already identifies
the actual hexacode and binary matrix carriers using the supplied central
quotient isomorphisms. Thus only the genuine F.9.18(4) and A.3.6 alternatives
remain in the general catalogue implication.

The local application uses the literal image K* in H/O₂(H). The Fitting
centralizer bound makes this image quasisimple, and the supplied Suzuki
exclusion removes the remaining alternative. No quotient, action or covering
map is replaced by a group-family label. Proving those earlier source inputs,
including relative component normality needed for F.9.18(4), remains the
responsibility of the 13.8.15–17 assembly; this module does not assert that
those lemmas or Theorem D are complete.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.5–6,
printed p.43; F.9.18(4), pp.325–326; and 13.8.17, p.953 (PDF p.970).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.SourceApplication

open Subgroup Theory.GroupTheory
open Chapter1.Section02.LocalModels Models

/-- The full covering comparison, with the classical parameter and M₂₂
recognition inputs discharged under the original finite quasisimple hypotheses.
The earlier source classification conclusions remain explicit. -/
theorem classified_of_source {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (hF : F918Models G)
    (hA : IsSimpleGroup G ∨
      (Nonempty (center G ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel G)) :
    ComponentModelOrSuzuki G :=
  lift_classified_of_source hF hA (ClassicalParameters.classicalCoverParameters G)

/-- Apply the catalogue to the actual K* ≤ H/O₂(H), using the earlier
Fitting-centralizer conclusion and the Suzuki exclusion of 13.8.16.
The F.9.18 input concerns K*/Z(K*), with its original quotient marking. -/
theorem componentStar_model_of_source {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hc : fittingSubgroup (Source.Hstar H) ≤
      centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hF : F918Models (Source.starImage H K))
    (hA : IsSimpleGroup (Source.starImage H K) ∨
      (Nonempty (center (Source.starImage H K) ≃* Multiplicative (ZMod 3)) ∧
        ThreeCoverModel (Source.starImage H K)))
    (hno : ∀ m : ℕ, 1 ≤ m → ¬ Nonempty (Source.starImage H K ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ComponentModel (Source.starImage H K) := by
  let : IsQuasisimple (Source.starImage H K) :=
    star_quasisimple_of_fitting_centralizes H K hK hc
  exact (classified_of_source hF hA).of_no_suzuki hno

end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.SourceApplication
