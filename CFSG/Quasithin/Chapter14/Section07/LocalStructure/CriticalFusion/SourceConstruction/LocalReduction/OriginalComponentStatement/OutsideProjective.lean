module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjective.Linear
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjective.Unitary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveExceptions

/-!
# All nonbinary projective degree-three components are excluded

The original Borel arguments already dispose of the contained components
and the exceptional field congruences. The remaining outside branches now
use the actual original module, cubic, and component-retaining quotient.
Together these exclude every nonbinary projective linear-three or
unitary-three component under the original source hypotheses.
Source: Aschbacher–Smith 14.7.41–43, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every original component excludes the nonbinary projective linear-three row. -/
theorem local_nonbinary_linearThree_model_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (n : ℕ) (hn : 1 < n) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2^n) := by
  rintro ⟨E,hEf,hEfin,hE,⟨e⟩⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  by_cases hin : F.Li L 1 ≤ C.map I.subtype
  · exact local_linearThree_contained_impossible d h hab structural previous faithful earlier
      I hI C hC hin hE hn e
  · rcases Nat.even_or_odd n with heven | hodd
    · exact local_even_linearThree_component_impossible d h hab structural previous faithful earlier
        I hI C hC hE hn heven e
    · exact local_outside_odd_linear_impossible d h hab structural previous faithful earlier
        I hI C hC hin hE hn hodd e

/-- Every original component excludes the nonbinary projective unitary-three row. -/
theorem local_nonbinary_unitaryThree_model_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (n : ℕ) (hn : 2 ≤ n) :
    ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 (2^n) := by
  rintro ⟨E,hEf,hEfin,J,hE,hconj,⟨e⟩⟩
  by_cases hin : F.Li L 1 ≤ C.map I.subtype
  · exact local_unitaryThree_contained_impossible d h hab structural previous faithful earlier
      I hI C hC hin J hn hE hconj e
  · rcases Nat.even_or_odd n with heven | hodd
    · exact local_outside_even_unitary_impossible d h hab structural previous faithful earlier
        I hI C hC hin J hn heven hE hconj e
    · exact local_odd_unitaryThree_component_impossible d h hab structural previous faithful earlier
        I hI C hC J hn hE hconj hodd e

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
