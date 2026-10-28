module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalSourceComplete

/-!
# The completed local configuration in the guarded 12.2.13 assembly

`localConfiguration_of_many_at` constructs the split linear configuration
from the original chosen module, NoEscape and global TI. It combines the
natural H-star analysis, cyclic TI pair and rigidity at the same G and T,
including the literal L/O₂(L) action and the complement inside L.

Here that theorem discharges `localStep` in the original recognition
assembly and supplies its ambient-local `Theorem12213At` consumer. The
multiple-overgroup guard is retained throughout. Global TI and terminal
recognition remain independent source inputs: their discharge, together
with the earlier structural and seven-module inputs, belongs to
`qt-d-1222-recognition` and its upstream source producers. These conditional
consumers do not assert the full theorem before those inputs are supplied.

Source: Aschbacher–Smith, 12.2.13 and 12.2.17–27, printed pp.799–807,
with the standing multiple-overgroup hypothesis following 2.1.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Discharge the original localStep on the unchanged chosen module. The
remaining premises are global TI and the ambient recognition in 12.2.27. -/
theorem alternatives_of_ti_and_recognition_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ti : NoEscape L V → IsTISubgroup V)
    (recognize : ∀ d, SplitLinearConfiguration L V d →
      NoEscape L V → RecognizedGroup G d) : Alternatives12213 T L V :=
  alternatives_of_source_steps ti
    (localConfiguration_of_many_at h D structural modules hmany) recognize

/-- The guarded source consumer at the original G,T. Its local-configuration
premise is proved, and no natural, cyclic, rigidity or splitting callback
remains. The parent supplies the two independent global source implications. -/
theorem theorem12213_of_ti_and_recognition_of_many_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (ti : ∀ L V : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → NoEscape L V → IsTISubgroup V)
    (recognize : ∀ (L V : Subgroup G) (d : ℕ),
      Hypothesis1223 KnownSimple.IsKnownSimple T L → ChosenModule T L V →
      SplitLinearConfiguration L V d → NoEscape L V → RecognizedGroup G d) :
    Theorem12213At KnownSimple.IsKnownSimple T := by
  intro L V h D
  exact alternatives_of_ti_and_recognition_of_many_at h D structural modules hmany
    (ti L V h D) (fun d => recognize L V d h D)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
