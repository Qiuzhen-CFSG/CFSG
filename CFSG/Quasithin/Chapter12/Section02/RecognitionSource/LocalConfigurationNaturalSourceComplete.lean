module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceProperSix
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicSourceAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityCompleteAt

/-!
# H-star solvability, natural recognition and the original local configuration

The nonsolvable H-star construction has a proper A₇ overcomponent. Its
four-dimensional row is excluded by point-centralizer generation; its deleted
six-dimensional row contains a five-point moved module, contradicted by the
quadratic action forced by the original TI pair. Thus every original H-star
member is solvable. The proved movement and solvable full-axis recognition
supply the marked natural L/O₂(L) action in degree three, four or five.

The multiple-overgroup hypothesis is the standing source guard, at this same
G and T. The final application discharges the natural, cyclic and rigidity
steps in the original split-configuration consumer. Only the earlier local
structural and seven-module source inputs remain explicit; their discharge
and the final 12.2.13 classification belong to the local-configuration owner.
No residual, TI-layer, solvability, axis or marking callback remains.

Source: Aschbacher–Smith 12.2.18–26, printed pp.800–806, with the standing
multiple-overgroup hypothesis following 2.1.1. The quadratic obstruction is
an alternative to constructing the natural SL₂(4) layer in 12.2.19.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Source 12.2.19 for every original H-star member. -/
theorem chosen_hstar_solvable_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Group.IsSolvable H := by
  by_contra hs
  obtain ⟨X,Y,C,_,hXY,hY,_⟩ := chosen_hstar_proper_seven_full_natural_of_many_at
    h D structural modules hmany hnone hTI hH hs
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
  exact C.not_proper_overcomponent_at h D structural modules hnone hTI hH hXY hY E

/-- The complete natural-step contract at the original G,T, with all H-star
and natural-action premises discharged. -/
theorem naturalLocalAnalysis_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ d, NaturalLocalAnalysis T L V d := by
  apply naturalLocalAnalysis_of_many_and_hstar_solvable_at h D structural modules hmany hnone hTI
  exact fun _ hH _ => chosen_hstar_solvable_of_many_at h D structural modules hmany hnone hTI hH

/-- The literal split-configuration consumer, including the independently
proved cyclic and rigidity steps with the same local source inputs. -/
theorem localConfiguration_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V) :
    ∃ d, SplitLinearConfiguration L V d :=
  localConfiguration_of_source_analyses_at h D structural modules
    (fun hn ht => naturalLocalAnalysis_of_many_at h D structural modules hmany hn ht)
    (fun _ A hn ht => exists_cyclicLocalAnalysis_at h D structural A hn ht) hnone hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
