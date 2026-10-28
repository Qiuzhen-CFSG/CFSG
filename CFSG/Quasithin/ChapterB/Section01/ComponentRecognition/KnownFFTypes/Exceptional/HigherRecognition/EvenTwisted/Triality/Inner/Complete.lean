module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inner.Source
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.CompleteSource

/-!
# Unconditional inner triality displacement through every central cover

All geometric, finite representation and scalar-field inputs are discharged.
The conclusion is the original component bound for arbitrary faithful
irreducible actions, including nonabsolute modules and the field-two case.
Source: Guralnick--Malle II, Lemma 8.6.
-/

public section
open Theory.AlgebraicGroup
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
universe u v

theorem componentInvolutionBound_source
    {R : Type u} [Group R] [Finite R] [Theory.GroupTheory.IsQuasisimple R]
    (n : ℕ) (hn : 0<n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2^n) (R ⧸ Subgroup.center R)) :
    ComponentInvolutionBound.{u,v} R n :=
  componentInvolutionBound_of_semisimple_centers n hn hmodel (fun _ _ _ _ _ _ hH _ hT =>
    SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hT)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
