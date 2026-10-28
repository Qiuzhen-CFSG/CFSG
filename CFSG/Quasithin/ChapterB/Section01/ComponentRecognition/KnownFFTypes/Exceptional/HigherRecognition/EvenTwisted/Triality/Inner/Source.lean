module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inner.CoverApplication
public import Theory.Representation.Triality.RestrictedWeights.ConcreteAbsoluteSource

/-!
# Full source inner triality bound for arbitrary quasisimple covers

The genuine finite tensor classification, root displacement, character periods
and scalar descent supply the native absolute bound. The independently proved
center calculation and original component transport then give the required
inner bound on every faithful irreducible cover action, including n=1.
Only the shared semisimple-center source theorem remains explicit.
Source: Guralnick--Malle II, Lemma 8.6; Aschbacher--Smith B.1.7.
-/

public section
open Theory.AlgebraicGroup
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
universe u v

/-- The literal component estimate, with every representation premise discharged. -/
theorem componentInvolutionBound_of_semisimple_centers
    {R : Type u} [Group R] [Finite R] [Theory.GroupTheory.IsQuasisimple R]
    (n : ℕ) (hn : 0<n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2^n) (R ⧸ Subgroup.center R))
    (hcenter : ∀ (k : Type v) [Field k] [IsAlgClosed k] [CharP k 2],
      ∀ (H : Variety k) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
        ∀ T : ClosedSubgroup H, IsMaximalTorus T →
          Subgroup.center (Variety.Point H) ≤ T.toSubgroup) :
    ComponentInvolutionBound.{u,v} R n :=
  componentInvolutionBound_of_model_absoluteBound n hn hmodel
    (_root_.Triality.RestrictedWeights.Concrete.native_absoluteBound_of_semisimple_centers n hn hcenter)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
