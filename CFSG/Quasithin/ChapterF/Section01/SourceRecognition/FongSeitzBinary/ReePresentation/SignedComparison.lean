module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceSigned
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReePresentation.NormalizerComparison

/-!
# Original and geometric opposite-root squares for the Ree presentation

The finite signed-root equations place each complete native opposite simple
root in the corresponding source parabolic. Restricting the SAME marked
endpoint equivalence gives an injective homomorphism into the original
endpoint, with both field-generator formulas. The direct quotient adapter
uses literally Q.q; an arbitrary original or universal/geometric marking e
retains its own endpointMap. The native carriers are the actual signed
fixed-block intersections by SignedCharts.rootGroup_simple.

This extends the earlier Borel/normalizer compatibility to negative root
letters. It does not yet compare either whole parabolic or the full group.
Source: DGS Groups and Graphs, Theorem D, p.224; GLS3 2.3.6--8;
Aschbacher--Smith F.1.1--3, pp.259--261.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open ReeF4.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) {m : ℕ} (d : SourcePositive.Charts Q split m)
  (T : SourceBorel.TorusData Q split d) (W : SourceNormalizer.WeylData Q split d T)
  (R : SourceSigned.Equations Q split d T W)

/-- The entire negative simple root, mapped to the literal oriented source endpoint. -/
def negativeRootEndpoint (s : Bool) :
    AngularPresentation.Parameter m (SourceSigned.simpleIndex s) →*
      Q.tits.standardParabolic {Q.simple (SourceNormalizer.index d.orientation s)} :=
  (SourceSigned.rootHom Q split d T W false (SourceSigned.simpleIndex s)).codRestrict _
    (fun a => SourceSigned.rootHom_negative_le_endpoint Q split d T W R s ⟨a,rfl⟩)

/-- The native opposite root has an injective lift through the original or
universal/geometric marked endpoint, under the same marking e. -/
def originalNegativeRootLift (s : Bool) :
    SignedCharts.rootGroup m false (SourceSigned.simpleIndex s) →*
      parabolic L S (SourceNormalizer.index d.orientation s) :=
  (MarkedLocal.endpoint Q e (SourceNormalizer.index d.orientation s)).symm.toMonoidHom.comp
    ((negativeRootEndpoint Q split d T W R s).comp
      (SignedCharts.rootEquiv m false (SourceSigned.simpleIndex s)).symm.toMonoidHom)

theorem originalNegativeRootLift_square (s : Bool)
    (a : SignedCharts.rootGroup m false (SourceSigned.simpleIndex s)) :
    MarkedLocal.endpointMap Q e (SourceNormalizer.index d.orientation s)
      (originalNegativeRootLift Q e split d T W R s a) =
        (SourceSigned.comparison Q split d T W false (SourceSigned.simpleIndex s) a : X ⧸ Q.D) := by
  change (MarkedLocal.endpoint Q e _ ((MarkedLocal.endpoint Q e _).symm _) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem originalNegativeRootLift_injective (s : Bool) :
    Function.Injective (originalNegativeRootLift Q e split d T W R s) := by
  intro a b he
  apply (SourceSigned.comparison Q split d T W false (SourceSigned.simpleIndex s)).injective
  apply Subtype.ext
  have h := congrArg (MarkedLocal.endpointMap Q e (SourceNormalizer.index d.orientation s)) he
  simpa only [originalNegativeRootLift_square] using h

/-- The direct quotient adapter uses exactly q = QuotientGroup.mk' Q.D. -/
def quotientNegativeRootLift (s : Bool) :
    SignedCharts.rootGroup m false (SourceSigned.simpleIndex s) →*
      P (SourceNormalizer.index d.orientation s) :=
  (Q.endpointEquiv (SourceNormalizer.index d.orientation s)).symm.toMonoidHom.comp
    ((negativeRootEndpoint Q split d T W R s).comp
      (SignedCharts.rootEquiv m false (SourceSigned.simpleIndex s)).symm.toMonoidHom)

theorem quotientNegativeRootLift_square (s : Bool)
    (a : SignedCharts.rootGroup m false (SourceSigned.simpleIndex s)) :
    Q.q (quotientNegativeRootLift Q split d T W R s a) =
      (SourceSigned.comparison Q split d T W false (SourceSigned.simpleIndex s) a : X ⧸ Q.D) := by
  rw [← Q.endpointEquiv_apply]
  change (Q.endpointEquiv _ ((Q.endpointEquiv _).symm _) : X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl


/-- The original linear endpoint square preserves the literal field generator. -/
theorem originalNegativeRootLift_pair (a : ReeF4.CoefficientField m) :
    MarkedLocal.endpointMap Q e (SourceNormalizer.index d.orientation false)
      (originalNegativeRootLift Q e split d T W R false
        (SignedCharts.rootEquiv m false (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) a))) =
          SourceSigned.pair Q split d T W (false,0) a := by
  rw [originalNegativeRootLift_square]
  exact SourceSigned.comparison_pair Q split d T W false 0 a

/-- The original Suzuki endpoint square retains both nonlinear coordinates. -/
theorem originalNegativeRootLift_quartet (a b : ReeF4.CoefficientField m) :
    MarkedLocal.endpointMap Q e (SourceNormalizer.index d.orientation true)
      (originalNegativeRootLift Q e split d T W R true
        (SignedCharts.rootEquiv m false (.inr 0) (PositiveTables.rootChartEquiv m (.inr 0) (a,b)))) =
          SourceSigned.quartet Q split d T W (false,0) a b := by
  rw [originalNegativeRootLift_square]
  exact SourceSigned.comparison_quartet Q split d T W false 0 a b

/-- The endpoint map on the actual native fixed simple-block intersection. -/
def originalNegativeBlockLift (s : Bool) :
    rootBlock m (NormalizerPresentation.side s) false →*
      parabolic L S (SourceNormalizer.index d.orientation s) :=
  (originalNegativeRootLift Q e split d T W R s).comp
    (SignedCharts.simpleRootEquiv m false s).toMonoidHom

theorem originalNegativeBlockLift_injective (s : Bool) :
    Function.Injective (originalNegativeBlockLift Q e split d T W R s) :=
  (originalNegativeRootLift_injective Q e split d T W R s).comp
    (SignedCharts.simpleRootEquiv m false s).injective

theorem originalNegativeBlockLift_square (s : Bool)
    (a : rootBlock m (NormalizerPresentation.side s) false) :
    MarkedLocal.endpointMap Q e (SourceNormalizer.index d.orientation s)
      (originalNegativeBlockLift Q e split d T W R s a) =
        (SourceSigned.comparison Q split d T W false (SourceSigned.simpleIndex s)
          (SignedCharts.simpleRootEquiv m false s a) : X ⧸ Q.D) :=
  originalNegativeRootLift_square Q e split d T W R s _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReePresentation
