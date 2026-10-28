module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.SourceData
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.MarkedModel

/-!
# Root calculations needed for binary inversion coverage

There are two separate geometric calculations. First, involutions in the
positive subgroup must be conjugated onto the two actual root curves.
Second, the nonzero points of those curves must be conjugated to the marked
binary Tits representatives under the literal coefficient embedding.

These definitions specify the remaining calculations; they do not assert
either calculation. The consumer in `InversionCoverage` combines them with
Sylow conjugacy and the explicit odd-order witnesses.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal p.57; GLS3, Table 2.4 and section 2.4, for the root conventions.
-/

@[expose] public section

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
open EvenInvolutionGeometry Tits.InvolutionRootGeometry

/-- Coverage restricted to the literal positive fixed subgroup. The conjugacy
is in the full Ree model; no assertion about centralizers is needed. -/
def UnipotentRootCoverage (m : ℕ) : Prop :=
  ∀ t : Model m, t ∈ Parabolics.unipotent m → t ≠ 1 → t ^ 2 = 1 →
    IsLongRootInvolution t ∨ IsShortRootInvolution t

/-- The actual binary marking of every nonzero root parameter, for each
coefficient embedding. This includes the Weyl change of root coordinates. -/
def BinaryRootNormalization (m : ℕ) : Prop :=
  ∀ (e : CoefficientField 0 →+* CoefficientField m) (a : CoefficientField m), a ≠ 0 →
    IsConj (Subfield.reeMap (by simp) e (fixedGenerator .s1)) (longRootElement m a) ∧
    IsConj (Subfield.reeMap (by simp) e (fixedGenerator .s4)) (shortRootElement m a)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
