module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source

/-!
# The finite natural-line calculation for the preliminary displacement

In a marked binary natural section A/N, a maximal subgroup preserving a
line E/N acts on that line's quotient through its Levi factor. Its normal
two-subgroups consequently have displacement in E. This contract keeps the
actual coordinate homomorphism, its intrinsic kernel and conjugation action.
Preliminary.NaturalAction proves this finite-module contract, so it is not
an assumption of the MS93 theorem.

Source: the natural-module implication preceding the sharpening in
Meierfrankenfeld--Stellmacher (1993), (4.5.3)(ii), printed p.898.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
universe u

/-- The point-parabolic radical calculation on a literal natural quotient.
Preliminary.NaturalAction supplies its proof to the source application. -/
def NaturalLineAction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (π : G →* SL)
    (A N P T E : Subgroup G),
    Function.Surjective π → π.ker ≤ P → IsCoatom P →
    RankOnePairing.NaturalFactor π ⊤ A N →
    N ≤ E → E ≤ A → N.relIndex E = 2 →
    P ≤ normalizer E → T ≤ P → P ≤ normalizer T → IsPGroup 2 T →
    ⁅A, T⁆ ≤ E

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
