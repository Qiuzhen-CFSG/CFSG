module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.CensusTransport
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.PointedPairs.SecondCensus

/-!
# Four actual Borel orbits of binary Ree reflection pairs

The first endpoint's two involution orbits and the second endpoint's two
fixed-core orbits combine through their literal shared Borel embedding.
Thus any pair of outside-Borel involutions is a common Borel conjugate of
one of the four specified root/Weyl pairs. This is the finite pointed
selection used by the full binary Ree specialization of F.4.8.

Source: Aschbacher--Smith F.4.8, printed p.278, and the marked binary
Ree root model from Shinoda (1975), pp.81--83.
-/

public section
namespace Tits.AmalgamRigidity.FullRee.PointedPairs
open ReeTwo ParabolicMarkedComparison
open ReeF4.Parabolics.Binary.FixedGeometry
local notation "B" => Tits.ExceptionalParabolics.FullRee.B
local notation "P" => Tits.ExceptionalParabolics.FullRee.first
local notation "Q" => Tits.ExceptionalParabolics.FullRee.second

theorem reflection_pair_conjugate
    (x y : ReeF4.Model 0) (hx : x ∈ P) (hy : y ∈ Q)
    (hnx : x ∉ B) (hny : y ∉ B) (hx2 : x^2=1) (hy2 : y^2=1) :
    ∃ b : B, ∃ i j : Bool,
      x = b * (if i then Ambient.root 9 * weylLift 0 .suzuki else weylLift 0 .suzuki) *
        (b : ReeF4.Model 0)⁻¹ ∧
      y = b * (if j then Ambient.rootOne⁻¹ * weylLift 0 .linear * Ambient.rootOne
        else weylLift 0 .linear) * (b : ReeF4.Model 0)⁻¹ := by
  apply reflection_pair_conjugate_of_second_census ?_ x y hx hy hnx hny hx2 hy2
  intro a ha hn
  exact second_involution_conjugate a ha hn

end Tits.AmalgamRigidity.FullRee.PointedPairs
