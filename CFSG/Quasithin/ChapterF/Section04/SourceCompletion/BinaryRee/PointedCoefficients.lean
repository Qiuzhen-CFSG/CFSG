module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.PointedTransport
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.EndpointSeparation
/-!
# Literal root coefficients for the binary Ree pointed-pair selection

The finite census uses the actual root-one and root-nine elements and the two
Weyl lifts. The local word certificates use their verified coordinate Sylow
preimages. This module proves their exact agreement through the original
completion maps, including root-nine as the square of certificate generator
two. Consequently the concrete census and the three certified exclusions imply
the canonical braid consumed by the full marked recognition theorem.

The census and exclusion producers are separate finite modules; the final
source recognition imports and discharges them. There is no additional marking
or ambient order premise hidden in these coefficient comparisons.

Source: Aschbacher--Smith F.4.8 and F.4.15--17, pp.278,281--283;
Shinoda root conventions in the verified ReeTwo parabolic comparison.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.PointedCoefficients
open Theory.GroupTheory ReeTwo
open ReeTwo.ParabolicMarkedComparison
open ReeF4.Parabolics.Binary.FixedGeometry
local notation "B" => Tits.ExceptionalParabolics.FullRee.B
local notation "P" => Tits.ExceptionalParabolics.FullRee.first
local notation "Q" => Tits.ExceptionalParabolics.FullRee.second
open Tits.AmalgamRigidity.FullRee

def u : B := borelEquiv SylowModel.rootOne
def z : B := borelEquiv (SylowModel.root 9)
def r : P := Verified.firstEquiv Centralizer.weyl
def s : Q := SecondExtension.reflection

theorem u_coe : (u : ReeF4.Model 0) = Ambient.rootOne := SecondExtension.inclusion_rootOne

theorem z_coe : (z : ReeF4.Model 0) = Ambient.root 9 := SecondExtension.inclusion_root 9

theorem r_coe : (r : ReeF4.Model 0) = weylLift 0 .suzuki := by
  change (Verified.firstEquiv Centralizer.weyl : ReeF4.Model 0) = _
  rw [Verified.firstEquiv_coe, Verified.localMap_weyl]
  rfl

theorem s_coe : (s : ReeF4.Model 0) = weylLift 0 .linear := rfl

/-- Exact literal finite-model census input, with a single common Borel conjugator. -/
def ModelCensus : Prop :=
  ∀ x y : ReeF4.Model 0, x ∈ P → y ∈ Q → x ∉ B → y ∉ B →
    x ^ 2 = 1 → y ^ 2 = 1 →
    ∃ b : B, ∃ i j : Bool,
      x = b * (if i then Ambient.root 9 * weylLift 0 .suzuki else weylLift 0 .suzuki) *
        (b : ReeF4.Model 0)⁻¹ ∧
      y = b * (if j then Ambient.rootOne⁻¹ * weylLift 0 .linear * Ambient.rootOne
        else weylLift 0 .linear) * (b : ReeF4.Model 0)⁻¹

variable {G : Type*} [Group G] (c : Completion G)

theorem source_u : c.middle u = BadBraid.generator c 0 := rfl

theorem source_z : c.middle z = BadBraid.generator c 2 ^ 2 :=
  (BadBraid.generator_square_root_nine c).symm

theorem source_r : c.left r = BadBraid.generator c 3 := rfl

theorem source_s : c.right s = BadBraid.generator c 4 := rfl

/-- The concrete coefficients bridge the finite census and replay exclusions
to the canonical Weyl braid used by the full recognition theorem. -/
theorem canonicalBraid_of_census_and_exclusions (hsmall : c.Small) (hcensus : ModelCensus)
    (hshift : (BadBraid.generator c 3 * (BadBraid.generator c 0)⁻¹ *
      BadBraid.generator c 4 * BadBraid.generator c 0) ^ 8 ≠ 1)
    (htwist : (BadBraid.generator c 2 ^ 2 * BadBraid.generator c 3 *
      BadBraid.generator c 4) ^ 8 ≠ 1)
    (hboth : (BadBraid.generator c 2 ^ 2 * BadBraid.generator c 3 *
      (BadBraid.generator c 0)⁻¹ * BadBraid.generator c 4 * BadBraid.generator c 0) ^ 8 ≠ 1) :
    Tits.ExceptionalParabolics.FullRee.CompletionPresentation.CanonicalBraid c := by
  have h : (c.left r * c.right s) ^ 8 = 1 :=
    Completion.standard_braid_of_four_pair_census c hsmall u z r s
      (by
        intro x y hx hy hnx hny hx2 hy2
        simpa only [u_coe, z_coe, r_coe, s_coe] using hcensus x y hx hy hnx hny hx2 hy2)
      (by simpa only [source_u, source_r, source_s] using hshift)
      (by simpa only [source_z, source_r, source_s] using htwist)
      (by simpa only [source_u, source_z, source_r, source_s] using hboth)
  rw [Tits.ExceptionalParabolics.FullRee.CompletionPresentation.canonicalBraid_iff_weyl]
  have hr : r = ⟨weylLift 0 .suzuki, weylLift_mem_seed 0 .suzuki⟩ := Subtype.ext r_coe
  have hs : s = ⟨weylLift 0 .linear, weylLift_mem_seed 0 .linear⟩ := rfl
  rwa [hr, hs] at h

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.PointedCoefficients
