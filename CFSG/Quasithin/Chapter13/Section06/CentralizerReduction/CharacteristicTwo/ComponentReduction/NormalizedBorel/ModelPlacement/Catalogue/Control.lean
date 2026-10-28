module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Catalogue.Carriers
public import Theory.GroupTheory.SolvableSylowControl.Marked
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.SpecificGroups.Triality.SolvableSylowControl
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment

/-!
# Solvable Sylow control in the concrete catalogue

The rank-one families use uniqueness of proper Sylow overgroups and
nonsolvability. Linear-three uses the full upper-triangular calculation;
symplectic-four uses orthogonal root orbits; G₂, genuine triality and Ree–F₄
use their checked Bruhat root-capture theorems. All statements retain the
supplied Sylow.

The unrestricted triality theorem discharges the last intrinsic branch,
without a prescribed three-complement, order bound or prior parabolic
containment. The complete-catalogue `control` theorem has no extra premise.
The earlier conditional interfaces are retained for compatibility.

Source: Aschbacher–Smith, A.2.3–4 and proof of 13.6.6, printed p.927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.Catalogue
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source
open scoped MatrixGroups

/-- The unrestricted intrinsic branch on the genuine binary triality carrier. -/
def TrialityControl : Prop := ∀ (n : ℕ) (hn : 1 < n),
  SolvableSylowControl 2 (Triality.Standard.Carrier
    (Triality.Standard.binaryParameters n (by omega)))

/-- The genuine folded-root calculation discharges the triality branch. -/
theorem trialityControl : TrialityControl := by
  intro n hn
  exact Triality.Standard.SolvableSylowControl.binary_control n hn

private theorem rankOne_control {D : Type*} [Group D] [Group.IsPerfect D]
    (facts : ∀ S : Sylow 2 D, RankOneSylowFacts S) : SolvableSylowControl 2 D := by
  intro S A hA hSA
  have hnontrivial : Nontrivial D := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    let : Subsingleton D := hs
    apply (facts S).proper.ne
    apply top_unique
    intro x _
    simpa only [Subsingleton.elim x 1] using (normalizer (S : Set D)).one_mem
  let : Nontrivial D := hnontrivial
  exact SolvableSylowControl.of_proper_overgroups
    (Group.IsPerfect.not_isSolvable D) (fun P => (facts P).unique_maximal) S A hA hSA

namespace StandardModel

/-- The branch premise of the original conditional dispatcher. Only triality
requires a supplied proof; `trialityControl` now provides it. -/
def ControlPremise {m : ℕ} (M : StandardModel m) : Prop := by
  cases M with
  | triality n hn =>
    exact SolvableSylowControl 2
      (Triality.Standard.Carrier (Triality.Standard.binaryParameters m (by omega)))
  | _ => exact True

/-- The seven other intrinsic calculations and the supplied triality branch
give control on each actual standard carrier. -/
theorem control {m : ℕ} (M : StandardModel m) (htriality : M.ControlPremise) :
    SolvableSylowControl 2 M.Carrier := by
  cases M with
  | linearTwo F hm hF =>
    have hlarge : 3 < Nat.card F := by
      rw [hF]
      have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 2 ≤ m)
      omega
    let : Group.IsPerfect PSL(2, F) := GorensteinWalter.psl2_isPerfect_of_card_gt_three F hlarge
    exact rankOne_control (D := PSL(2, F)) (rankOneSylowFacts_psl2 F m (by omega) hF)
  | unitaryThree F J hJ hm hF hconj =>
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Representation.SU3.BinaryDegree.isPerfect_projective J (by omega) hF hconj
    exact rankOne_control (D := ProjectiveSpecialUnitaryMatrixGroup J) (rankOneSylowFacts_psu3 J m (by omega) hF hconj)
  | suzuki n hn =>
    exact SolvableSylowControl.of_proper_overgroups
      (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable n (by omega))
      (fun P => (suzuki_rankOneSylowFacts n P).unique_maximal)
  | linearThree F hm hF =>
    exact Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer_of_two_le
      F (by omega) hF
  | symplecticFour F hm hF =>
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show (2 : ℕ) ^ 1 < 2 ^ m from Nat.pow_lt_pow_right (by decide) hm)
    exact Theory.SpecificGroups.SymplecticFour.solvable_overgroups_of_orthogonal_root_orbits hF hm
      (Theory.SpecificGroups.SymplecticFour.solvable_unipotent_point_orbit_orthogonal hlarge)
  | g2 F hm hF =>
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact (show (2 : ℕ) ^ 1 < 2 ^ m from Nat.pow_lt_pow_right (by decide) hm)
    exact SolvableSylowControl.of_standard Atlas.G2.LieParabolicSetup.sylow Atlas.G2.borel
      Atlas.G2.SylowNormalizer.normalizer_unipotent
      (fun A hA hU => Atlas.G2.SolvableSylowPlacement.le_borel hlarge A hU hA)
  | triality n hn => exact htriality
  | ree n hn =>
    apply SolvableSylowControl.of_standard
      (ReeF4.Parabolics.ThreeSylowContainment.positiveSylow n) (ReeF4.Parabolics.borel n)
    · change normalizer ((ReeF4.Parabolics.ThreeSylowContainment.positiveSylow n :
        Subgroup (ReeF4.Model n)) : Set (ReeF4.Model n)) = _
      rw [ReeF4.Parabolics.ThreeSylowContainment.positiveSylow_coe]
      exact ReeF4.Parabolics.unipotent_normalizer_eq_borel n
    · intro A hA hU
      rw [ReeF4.Parabolics.ThreeSylowContainment.positiveSylow_coe] at hU
      exact ReeF4.Parabolics.ThreeSylowContainment.le_borel_of_solvable hn A hA hU

/-- A uniform triality theorem supplies the triality branch of the dispatcher. -/
theorem control_of_triality (htriality : TrialityControl) {m : ℕ} (M : StandardModel m) :
    SolvableSylowControl 2 M.Carrier := by
  apply M.control
  cases M with
  | triality n hn => exact htriality m hn
  | _ => trivial

/-- Unrestricted solvable Sylow control for every concrete standard carrier. -/
theorem solvableSylowControl {m : ℕ} (M : StandardModel m) :
    SolvableSylowControl 2 M.Carrier :=
  M.control_of_triality trialityControl

end StandardModel

/-- The original conditional catalogue assembly, retained for compatibility.
The exponent-one constructors are excluded in `exists_standardModel`. -/
theorem control_of_triality {D : Type*} [Group D] [Finite D]
    {m : ℕ} (hmodel : InitialSieve.BinaryModelAt D m) (hm : 1 < m)
    (htriality : TrialityControl) : SolvableSylowControl 2 D := by
  obtain ⟨M, ⟨e⟩⟩ := exists_standardModel hmodel hm
  exact (M.control_of_triality htriality).of_equiv e

/-- Every solvable overgroup of any supplied Sylow two-subgroup normalizes
that same Sylow, throughout the complete large-field binary catalogue.
The transport uses the actual model equivalence, including central quotients. -/
theorem control {D : Type*} [Group D] [Finite D]
    {m : ℕ} (hmodel : InitialSieve.BinaryModelAt D m) (hm : 1 < m) :
    SolvableSylowControl 2 D :=
  control_of_triality hmodel hm trialityControl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.Catalogue
