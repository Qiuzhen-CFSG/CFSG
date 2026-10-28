module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Frattini
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.CaseFourSource

/-!
# Excluding distance four in the original fourth MS alternative

The fourth alternative of C.1.34 has Z(Q) strictly below Phi(Q). At critical
distance four, the original MS93 radius facts give central involutory
commutators in the actual amalgam core, hence Phi(core) lies in its center.
Transport along the genuine core isomorphism contradicts the fourth
alternative. Evenness and the common lower bound then give b > 4.

The original 13.6.22 application consequently constructs the entire higher
layer input from prescribed replacement. It retains that separately owned
MS93 (4.4.4) premise, with no distance bound, center-cardinality theorem,
or distance-four quotient classification required.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.34(4),
pp.136--137, and 13.6.22, pp.932--933; Meierfrankenfeld--Stellmacher (1993),
(4.6.9), p.908, and (4.4), pp.890--894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Source
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn

variable {M G : Type*} [Group M] [Finite M] [Group G]
  {L R : Subgroup M} {K T S : Subgroup G}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual fourth alternative excludes b=4 using its strict Frattini section. -/
theorem caseFour_source_distance_gt_four_original
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K T S e)
    (common : CommonFacts R source geometry)
    (f : core R (alpha R) ≃* msQ K T) : 4 < geometry.b R := by
  have hlarge := common.large_distance
  have heven := geometry.even (alpha R) rfl
  change Even (geometry.b R) at heven
  obtain ⟨n,hn⟩ := heven
  by_contra hle
  have hb : geometry.b R = 4 := by omega
  have hphi := DistanceFour.core_frattini_le_center_of_distance_four common hb
  have hphiQ : frattini (msQ K T) ≤ center (msQ K T) := by
    rw [← frattini_map_equiv f, ← center_map_equiv f]
    exact map_mono hphi
  exact (caseFour_center_lt_frattini e h).not_ge (map_mono hphiQ)

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open DistanceEight.PathCentrality
universe u
variable {J : Type u} [Group J] [Finite J] {κ : CFSG.Quasithin.GroupClass.{u}}
  {K T S : Subgroup J}

/-- The original realized fourth-case source has critical distance greater than four. -/
theorem realized_distance_gt_four
    {hMS : LinearThreeMSPair κ K T 1 (ZMod 2)}
    {e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group}
    (d : Realization.Data hMS e) (h : CaseFour K T S e) :
    4 < d.setup.geometry.b d.setup.reduction.radical :=
  caseFour_source_distance_gt_four_original e h d.common d.coreEquiv

/-- The original checked-center identity now retains only prescribed replacement
from MS93 (4.4.4); the distance-four exclusion is discharged. -/
theorem sourceSpecialized_checked_commutator_of_replacement
    (L T : Subgroup J) (z v : J) (hK : K ∈ Yz L T z v) (hv : v ^ 2 = 1)
    (hn : Tv T v ≤ normalizer (K : Set J))
    (hMS : LinearThreeMSPair κ K (Tv T v) 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : CaseFour K (Tv T v) S e)
    (replacement : ∀ {a a'} (p : CriticalPath
      (Realization.ofSourceSpecialized L T z v hK hn hMS e h).setup.reduction.radical
      (Realization.ofSourceSpecialized L T z v hK hn hMS e h).setup.geometry a a'),
      HasTurnConjugators _ p → PrescribedReplacement _ p) :
    ⁅sourceZ0 K v hK.1.1,K⁆ = sourceU K := by
  let d := Realization.ofSourceSpecialized L T z v hK hn hMS e h
  exact sourceSpecialized_checked_commutator_of_earlier L T z v hK hv hn hMS e h
    (Source44.SourceEarlier.earlier d.common (realized_distance_gt_four d h) replacement)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Source
