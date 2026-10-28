module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoMinimalNormalBounds
import all CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceExtraspecial

/-!
# Perfectness of the original eight-field endpoint

The actual binary/eight strict critical geometry makes the original
eight-field enlargement perfect. In the linear branch that enlargement is
the original starred parabolic; in the Chapter 14 source it is exactly H.
Thus full H is perfect and equals its two-residual, before any marked
triality comparison.

The private import is an intentional proof split within this source family:
it reuses the already constructed strict selection and literal field marks.
Those private names do not occur in any public statement.

Source: DGS, Groups and Graphs (1985), (10.10)(d), pp.164--165;
Aschbacher--Smith 14.2.16 and 14.2.18, pp.986--987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePerfect
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.Reduction
open ChapterF.Source.DGS85.NoncommutingProfile.Reduction
variable {G : Type*} [Group G] {K U S : Subgroup G}

/-- The literal eight-field/binary pair has a perfect original eight-field
starred endpoint, without a critical-path or strictness hypothesis. -/
theorem eight_pair_first_perfect
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* Theory.PSL2.BinaryGroup 3)
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) :
    Group.IsPerfect (starredParabolic ![K,U] S 0) := by
  obtain ⟨u,t,hc,hne,hb,hβu,ht,htne,hD⟩ := strict_core_selection h eK eU
  have hp := original_bTwo_nonbinary_beta_isPerfect h.swap hc hne hb hβu ht htne
    coreFields (core_field_markings eK eU)
    (by norm_num [coreFields,GaloisField.card 2 3 (by decide)]) hD
  have he := reduced_enlargedEndpoint_eq_starred_of_linear h.swap 1 eK
  have hs : starredParabolic ![U,K] S 1 = starredParabolic ![K,U] S 0 := rfl
  exact (congrArg (fun P : Subgroup G => Group.IsPerfect P) (he.trans hs)).mp hp

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The actual full original H is perfect. -/
theorem first_perfect : Group.IsPerfect H := by
  obtain ⟨hF,hS,_,_,_⟩ := source_hypothesis hG T hempty hM hu hmany hcard e H hH eR
  have hq : IsRankOneModel (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
      GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
  have hnot := source_normal_amalgam_not_normalizes hG T hempty hM hu hmany hcard e H hH
    (pResidual 2 H) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)) rfl hq
  obtain ⟨eU⟩ := (source_residual_actor_movement hG T hempty hM hu hmany hcard e
    (secondSylow T M Mc H) hS le_sup_left hnot).2
  have hp := eight_pair_first_perfect hF (residualQuotientEquiv H eR) eU
  have he := (source_starredParabolics hG T hempty hM hu hmany hcard e H hH eR).1
  exact (congrArg (fun P : Subgroup G => Group.IsPerfect P) he).mp hp

/-- The original full H equals its two-residual. -/
theorem first_twoResidual_eq_top : pResidual 2 H = ⊤ := by
  let := first_perfect hG T hempty hM hu hmany hcard e H hH eR
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) := (isPGroup_quotient_pResidual 2).isNilpotent
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ (pResidual 2 H))

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourcePerfect
