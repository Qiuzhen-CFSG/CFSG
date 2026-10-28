module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOneResidual
public import Theory.GroupTheory.PrimeRankNineCubicSection
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Parabolic.CubicActor

/-!
# The rank-five residual contradiction

A rank-one node over the original point Sylow has two-residual with
intrinsic two-core quotient of order three. The moving pair supplies an
elementary nine-group which normalizes that residual and meets the plane
centralizer trivially. Their literal join has three-rank at least three,
contrary to the SQTK upper bound already proved for its containing group.
Together with the rank-ten exclusion this discharges LinearFiveExclusionAt.

The owner qt-d-10-nona5-point-constrained retains the earlier preparation
and model recognition constructing LinearFiveData from the source Context.
Source: Aschbacher--Smith, 10.2.9, printed pp.752--753.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The literal rank-one node has cubic residual modulo its own two-core. -/
theorem LinearFiveData.node_residual_quotient_card {c : Context D t v I}
    (m : LinearFiveData c) (P : Subgroup G) (hSP : pointSylow T v ⋖ P)
    (hPH : P ≤ pointJoin T v I) :
    Nat.card (((pResidual 2 P).map P.subtype) ⧸
      pCore 2 ((pResidual 2 P).map P.subtype)) = 3 := by
  let H := pointJoin T v I
  obtain ⟨S,hS⟩ := c.join_sylow
  have hp : (S : Subgroup H) ⋖ P.subgroupOf H := by
    apply (covBy_map_subtype_iff H _ _).mp
    rw [hS,map_subgroupOf_eq_of_le hPH]
    exact hSP
  have hc := BinaryLinear.FiveFlagGeometry.rankOne_residual_quotient_card_of_two_kernel
    m.joinAction m.joinAction_surjective m.joinAction_kernel_two S (P.subgroupOf H) hp
  let eP := subgroupOfEquivOfLe hPH
  let eR : pResidual 2 (P.subgroupOf H) ≃* pResidual 2 P :=
    (eP.subgroupMap (pResidual 2 (P.subgroupOf H))).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 eP.toMonoidHom eP.surjective))
  let e := eR.trans ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective)
  rw [←Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv]
  exact hc

/-- Both terminal dimensions are impossible on the original linear-five data.
The moving nine-group is independent of the residual because the latter
centralizes the original plane. Their actual join violates the SQTK bound. -/
theorem LinearFiveData.impossible {c : Context D t v I} (m : LinearFiveData c) : False := by
  obtain ⟨P,F,hP,hPC,_,_,hF,hFL,hFC,_,hn,_,hu⟩ := m.exists_rankFive_residual_configuration
  obtain ⟨E,hEF,hEe,hEc,hEd⟩ := m.exists_moving_nine F hF hFL hFC
  let R := (pResidual 2 P).map P.subtype
  have hRC : R ≤ centralizer (pointPlane t v : Set G) :=
    (map_subtype_le _).trans (hPC.trans inf_le_right)
  have hd : Disjoint R E := (hEd.mono_right hRC).symm
  have hER : E ≤ normalizer (R : Set G) := hEF.trans hn
  have hl := three_le_primeRank_of_nine_normalizing_cubic_section R E hER
    (m.node_residual_quotient_card P hP (hPC.trans inf_le_left)) hEe hEc hd
  have hb := (primeRank_mono 3 (sup_le_sup le_rfl hEF)).trans hu
  change primeRank 3 (R ⊔ E : Subgroup G) ≤ 2 at hb
  omega

/-- The complete parabolic source obligation, with no remaining actor or
centralizer callback. The preceding model recognition is discharged separately. -/
theorem linearFiveExclusion (T : Sylow 2 G) : LinearFiveExclusionAt T := by
  intro L D t v I c _ m
  exact m.impossible

end CFSG.Quasithin.Chapter10.PointControl.Constrained
