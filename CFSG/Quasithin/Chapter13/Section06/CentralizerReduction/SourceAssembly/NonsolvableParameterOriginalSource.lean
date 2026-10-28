module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableNoncommutingOriginalSource
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CommutingExclusion

/-!
# The genuine original nonsolvable generation parameter

The earlier original module clause supplies the residual Context and the
whole S5 action on H. Thompson movement holds for both chosen modules.
The unbounded original commuting-pair exclusion forces them not to commute.
The actual crossed action then constructs an elementary subgroup of O²(H)
whose image in H/O₂(H) has order four, proving n(H)=2.

The conclusion is obtained before applying5.2.3. No core-order bound,
normalized Borel, native-model input, universal Context producer or final
classification exclusion is assumed.
Source: Aschbacher--Smith 13.2.8(1), p.880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section02.A5Outside.OriginalCentralization
open Section03.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The original nonsolvable mover has an actual elementary lift in its
own residual and generation parameter two, without any core bound. -/
theorem original_nonsolvable_parameter_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_action_from_modules d hmany hmodules hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hB := OriginalCentralization.baumann_normalizer_of_many d hmany
  have hker : centralizer ((omegaOrbit T H).subgroupOf H : Set H) = pCore 2 H :=
    hU.symm.trans hk
  have hJd := OriginalCentralization.thompson_moves_of_omega_movement d hH hZ
  have hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
    intro hj
    have hC := (e.local_centralizers e.normalizes_L).1
    rw [hjoin] at hC
    have hcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ H.pCoreIn 2 :=
      (le_inf ((show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
        sSup_le fun _ hA => hA.1).trans hH.1.1.2) hj).trans hC.le
    apply thompson_moves_omegaOrbit d.hypothesis.qtke T hH hB hZ
    intro j hj u hu
    obtain ⟨a,ha,heq⟩ := hcore hj
    have huH : u ∈ H := (conjugateSpanBy_le
      (fun z hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      H.le_normalizer) hu
    have hc : a ∈ centralizer ((omegaOrbit T H).subgroupOf H : Set H) := hker.symm ▸ ha
    rw [←heq]
    exact congrArg H.subtype (hc ⟨u,huH⟩ hu)
  have hm : ¬ V ≤ centralizer (W : Set G) :=
    original_commuting_pair_impossible d e hjoin hH hJd hJe q hq hk he
  exact original_nonsolvable_noncommuting_parameter_from_source
    d hmany hH hZ hs e q hq hk hr he hm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
