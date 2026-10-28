module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableTwoFiftySixModel
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalF11
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BaumannBlocks
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockCore

/-!
# Genuine F.1.1 for the surviving original nonsolvable outside pair

The original earlier module clause constructs the residual Context and its
whole marked S5 action. Original5.2.3 excludes the noncommuting branch and
every core of order at most256. Thompson movement holds on both sides. A
Sylow omega-center of order two forces a genuine alternating block with
core sixteen, so the remaining omega-center has order four. Its actual
fixed lines then construct F.1.1 for the original two components and the
full original Sylow T.

No normalized Borel, reduced catalogue, critical pair or native model is
assumed. The genuine earlier module and5.2.3 source duties stay explicit.
Source: Aschbacher--Smith 13.2.8(1), printed p.880, and C.1.24(a).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section02.A5Outside.OriginalCentralization
open Section03.SourceCompletion TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Every surviving original nonsolvable outside pair supplies literal
F.1.1 on the same components and full Sylow, together with its actual
residual Context, whole action kernel and commuting natural modules. -/
theorem original_nonsolvable_f11_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ (W W₁ W₂ W₃ : Subgroup G)
      (e : Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (q : H →* Equiv.Perm (Fin 5)),
      Function.Surjective q ∧ q.ker = pCore 2 H ∧
      (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
        h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
          e.flag.module.map (Multiplicative.ofAdd
            (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
      V ≤ centralizer (W : Set G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      ChapterF.Source.HypothesisF11 ![L,(pResidual 2 H).map H.subtype] (T : Subgroup G) := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_action_from_modules d hmany hmodules hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hVW : V ≤ centralizer (W : Set G) := by
    by_contra hm
    have hp := (original_nonsolvable_noncommuting_parameter_from_source d hmany
      hH hZ hs e q hq hk hr he hm).2
    exact hno (main_model_of_source523_omega_movement d h523 hH hZ (by omega))
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
  have hbound := (original_pair_omega_bounds d e hH hjoin hJd hJe).1
  have hdiv : 2 ∣ Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := by
    simpa only [d.flag.one_card] using
      (card_dvd_of_le (le_sup_left.trans (omega_decomposition_of_thompson_moves d hJd).ge) :
        Nat.card V₁ ∣ Nat.card (omegaOneCenterAmbient (T : Subgroup G)))
  have hpos : 0 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := Nat.card_pos
  have hfour : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
    by_contra hn
    have hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by omega
    have hcards := original_commuting_pair_core_cards_ge_fiveTwelve d e hjoin hH
      (localActor_surjective_of_omega_movement d hH hZ) q hq hk he hVW
    rcases original_pair_block_of_omega_card_two d e hjoin hH hJd hJe hz with hb | hb
    · have hc := d.block_local_core_card_of_omega_card_two hb hz
      omega
    · have hc := e.block_local_core_card_of_omega_card_two hb hz
      rw [hjoin] at hc
      omega
  exact ⟨W,W₁,W₂,W₃,e,q,hq,hk,he,hVW,hfour,
    original_pair_hypothesisF11 d e hjoin hH hJd hJe hfour⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
