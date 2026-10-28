module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableNoncommuting
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CommutingCoreOffenders

/-!
# Elementary odd actors in the remaining original commuting pair

The completed noncommuting exclusion leaves commuting natural modules.
Their cores cannot have Thompson subgroups that both centralize the opposite
module: heredity would give a common nontrivial characteristic subgroup and
violate the original maximal-local normalizer bound. The marked offender
calculation therefore supplies a maximum elementary subgroup of one core
whose action on the opposite natural module contains an odd permutation.

This is applied after every original guarded Sylow/component rechoice,
retaining both Contexts, the same residual, the full omega-centralizer kernel
and one S₅ marking. It excludes the even cross-action case. The odd elementary
actor is not asserted to lie in O²(H), and is not the residual four-group lift
needed to finish n(H)>1. That remaining construction, the earlier source
discharge, full 13.2.7/13.6.7 assembly and nonsingular hCv stay with this owner.
Source: Aschbacher--Smith 13.2.4(1),13.2.8(1), pp.879--880; B.2.3, B.3.2(4).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every remaining original commuting pair has an elementary odd cross-actor
in one of its actual cores. Both marked actions and all rechoice guards remain. -/
theorem universal_original_nonsolvable_commuting_core_offender
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ¬ IsMulCommutative (pCore 2 H) ∧
    ∃ (V V₁ V₂ V₃ : Subgroup G) (d : Context S I V V₁ V₂ V₃)
      (W W₁ W₂ W₃ : Subgroup G)
      (e : Context S ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (q : H →* Equiv.Perm (Fin 5)),
      W ≤ omegaOrbit S H ∧ Function.Surjective q ∧ q.ker = pCore 2 H ∧
        q.ker = centralizer ((omegaOrbit S H).subgroupOf H : Set H) ∧
        (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
        (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
          h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
            e.flag.module.map (Multiplicative.ofAdd
              (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
        V ≤ centralizer (W : Set G) ∧
        ((∃ A ∈ elementaryAbelianMaxSubgroups (H.pCoreIn 2),
          ¬ (A.subgroupOf (I ⊔ (S : Subgroup G))).map d.localActor ≤
            alternatingGroup (Fin 5)) ∨
        (∃ A ∈ elementaryAbelianMaxSubgroups ((I ⊔ (S : Subgroup G)).pCoreIn 2),
          ¬ (A.subgroupOf H).map q ≤ alternatingGroup (Fin 5))) := by
  obtain ⟨hab,V,V₁,V₂,V₃,d,W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he,hVW⟩ :=
    universal_original_nonsolvable_commuting_pair T hmany hc hno h1332 hcontexts h523
      S I standing H hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (S : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (S.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((S : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  exact ⟨hab,V,V₁,V₂,V₃,d,W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he,hVW,
    original_commuting_pair_core_offender d e hjoin hH q hk he hVW⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
