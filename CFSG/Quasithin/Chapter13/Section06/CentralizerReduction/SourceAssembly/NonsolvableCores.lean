module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCores
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableCrossModule

/-!
# Excluding the smallest original nonsolvable core

Construct the original Context on the embedded residual and retain its
whole-omega kernel and marked S₅ action. If O₂(H) has order at most sixteen,
the explicit natural-kernel section supplies a residual elementary lift,
so n(H)=2. The literal earlier 5.2.3 consumer then gives the catalogue model.

In a remaining catalogue counterexample, the core has order greater than
sixteen. Both original local cores have the same order and are incomparable.
Commuting natural modules force a nonabelian core. In particular an outside
core of order thirty-two forces the original V to have outer image four
in the same marked S₅ action. This V is still not a residual four-group lift.
The universal application constructs both Contexts after every guarded
S,I rechoice and transports the multiple-overgroup hypothesis.

The larger-core parameter obstruction, full 13.2.7 and 13.6.7 assembly,
and the nonsingular centralizer bound remain unfinished. The earlier
Context, 13.3.2 and 5.2.3 hypotheses retain their existing source producers.
Source: Aschbacher--Smith 13.2.8(1), p.880, and 5.2.3.
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

/-- In the original branch, a two-core of order at most sixteen supplies an
actual elementary residual lift and forces parameter two. -/
theorem original_nonsolvable_small_core_parameter
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (hsmall : Nat.card (pCore 2 H) ≤ 16) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hWQ : W ≤ H.pCoreIn 2 := e.chosen.le_componentCore.trans
    (pCoreIn_mono_of_normalizes (map_subtype_le _)
      (le_normalizer_embedded_pResidual 2 H))
  obtain ⟨A,hA,hAR,hcard⟩ := residual_lift_of_core_le_sixteen e q hq hk
    he hWQ hsmall
  let := hA
  obtain ⟨_,⟨a⟩⟩ := OriginalCentralization.nonsolvable_residual_faithful_A5 d
    (normalizes_faithful_of_source1332 d h1332) hH hZ hs
  exact ⟨⟨A,hA,hAR,hcard⟩,
    ChapterE.ValuesEvenClassical.ResidualFive.parameter_two_of_residual_A5_lift
      (T.subtype hH.1.1.2) a A hAR hcard⟩

/-- The same source group satisfies the catalogue conclusion in this small-core
branch; its numerical generation premise has been discharged by the lift. -/
theorem original_nonsolvable_small_core_model
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (hsmall : Nat.card (pCore 2 H) ≤ 16) : ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_small_core_parameter d hc hmany h1332 hcontexts
    hH hZ hs hsmall).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- The remaining original branch has a larger core. The two local cores have
the same order but are incomparable; commuting original modules force a
nonabelian core, ruling out the abelian-kernel local diagnostic in that case. -/
theorem original_nonsolvable_core_constraints
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    16 < Nat.card (pCore 2 H) ∧
      Nat.card (H.pCoreIn 2) = Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ H.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ H.pCoreIn 2 ∧
      ∃ (W W₁ W₂ W₃ : Subgroup G)
        (e : Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
        (q : H →* Equiv.Perm (Fin 5)),
        W ≤ omegaOrbit T H ∧ Function.Surjective q ∧ q.ker = pCore 2 H ∧
          q.ker = centralizer ((omegaOrbit T H).subgroupOf H : Set H) ∧
          (pResidual 2 H).map q = alternatingGroup (Fin 5) ∧
          (∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
            h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
              e.flag.module.map (Multiplicative.ofAdd
                (BinaryPermutation.coreRepresentation (Fin 5) (q h) w))) ∧
          (V ≤ centralizer (W : Set G) → ¬ IsMulCommutative (pCore 2 H)) ∧
          (Nat.card (pCore 2 H) ≤ 32 →
            Nat.card ((V.subgroupOf H).map q) = 4 ∧
              ¬ (V.subgroupOf H).map q ≤ alternatingGroup (Fin 5)) := by
  have hlarge : 16 < Nat.card (pCore 2 H) := by
    by_contra! hh
    exact hno (original_nonsolvable_small_core_model d hc hmany h1332 hcontexts
      h523 hH hZ hs hh)
  obtain ⟨W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hd := OriginalCentralization.localActor_surjective_of_omega_movement d hH hZ
  have hcard := original_pair_core_cards d hH.1.1.2 hd q hq hk
  obtain ⟨hnot₁,hnot₂⟩ := original_pair_cores_incomparable d hH hd q hq hk
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hnonab := original_pair_commuting_core_nonabelian d e hjoin hH hd q hq hk
  refine ⟨hlarge,hcard,hnot₁,hnot₂,W,W₁,W₂,W₃,e,q,hW,hq,hk,hU,hr,he,hnonab,?_⟩
  intro hsmall
  have hab := core_commutative_of_card_le_thirtyTwo e hjoin hsmall
  have hm : ¬ V ≤ centralizer (W : Set G) := fun hv => hnonab hv hab
  have hWH : W ≤ H := e.chosen.le_sylow.trans hH.1.1.2
  have hCW := (e.local_centralizers e.normalizes_L).1
  rw [hjoin] at hCW
  have hkW : q.ker = centralizer (W.subgroupOf H : Set H) := by
    rw [hk]
    apply map_injective H.subtype_injective
    change H.pCoreIn 2 = _
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWH]
    exact hCW.symm
  exact d.cross_action_outer_four e (d.chosen.le_sylow.trans hH.1.1.2) hWH q hkW he hm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every guarded original rechoice excludes the small-core branch by the
actual lift, and retains the two-component obstruction in the surviving branch. -/
theorem universal_original_nonsolvable_core_constraints
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
    16 < Nat.card (pCore 2 H) ∧
      Nat.card (H.pCoreIn 2) = Nat.card ((I ⊔ (S : Subgroup G)).pCoreIn 2) ∧
      ¬ H.pCoreIn 2 ≤ (I ⊔ (S : Subgroup G)).pCoreIn 2 ∧
      ¬ (I ⊔ (S : Subgroup G)).pCoreIn 2 ≤ H.pCoreIn 2 ∧
      ∃ (V V₁ V₂ V₃ : Subgroup G) (_ : Context S I V V₁ V₂ V₃)
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
          (V ≤ centralizer (W : Set G) → ¬ IsMulCommutative (pCore 2 H)) ∧
          (Nat.card (pCore 2 H) ≤ 32 →
            Nat.card ((V.subgroupOf H).map q) = 4 ∧
              ¬ (V.subgroupOf H).map q ≤ alternatingGroup (Fin 5)) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  obtain ⟨hlarge,hcard,hnot₁,hnot₂,hrest⟩ := original_nonsolvable_core_constraints
    d hc hno hmanyS h1332 hcontexts h523 hH hZ hs
  exact ⟨hlarge,hcard,hnot₁,hnot₂,V,V₁,V₂,V₃,d,hrest⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
