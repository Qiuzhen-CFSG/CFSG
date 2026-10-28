module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableDerived
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreOneTwentyEight

/-!
# Excluding original nonsolvable outside cores of order at most one hundred and twenty-eight

The Context of the literal embedded O²(H) puts its natural sixteen centrally
in O₂(H). Its actual quintic actor gives a fixed-free central factor and a
complement of order at most eight, so the core has cyclic derived subgroup.
The established original cross-module argument constructs an elementary
subgroup in the same O²(H), with image
four under H → H/O₂(H), and gives n(H)=2.

The actual 5.2.3 consumer excludes this range. Thus a surviving original
nonsolvable outside core has order at least 256. Larger noncyclic-derived
cores and the original earlier-source inputs remain open.

Source application: Aschbacher--Smith 13.2.8(1), printed p.880, and 5.2.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

theorem original_nonsolvable_core_le_oneTwentyEight_parameter
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
    (hs : ¬ Group.IsSolvable H) (hsmall : Nat.card (pCore 2 H) ≤ 128) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,⟨e⟩⟩ :=
    original_nonsolvable_residual_context d hc h1332 hcontexts hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hcyc := e.core_cyclic_derived_of_card_le_oneTwentyEight (hjoin.symm ▸ hsmall)
  rw [hjoin] at hcyc
  exact original_nonsolvable_cyclic_derived_core_parameter d hc hmany h1332 hcontexts
    hH hZ hs hcyc

theorem original_nonsolvable_core_le_oneTwentyEight_model
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
    (hs : ¬ Group.IsSolvable H) (hsmall : Nat.card (pCore 2 H) ≤ 128) :
    ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_core_le_oneTwentyEight_parameter d hc hmany h1332 hcontexts
    hH hZ hs hsmall).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

theorem universal_original_nonsolvable_core_ge_twoFiftySix
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
    (hs : ¬ Group.IsSolvable H) : 256 ≤ Nat.card (pCore 2 H) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  have hlarge : 128 < Nat.card (pCore 2 H) := by
    by_contra! hsmall
    exact hno (original_nonsolvable_core_le_oneTwentyEight_model
      d hc hmanyS h1332 hcontexts h523 hH hZ hs hsmall)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hnlarge : 8 ≤ n := by
    by_contra! hnsmall
    have hb := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 7)
    rw [← hn] at hb
    norm_num at hb
    omega
  calc
    256 = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hnlarge
    _ = Nat.card (pCore 2 H) := hn.symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
