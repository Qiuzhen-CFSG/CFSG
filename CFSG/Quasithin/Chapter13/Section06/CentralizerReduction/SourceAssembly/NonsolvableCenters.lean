module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCenters
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableAction

/-!
# Center bounds in the original nonsolvable outside branch

Construct the second original Context on the same embedded O²(H). Its
omega-centralizer kernel and the independent Baumann bound make J(T) move
that Context's natural module. Comparing this module with the original one
bounds the Sylow and Thompson omega-centers, the original fixed summands,
and the whole original H-orbit, after every source-guarded S,I rechoice.

The multiple-overgroup guard is transported to the chosen Sylow. All
residuals and centralizers are the literal original subgroups. These bounds
do not prove n(H)>1 or assert an elementary lift. That ambient exclusion,
full outside-centralization and 13.6.7 remain with this assembly owner;
the earlier Context and 13.3.2 inputs retain their original producers.
Source: Aschbacher--Smith 13.2.4(2b),13.2.8(1), printed pp.879--880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The bounds apply to the actual original nonsolvable outside group. -/
theorem original_nonsolvable_center_bounds
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
    (hs : ¬ Group.IsSolvable H) :
    Nat.card (omegaOneCenterAmbient (T : Subgroup G)) ≤ 4 ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) ≤ 2 ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) : Subgroup G) ≤ 2 ∧
      Nat.card (ChapterB.thompsonAlpha (T : Subgroup G)) ≤ 16 ∧
      Nat.card (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G) : Subgroup G) ≤ 4 ∧
      Nat.card (ChapterB.thompsonAlpha (T : Subgroup G) ⊓
        centralizer ((pResidual 2 H).map H.subtype : Set G) : Subgroup G) ≤ 4 ∧
      (Nat.card (omegaOrbit T H) = 16 ∨ Nat.card (omegaOrbit T H) = 32) := by
  obtain ⟨W,W₁,W₂,W₃,⟨e⟩⟩ := original_nonsolvable_residual_context d hc h1332 hcontexts hH hZ hs
  have hn := normalizes_faithful_of_source1332 d h1332
  have hB := OriginalCentralization.baumann_normalizer_of_many d hmany
  have hker := OriginalCentralization.nonsolvable_omega_centralizer_eq_twoCore d hn hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
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
    obtain ⟨a,ha,he⟩ := hcore hj
    have huH : u ∈ H := (conjugateSpanBy_le
      (fun z hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      H.le_normalizer) hu
    have hc : a ∈ centralizer ((omegaOrbit T H).subgroupOf H : Set H) := hker.symm ▸ ha
    rw [←he]
    exact congrArg H.subtype (hc ⟨u,huH⟩ hu)
  obtain ⟨hz,hl,hk⟩ := OriginalCentralization.original_pair_omega_bounds d e hH hjoin hJd hJe
  obtain ⟨ha,haL,haK⟩ := OriginalCentralization.original_pair_alpha_bounds d e hH hjoin hJd hJe
  have hHfix : Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (H : Set G) : Subgroup G) ≤ 2 :=
    (card_le_of_le (inf_le_inf_left _ (centralizer_le (map_subtype_le _)))).trans hk
  exact ⟨hz,hl,hHfix,ha,haL,haK,
    (OriginalCentralization.original_pair_omegaOrbit_bounds d e hH hjoin hJd hJe).2.2⟩

/-- The bounds concern the same original residual and full omega orbit
after every source-guarded rechoice. -/
theorem universal_original_nonsolvable_center_bounds
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    Nat.card (omegaOneCenterAmbient (S : Subgroup G)) ≤ 4 ∧
      Nat.card (omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) : Subgroup G) ≤ 2 ∧
      Nat.card (omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (H : Set G) : Subgroup G) ≤ 2 ∧
      Nat.card (ChapterB.thompsonAlpha (S : Subgroup G)) ≤ 16 ∧
      Nat.card (ChapterB.thompsonAlpha (S : Subgroup G) ⊓ centralizer (I : Set G) : Subgroup G) ≤ 4 ∧
      Nat.card (ChapterB.thompsonAlpha (S : Subgroup G) ⊓
        centralizer ((pResidual 2 H).map H.subtype : Set G) : Subgroup G) ≤ 4 ∧
      (Nat.card (omegaOrbit S H) = 16 ∨ Nat.card (omegaOrbit S H) = 32) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact original_nonsolvable_center_bounds d hc hmanyS h1332 hcontexts hH hZ hs

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
