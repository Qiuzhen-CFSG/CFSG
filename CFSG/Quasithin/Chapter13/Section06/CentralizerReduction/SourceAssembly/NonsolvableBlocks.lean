module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.BlockCore
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BaumannBlocks
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableCenters
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableCores

/-!
# Closing the prime-omega-center case in the original nonsolvable pair

When Ω₁Z(T) has order two, both original Sylow component centralizers
vanish. The first Baumann-pair member centralizes J(T), so the genuine
Thompson commutator identities exclude its normalization by either local
group. The same universal pair therefore forces an alternating-five block.
C.1.13(c) now gives local core order sixteen, and the two marked S₅ actions
transfer that order to O₂(H). Natural-kernel splitting supplies an elementary
A ≤ O²(H) with image four under the literal H → H/O₂(H), giving n(H)=2.

The actual 5.2.3 consumer excludes this branch. Every surviving original
nonsolvable pair consequently has |Ω₁Z(T)|=4. Its block alternatives retain
their full subnormal placement, module maps and Thompson commutators; the
same pair's opposite-normalizer branch is kept. The universal application
preserves SourceHypothesis after every rechoice and transports the
multiple-overgroup guard. The order-four-center pair, unrestricted
hparameter, earlier-source discharge, full 13.2.7/13.6.7 and literal hCv
remain open. Source: Aschbacher--Smith 13.2.8(1), p.880; C.1.13(c),
pp.124--125; C.1.18--24, pp.126--131; and the actual 5.2.3 consumer.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization ChapterB ChapterC
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A prime Sylow omega-center forces an original block and then an actual residual lift. -/
theorem original_nonsolvable_omega_two_parameter
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
    (hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,hU,_,_⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
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
    obtain ⟨a,ha,he⟩ := hcore hj
    have huH : u ∈ H := (conjugateSpanBy_le
      (fun z hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      H.le_normalizer) hu
    have hc : a ∈ centralizer ((omegaOrbit T H).subgroupOf H : Set H) := hker.symm ▸ ha
    rw [←he]
    exact congrArg H.subtype (hc ⟨u,huH⟩ hu)
  have hb := original_pair_block_of_omega_card_two d e hjoin hH hJd hJe hz
  have hcard : Nat.card (pCore 2 H) = 16 := by
    rcases hb with hb | hb
    · have he := original_pair_core_cards d hH.1.1.2
        (localActor_surjective_of_omega_movement d hH hZ) q hq hk
      simpa only [pCoreIn,card_map_of_injective H.subtype_injective,
        card_map_of_injective (L ⊔ (T : Subgroup G)).subtype_injective,
        d.block_local_core_card_of_omega_card_two hb hz] using he
    · have he := e.block_local_core_card_of_omega_card_two hb hz
      rwa [hjoin] at he
  exact original_nonsolvable_small_core_parameter d hc hmany h1332 hcontexts
    hH hZ hs (by omega)

/-- After 5.2.3, every surviving original nonsolvable pair has omega-center order four. -/
theorem original_nonsolvable_baumann_block_alternatives
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
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
    ∃ (W W₁ W₂ W₃ : Subgroup G)
      (_ : Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G))),
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      D.Universal.{u,u} ∧
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      ((IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧
          IsAlternatingBlock L 5 ∧ (blockU L).map L.subtype = V ∧
          L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) ∨
        (IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) ∧
          IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∧
          (blockU ((pResidual 2 H).map H.subtype)).map
            ((pResidual 2 H).map H.subtype).subtype = W ∧
          (pResidual 2 H).map H.subtype =
            ⁅(pResidual 2 H).map H.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆) ∨
        (D.first ≠ D.second ∧
          ((L ⊔ (T : Subgroup G) ≤ normalizer
              (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
          (L ⊔ (T : Subgroup G) ≤ normalizer
              (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G))))) := by
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
  have hbound := (original_nonsolvable_center_bounds d hc hmany h1332 hcontexts hH hZ hs).1
  have hdiv : 2 ∣ Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := by
    simpa only [d.flag.one_card] using
      (card_dvd_of_le (le_sup_left.trans (omega_decomposition_of_thompson_moves d hJd).ge) :
        Nat.card V₁ ∣ Nat.card (omegaOneCenterAmbient (T : Subgroup G)))
  have hpos : 0 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)) := Nat.card_pos
  have hfour :
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
    by_contra hn
    have hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by omega
    have hp := (original_nonsolvable_omega_two_parameter d hc hmany h1332 hcontexts hH hZ hs hz).2
    exact hno (main_model_of_source523_omega_movement d h523 hH hZ (by omega))
  obtain ⟨D,hD,hn₁,hn₂,hcases⟩ :=
    original_pair_baumann_block_alternatives d e hjoin hH hJd hJe
  exact ⟨W,W₁,W₂,W₃,e,D,hfour,hD,hn₁,hn₂,hcases⟩

/-- Apply the pair reduction after every original guarded rechoice. -/
theorem universal_original_nonsolvable_baumann_block_alternatives
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
    ∃ (V V₁ V₂ V₃ : Subgroup G) (_ : Context S I V V₁ V₂ V₃)
      (W W₁ W₂ W₃ : Subgroup G)
      (_ : Context S ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (D : GlaubermanNiles.CharacteristicPair (baumann (S : Subgroup G))),
      Nat.card (omegaOneCenterAmbient (S : Subgroup G)) = 4 ∧
      D.Universal.{u,u} ∧
      ¬ (I ⊔ (S : Subgroup G) ≤ normalizer
        (D.first.map (baumann (S : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (S : Subgroup G)).subtype : Set G)) ∧
      ¬ (I ⊔ (S : Subgroup G) ≤ normalizer
        (D.second.map (baumann (S : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (S : Subgroup G)).subtype : Set G)) ∧
      ((IsBlock (I.subgroupOf (I ⊔ (S : Subgroup G))) ∧
          IsAlternatingBlock I 5 ∧ (blockU I).map I.subtype = V ∧
          I = ⁅I,elementaryAbelianMaxJ (S : Subgroup G)⁆) ∨
        (IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) ∧
          IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∧
          (blockU ((pResidual 2 H).map H.subtype)).map
            ((pResidual 2 H).map H.subtype).subtype = W ∧
          (pResidual 2 H).map H.subtype =
            ⁅(pResidual 2 H).map H.subtype,elementaryAbelianMaxJ (S : Subgroup G)⁆) ∨
        (D.first ≠ D.second ∧
          ((I ⊔ (S : Subgroup G) ≤ normalizer
              (D.first.map (baumann (S : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.second.map (baumann (S : Subgroup G)).subtype : Set G)) ∨
          (I ⊔ (S : Subgroup G) ≤ normalizer
              (D.second.map (baumann (S : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.first.map (baumann (S : Subgroup G)).subtype : Set G))))) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  obtain ⟨W,W₁,W₂,W₃,e,D,hrest⟩ := original_nonsolvable_baumann_block_alternatives
    d hc hno hmanyS h1332 hcontexts h523 hH hZ hs
  exact ⟨V,V₁,V₂,V₃,d,W,W₁,W₂,W₃,e,D,hrest⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
