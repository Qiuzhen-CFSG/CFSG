module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.Splitting
public import Theory.GroupTheory.PResidual.CenterlessSylow
public import Theory.GroupTheory.CharacteristicTwoCenterJoin
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The center-free original outside group

The residual Sylow centralizer in 13.2.11(1) vanishes when Z(H)=1.
The actual solvable E.2.3 decomposition then becomes
Ω₁Z(J(T))=C_{U_H}(J(T)), and the original omega orbit is [U_H,H].
Every equality is transported through the original inclusion H→G.

For the opening of 13.2.12, the literal source subgroup is
L₁=O²(N_L(T∩L)). Its join with H has nontrivial two-core unless H is
center-free: the first omega of Z(H) would otherwise be a nontrivial
central two-subgroup of that join. The earlier [Z,L₁]=1 assertion from
13.2.4(2b) remains explicit, as do the Baumann bound and solvability.

Source: Aschbacher–Smith 13.2.11–12, printed pp.881–882.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- Original 13.2.11(1) for the actual outside residual and Sylow subgroup. -/
theorem source_residual_sylow_centralizer_eq_bot
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hz : center H = ⊥) :
    (T : Subgroup G) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) = ⊥ := by
  have hh := congrArg (map H.subtype)
    (sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot (T.subtype hTH) hz)
  rw [← map_inf_centralizer_of_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH, Subgroup.map_bot] at hh
  exact hh

/-- The original E.2.3 alpha decomposition has no residual-fixed summand. -/
theorem source_alpha_eq_omegaOrbit_fixed
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ChapterB.thompsonAlpha (T : Subgroup G) =
      omegaOrbit T H ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  obtain ⟨hsq, _, hp, hU, hj⟩ := e23_hypotheses
    d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let := hs
  have ha := (ChapterE.ThompsonAction.source_solvable_baumann_sylow_and_alpha
    S hp U hU hj (hsq.stronglyQuasithin 3 (by decide) (by decide)) inferInstance).2
  have hET : ChapterB.thompsonAlpha (S : Subgroup H) ≤ (S : Subgroup H) := by
    intro x hx
    exact (show elementaryAbelianMaxJ (S : Subgroup H) ≤ (S : Subgroup H) from
      sSup_le fun _ hA => hA.1) ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hfix : ChapterB.thompsonAlpha (S : Subgroup H) ⊓
      centralizer (pResidual 2 H : Set H) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_right _ hET).trans_eq
      (sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot S hz)
  rw [hfix, bot_sup_eq] at ha
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hH.1.1.2
  have hEmap : (ChapterB.thompsonAlpha (S : Subgroup H)).map H.subtype =
      ChapterB.thompsonAlpha (T : Subgroup G) := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H))).map
      H.subtype = omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G))
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective, hJmap]
  have hUH : omegaOrbit T H ≤ H := conjugateSpanBy_le
    (fun _ hx => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) H.le_normalizer
  have hh := congrArg (map H.subtype) ha
  rw [hEmap, ← map_inf_centralizer_of_injective H.subtype H.subtype_injective,
    hJmap, map_subgroupOf_eq_of_le hUH] at hh
  exact hh

/-- The original center-free omega orbit is its entire moved subgroup. -/
theorem source_centerfree_omegaOrbit_eq_commutator
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    omegaOrbit T H = ⁅omegaOrbit T H, H⁆ := by
  have hfixed : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (H : Set G) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf
      (fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
      (centralizer_le (map_subtype_le (pResidual 2 H)))).trans_eq
        (source_residual_sylow_centralizer_eq_bot T H hH.1.1.2 hz)
  have hh := (source_omegaOrbit_splitting d hH hB hZ hs).1
  rw [hfixed, sup_bot_eq] at hh
  exact hh.symm

/-- The original L₁=O²(N_L(T∩L)), with both subgroup inclusions retained. -/
noncomputable abbrev borelResidual (T : Sylow 2 G) (L : Subgroup G) : Subgroup G :=
  let N := normalizer ((T : Subgroup G).subgroupOf L : Set L)
  ((pResidual 2 N).map N.subtype).map L.subtype

/-- The opening of 13.2.12, retaining the literal earlier [Z,L₁]=1 premise. -/
theorem source_center_eq_bot_of_borel_join_core_eq_bot
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) : center H = ⊥ := by
  exact Theory.GroupTheory.center_eq_bot_of_join_core_eq_bot T H (borelResidual T L)
    hH.1.1.2 (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) hH.1.1)) hL₁Z hcore

/-- The contrary-core source branch supplies all center-free reductions
without a separate center or residual-centralizer hypothesis. -/
theorem source_borel_join_coreFree_reduction
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    center H = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) = ⊥ ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        omegaOrbit T H ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      omegaOrbit T H = ⁅omegaOrbit T H, H⁆ := by
  have hz := source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore
  exact ⟨hz, source_residual_sylow_centralizer_eq_bot T H hH.1.1.2 hz,
    source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz,
    source_centerfree_omegaOrbit_eq_commutator d hH hB hZ hs hz⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
