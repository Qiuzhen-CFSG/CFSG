module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.Paired
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FixedPoints
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvablePair
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup

/-!
# The original alpha plane and Sylow centralizers

The center-free paired action has no residual-fixed summand, so its two
natural factors identify U_H with a four-dimensional binary space. The
actual Thompson image is Sylow in the product of the two S₃ factors and
has fixed codimension two. Thus E=Ω₁Z(J(T)) has order four. The already
constructed plane C_V(J(T)) lies in E and has at least four elements,
forcing E=C_V(J(T))≤V.

Consequently Ω₁Z(T) is the original flag line V₁ and C_T(L)=1. The alpha
bound also forces J(T) to move V, so the actual local actor is onto S₅.
The final theorem applies these facts to the literal contrary core-free
join H∨O²(N_L(T∩L)); the earlier [Z,L₁]=1, Baumann bound and solvability
remain explicit. The marked equality E=V₂ and the later block and
Goldschmidt arguments are not asserted here.

Source: Aschbacher–Smith 13.2.11(1)–(3) and the opening of 13.2.12,
printed pp.881–882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

theorem source_alpha_card_four
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    Nat.card (ChapterB.thompsonAlpha (T : Subgroup G)) = 4 := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c, hc, ht⟩ := source_solvable_paired_factors d hH hB hZ hs hz
  let D := c.toSolvableFFFactors
  obtain ⟨_, _, hp, _, hj⟩ := e23_hypotheses
    d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective
    U q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hj
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans he.ge
  have hpq := (ChapterB.minimalParabolic_reduced_image S hp q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
  have hff : IsFFModule ρ := (isFFModule_iff_quadraticRatio_le_one ρ).mpr c.ratio_one.le
  have hr := (ChapterB.offender_generation (S.mapSurjective (QuotientGroup.mk'_surjective C))
    hpq ρ hff hU.quotient_pCore_eq_bot).1
  have hUT : U ≤ (S : Subgroup H) :=
    hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)
  have hfixedR : fixedSpace ρ (pResidual 2 (H ⧸ C)) = ⊥ := by
    apply bot_unique
    intro v hv
    have hvc : (v.toMul : H) ∈ centralizer (pResidual 2 H : Set H) := by
      apply (NormalElementaryQuotient.mem_fixedSpace_image U q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) (pResidual 2 H) v).mp
      rwa [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective C)]
    have hb : (v.toMul : H) ∈ (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H) :=
      ⟨hUT v.toMul.property, hvc⟩
    rw [sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot S hz] at hb
    exact Additive.toMul.injective (Subtype.ext (mem_bot.mp hb))
  have hfixed : fixedSpace ρ (offenderSubgroup ρ) = ⊥ :=
    (D.fixed_residual_eq hf hr).symm.trans hfixedR
  let f := D.pairQuotientMap hf hr hc
  have hfi : Function.Injective f := LinearMap.ker_eq_bot.mp
    ((D.pairQuotientMap_ker hf hr hc).trans hfixed)
  let e := LinearEquiv.ofBijective f ⟨hfi, D.pairQuotientMap_surjective hf hr hc⟩
  let τ := D.pairMovedAction hc
  have he : ∀ g v, e (ρ g v) = τ ((MonoidHom.id (H ⧸ C)) g) (e v) :=
    D.pairQuotientMap_equivariant hf hr hc
  have hdim : Module.finrank (ZMod 2) (Additive U) = 4 := by
    have hh := e.finrank_eq
    simpa [Module.finrank_prod, Module.finrank_pi_fintype] using hh
  have hJq := (ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot hUT hj c hc ht).1
  let O := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  have hcod : fixedCodim ρ ((elementaryAbelianMaxJ (S : Subgroup H)).map q) = 2 := by
    rw [fixedCodim_map_equivariant ρ τ (MonoidHom.id _) e he, Subgroup.map_id, hJq]
    obtain ⟨P, hP⟩ := (S.mapSurjective (QuotientGroup.mk'_surjective C)).exists_sylow_map_eq_inf_of_normal O
    change (P : Subgroup O).map O.subtype = (S : Subgroup H).map q ⊓ O at hP
    rw [← hP]
    simpa using SL2NaturalOffenders.paired_sylowImage_fixedCodim O (D.pairActorCoordinates hc)
      τ (fun a v => D.pairMovedAction_natural hc a v.1 v.2) P
  have hdimF : Module.finrank (ZMod 2)
      (fixedSpace ρ ((elementaryAbelianMaxJ (S : Subgroup H)).map q)) = 2 := by
    have hh := fixedCodim_add_finrank ρ ((elementaryAbelianMaxJ (S : Subgroup H)).map q)
    omega
  have hcardF : Nat.card (U ⊓ centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) : Subgroup H) = 4 := by
    rw [← Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      (elementaryAbelianMaxJ (S : Subgroup H))),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdimF]
    norm_num
  have hUH : omegaOrbit T H ≤ H := conjugateSpanBy_le
    (fun _ hx => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1) H.le_normalizer
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le hH.1.1.2
  have hcmap : (U ⊓ centralizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H)).map
      H.subtype = omegaOrbit T H ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← map_inf_centralizer_of_injective H.subtype H.subtype_injective,
      hJmap, map_subgroupOf_eq_of_le hUH]
  rw [source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz, ← hcmap,
    card_map_of_injective H.subtype_injective]
  exact hcardF

theorem source_alpha_eq_local_fixed_plane
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ChapterB.thompsonAlpha (T : Subgroup G) =
      V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let F := V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let := d.elementary
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ V from inf_le_left)
  have hFE : F ≤ ChapterB.thompsonAlpha (T : Subgroup G) :=
    elementary_centralizer_maxJ_le_omegaCenter _ F
      (inf_le_left.trans d.chosen.le_sylow) inf_le_right
  exact (eq_of_le_of_card_ge hFE (by
    rw [source_alpha_card_four d hH hB hZ hs hz]
    exact d.four_le_card_thompson_fixed)).symm

theorem source_omegaCenter_le_local_module
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let := omegaOneCenterAmbient_elementaryAbelian (T : Subgroup G)
  have hZT : Z ≤ (T : Subgroup G) := fun _ hx => (mem_omegaOneCenterAmbient_iff _ _).mp hx |>.1
  have hZC : Z ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro z hz x hx
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 x
      ((sSup_le fun _ hA => hA.1 : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G)) hx)
  have hZE := elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G) Z hZT hZC
  exact hZE.trans ((source_alpha_eq_local_fixed_plane d hH hB hZ hs hz).le.trans inf_le_left)

theorem source_local_sylow_centralizer_eq_bot
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  apply Section06.CentralizerReduction.centralizer_T_eq_bot_of_omega
    (T : Subgroup G) L T.isPGroup' d.normalizes_L
  apply bot_unique
  exact (inf_le_inf_right _ (source_omegaCenter_le_local_module d hH hB hZ hs hz)).trans_eq
    d.flag.module.fixed_eq_bot

theorem source_centerfree_localActor_surjective
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    Function.Surjective d.localActor := by
  apply d.localActor_surjective_of_thompson_moves
  intro hj
  have hVE : V ≤ ChapterB.thompsonAlpha (T : Subgroup G) := by
    rw [source_alpha_eq_local_fixed_plane d hH hB hZ hs hz]
    exact le_inf le_rfl (le_centralizer_iff.mp hj)
  have hcard := Nat.card_le_card_of_injective (inclusion (d.third_le.trans hVE))
    (inclusion_injective (d.third_le.trans hVE))
  rw [d.third_card, source_alpha_card_four d hH hB hZ hs hz] at hcard
  omega

theorem source_omegaCenter_eq_flag_line
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    omegaOneCenterAmbient (T : Subgroup G) = V₁ := by
  have h1V : V₁ ≤ V := d.flag.one_le_two.trans d.flag.two_le_V
  have h1C : V₁ ≤ centralizer ((T : Subgroup G) : Set G) := le_centralizer_iff.mp
    (d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card))
  apply le_antisymm
  · rw [← d.flag.module_fixed_eq_line]
    refine le_inf (source_omegaCenter_le_local_module d hH hB hZ hs hz) ?_
    intro x hx
    exact (mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.2
  · intro x hx
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨d.chosen.le_sylow (h1V hx), ?_, h1C hx⟩
    have he : (⟨x, hx⟩ : V₁) ^ 2 = 1 := by
      rw [← d.flag.one_card]
      exact pow_card_eq_one'
    exact congrArg Subtype.val he

theorem source_coreFree_borel_join_plane_and_centralizers
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hL₁Z : borelResidual T L ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    Nat.card (ChapterB.thompsonAlpha (T : Subgroup G)) = 4 ∧
      ChapterB.thompsonAlpha (T : Subgroup G) =
        V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      omegaOneCenterAmbient (T : Subgroup G) = V₁ ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G) = ⊥ ∧
      Function.Surjective d.localActor := by
  have hz := source_center_eq_bot_of_borel_join_core_eq_bot d hH hL₁Z hcore
  exact ⟨source_alpha_card_four d hH hB hZ hs hz,
    source_alpha_eq_local_fixed_plane d hH hB hZ hs hz,
    source_omegaCenter_eq_flag_line d hH hB hZ hs hz,
    source_local_sylow_centralizer_eq_bot d hH hB hZ hs hz,
    source_residual_sylow_centralizer_eq_bot T H hH.1.1.2 hz,
    source_centerfree_localActor_surjective d hH hB hZ hs hz⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
