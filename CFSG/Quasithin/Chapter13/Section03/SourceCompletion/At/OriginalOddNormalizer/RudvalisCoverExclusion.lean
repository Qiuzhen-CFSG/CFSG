module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisCoverExclusion
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalIntersectionGeometry
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisThreeCentralization

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.RudvalisCoverExclusion`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers Chapter12.Section02
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
section Component
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Commuting original module intersections exclude the actual Rudvalis
central cover; no centerlessness or full ambient Sylow placement is assumed. -/
theorem unitary_original_pushingUp_rudvalis_false
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (hinter : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let g := MulAut.conj (c : G)
  let j := H.subtype.comp K.subtype
  let W0 := (W.subgroupOf H).subgroupOf K
  let E := W0.map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  let lift (A : Subgroup G) := ((A.map g.toMonoidHom).subgroupOf H).subgroupOf K
  have hfull := unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hVW
  change W = V.map g.toMonoidHom at hfull
  have hWH : W ≤ H := (hc.module_le_center_radical.trans (map_subtype_le _)).trans
    (hc.radical_le.trans hc.local_le)
  have hWK : W.subgroupOf H ≤ K := (hc.ordinary_module_placement K hK).1.trans inf_le_right
  have hAM (A : Subgroup G) (hAV : A ≤ V) : A.map g.toMonoidHom ≤ W :=
    (map_mono hAV).trans hVW
  have hAlift (A : Subgroup G) (hAV : A ≤ V) : lift A ≤ W0 :=
    subgroupOf_mono K (subgroupOf_mono H (hAM A hAV))
  have hcard (A : Subgroup G) (hAV : A ≤ V) : Nat.card (lift A) = Nat.card A := by
    have hAH := (hAM A hAV).trans hWH
    have hAK := (subgroupOf_mono H (hAM A hAV)).trans hWK
    rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv,card_map_of_injective g.injective]
  have hfW : Function.Injective (f.comp W0.subtype) := by
    have hi := (unitary_original_pushingUp_chosen_injective s hcover hJH hc K hK c hVW).1
    rw [←hfull] at hi
    exact e.injective.comp hi
  have hZcard : Nat.card (lift Z) = 2 := (hcard Z hZV).trans hZ
  have hZn : lift Z ≠ ⊥ := (lift Z).one_lt_card_iff_ne_bot.mp (by omega)
  obtain ⟨z,hz⟩ := ne_bot_iff_exists_ne_one.mp hZn
  have hzbar : f z ≠ 1 := by
    intro he
    have hh : (⟨(z : K),hAlift Z hZV z.property⟩ : W0) = 1 := by
      apply hfW
      change f (z : K) = f 1
      rwa [map_one]
    have hh' : (z : K) = 1 := congrArg (fun w : W0 => (w : K)) hh
    exact hz (Subtype.ext hh')
  obtain ⟨X,_,Q,_,_,_,hQU,_,hQout⟩ :=
    unitary_original_pushingUp_rudvalis_quaternion_three s Z B U hZV hBV hUV hTZ hTB hTU
      hZ hB hU hcover hJH hc K hK e c hVW (f z) (mem_map_of_mem f z.property) hzbar
  obtain ⟨q,hq,hqC⟩ := Set.not_subset.mp hQout
  obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) q
  change f k = q at hk
  have hkU : f k ∈ centralizer ((lift U).map f : Set Rudvalis.Model) := hk.symm ▸ hQU hq
  let i := g.symm.toMonoidHom.comp j
  have hi : Function.Injective i := g.symm.injective.comp
    (H.subtype_injective.comp K.subtype_injective)
  have hWmap : W0.map j = W := by
    rw [←map_map,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hWH]
  have hVmap : W0.map i = V := by
    have he : g.symm.toMonoidHom.comp g.toMonoidHom = MonoidHom.id G := by
      ext v
      exact g.symm_apply_apply v
    dsimp only [i]
    rw [←map_map,hWmap,hfull,map_map,he,map_id]
  have hinterK : ∀ x : K, W0 ⊓ W0.map (MulAut.conj x).toMonoidHom ≠ ⊥ →
      W0.map (MulAut.conj x).toMonoidHom ≤ centralizer (W0 : Set K) := by
    apply commuting_intersections_of_injective_map i hi W0
    rw [hVmap]
    intro x hx
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hinter x hx))
  have hker : f.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let := hK.2
  let cov : PerfectCentralCovering.Cover K Rudvalis.Model :=
    { toMonoidHom := f, surjective := e.surjective.comp (QuotientGroup.mk'_surjective _),
      isPerfect := inferInstance, ker_le_center := hker.le }
  have hsmall := Rudvalis.Multiplier.cover_kernel_card_le_two_any_universe cov
  change Nat.card f.ker ≤ 2 at hsmall
  have hUcard : Nat.card (lift U) = 8 := (hcard U hUV).trans hU
  have hNE : normalizer (E : Set Rudvalis.Model) = C :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).1
  have hCE : C ⊓ centralizer (E : Set Rudvalis.Model) = E :=
    (unitary_original_pushingUp_rudvalis_normalizer s hcover hJH hc K hK e c hVW).2.2
  have hself : centralizer (E : Set Rudvalis.Model) ≤ E := by
    intro x hx
    apply hCE.le
    refine ⟨?_,hx⟩
    rw [←hNE]
    exact Subgroup.centralizer_le_normalizer _ hx
  have hn := map_mem_normalizer_of_commuting_intersections f hker.le W0 (lift U)
    (hAlift U hUV) (by omega) hinterK hself k hkU
  have hnC : f k ∈ C := by
    rw [←hNE]
    exact hn
  rw [hk] at hnC
  exact hqC hnC

end Component

section OriginalFlag
variable (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
  (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context D.T D.L D.V)
  (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
  (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
  (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
  (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
  (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
  (B : Subgroup G) (hBV : B ≤ D.V)
  (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
  (hHfull : D.H = normalizer (D.V₁ : Set G))
  (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
  (fixed : OriginalFixedModule1332At D.T D.L)
  (five : OriginalAlternatingFiveModules1332At D.T D.L)

include s earlier hUV hZV hTZ hTU hZ hU hBV hTB hB hHfull h1332 fixed five

/-- The original odd-actor pair has only the J₄ central quotient remaining.
The original ambient geometry discharges the commuting-intersection input. -/
theorem unitary_original_oddActorResidual_janko_only
    (A : Subgroup G) (hAN : A ≤ normalizer (D.L : Set G))
    (hcomm : ⁅A,D.L⁆ ≤ D.L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (D.V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual D.L A) (normalizer (D.L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (D.L : Set G)) D.L))
      (c : sectionCentralizerIn (normalizer (D.L : Set G)) D.L),
      PushLE D.L (oddActorResidual D.L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (D.L : Set G) < H ∧
      let Y := (solvableResidual (D.L ⊓ H : Subgroup G)).map (D.L ⊓ H).subtype
      let W := fullModule D.L ((S : Subgroup (sectionCentralizerIn (normalizer (D.L : Set G)) D.L)).map
        (sectionCentralizerIn (normalizer (D.L : Set G)) D.L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (D.L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((D.L ⊔ (D.T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (D.L : Set G)) D.L)).map
          (sectionCentralizerIn (normalizer (D.L : Set G)) D.L).subtype ∧
      D.V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (D.L : Set G)).subgroupOf H ∧
        Nonempty (K ⧸ center K ≃* Janko4.Model) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact ⟨e⟩
  · exfalso
    have hcover : (D.L : Set G) ⊆ (J : Set G) * (D.L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual D.L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le D.L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact unitary_original_pushingUp_rudvalis_false s D.V₁ B D.Vplus hZV hBV hUV
      hTZ hTB hTU hZ hB hU
      (unitary_original_commuting_intersections D s earlier hUV hZV hTZ hTU hZ hU
        B hBV hTB hB hHfull h1332 fixed five)
      hcover hJH hc K hK e c hcV

end OriginalFlag
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
