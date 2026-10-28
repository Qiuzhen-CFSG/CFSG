module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenResidual
public import Theory.SpecificGroups.Alternating.SevenCyclicSolvable
public import Theory.SpecificGroups.Alternating.SevenComponent

/-!
# Cubic action and an actual escaping cubic in the seven-point row

For either A7 covering quotient, the faithful action through the central
quotient preserves the original full Sylow. The solvable seven-point bound
therefore makes the literal escaping action on C/O2(C) have order three.
No cubic-image order is supplied as a premise.

In the centerless A7 row, the three-rank and outer-group bounds make the
index of the same selected C prime to three. A Sylow three-subgroup of the
original Cartan intersection thus lies in C. Its action survives faithfully
through O2(C), and its image is the entire escaping cubic action. Mapping
back to G gives an actual order-three subgroup inside A and the same C,
still failing to normalize the original residual.

Both Hall conditions and the original whole-module input are retained.
Inversion from the original Sylow, exclusion of the triple cover and the
exhaustive non-rank-two sieve remain open; this is not LocalCartanSieve.
Source: Aschbacher--Smith 5.1.13, printed pp.636--637, using A.3.18,
printed pp.51--52, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem seven_central_equiv {Q : Type*} [Group Q] [Finite Q]
    (hm : IsAlternating Q 7 ∨ IsAlternatingCover Q 7) :
    Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 7)) := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hz : center Q = ⊥ := by
      apply bot_unique
      intro x hx
      have hh := (centerCongr e ⟨x,hx⟩).property
      change e x ∈ center (alternatingGroup (Fin 7)) at hh
      rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
      exact e.map_eq_one_iff.mp hh
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e⟩
  · exact hm.2.2

private def sevenAutEquiv : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

/-- In either seven-point covering row the original escaping action is cubic.
The assertion concerns the literal action on C/O₂(C), not a replacement image. -/
theorem alternating_seven_action_card_three
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ IsAlternatingCover (C ⧸ pCore 2 C) 7) :
    Nat.card ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C))) = 3 := by
  obtain ⟨hKR,_,_⟩ := normal_alternating_seven_residual_and_hall
    h hH hgen c hK hKT horbit hY hescape C hC hKC hm
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) (hKR ▸ hKC)
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  obtain ⟨hc,ho,_,_,hne,_⟩ := cartan_action_escape h hH hgen c hY hescape C hRC
  let f₀ := normalQuotientAction C (pCore 2 C)
  let Q := C ⧸ pCore 2 C
  let e := (seven_central_equiv hm).some
  let j : MulAut Q →* Equiv.Perm (Fin 7) :=
    sevenAutEquiv.symm.toMonoidHom.comp
      (MulAut.centralQuotientAction e)
  let : Group.IsPerfect C := hC.perfect
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (pCore 2 C)) (QuotientGroup.mk'_surjective _)
  have hj : Function.Injective j :=
    sevenAutEquiv.symm.injective.comp
      (MulAut.centralQuotientAction_injective e)
  let f := j.comp f₀
  let q : C →* alternatingGroup (Fin 7) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' (pCore 2 C)))
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hfC (x : C) : f (x : Y) = (q x : Equiv.Perm (Fin 7)) := by
    apply sevenAutEquiv.injective
    change sevenAutEquiv
      (sevenAutEquiv.symm _) = _
    rw [MulEquiv.apply_symm_apply,normalQuotientAction_inner,MulAut.centralQuotientAction_conj]
    rfl
  have hTY := hH.1.1.2.trans hY.2
  let S := T.subtype hTY
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let J := A.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y
  let : Group.IsSolvable (J.map f₀) := by
    rw [Subgroup.map_sup]
    exact h.cartan_sylow_action_isSolvable c hTY f₀
  let D := (A.subgroupOf Y).map f₀
  let : IsCyclic D := hc
  have hPj : ((P.mapSurjective hq : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup _).map
      (alternatingGroup (Fin 7)).subtype ≤ (J.map f₀).map j := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    change (q y : Equiv.Perm (Fin 7)) ∈ (J.map f₀).map j
    rw [←hfC]
    exact mem_map_of_mem j (mem_map_of_mem f₀ (mem_sup_right (by rw [hP] at hy; exact hy)))
  have hh := Theory.SpecificGroups.Alternating.SevenCyclicSolvable.image_card_one_or_three j D (J.map f₀) (map_mono le_sup_left) ho
    (P.mapSurjective hq) hPj
  rw [card_map_of_injective hj] at hh
  exact hh.resolve_left (fun he => hne (card_eq_one.mp he))


/-- The A7 row supplies an actual escaping cubic in the original Cartan
and the same selected containing component. No cubic subgroup is assumed. -/
theorem alternating_seven_escaping_cubic
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsAlternating (C ⧸ pCore 2 C) 7) :
    ∃ D : Subgroup G, D ≤ A ⊓ C.map Y.subtype ∧ Nat.card D = 3 ∧
      ¬ D ≤ normalizer (residual H : Set G) := by
  let f := normalQuotientAction C (pCore 2 C)
  let AY := A.subgroupOf Y
  let Dbar := AY.map f
  have hcard := alternating_seven_action_card_three h hH hgen c hK hKT horbit
    hY hescape C hC hKC (.inl hm)
  obtain ⟨hKR,_,_⟩ := normal_alternating_seven_residual_and_hall
    h hH hgen c hK hKT horbit hY hescape C hC hKC (.inl hm)
  have hRC : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) (hKR ▸ hKC)
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hDbar := (cartan_action_escape h hH hgen c hY hescape C hRC).2.2.2.1
  let e := hm.some
  have hz : center (C ⧸ pCore 2 C) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (alternatingGroup (Fin 7)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hr : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hrY : primeRank 3 Y ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 Y) pCore_isPGroup]
    exact (Chapter1.Section02.uniqueness_local_quotient_sqtk h.qtke hY.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (C ⧸ pCore 2 C))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    obtain ⟨m,hm⟩ := alternatingGroup.SevenComponent.outer_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right m).coprime_dvd_right hm
  have hindex := cComponent_index_coprime_three_of_quotient C hC hz hr hrY ho
  let P : Sylow 3 AY := default
  let U := (P : Subgroup AY).map AY.subtype
  have hUA : U ≤ AY := map_subtype_le _
  have hpU : IsPGroup 3 U := P.isPGroup'.map AY.subtype
  have hUC : U ≤ C := (le_primeToResidual_of_isPGroup hpU).trans
    (primeToResidual_le C hindex)
  have hmap : U.map f = Dbar := by
    let g := f.subgroupMap AY
    let Q := P.mapSurjective (f.subgroupMap_surjective AY)
    have htop : (Q : Subgroup Dbar) = ⊤ := by
      apply top_unique
      apply IsPGroup.le_sylow_of_normal
      apply IsPGroup.of_card (p := 3) (n := 1)
      change Nat.card (⊤ : Subgroup Dbar) = 3 ^ 1
      rw [Nat.card_congr (topEquiv (G := Dbar)).toEquiv,pow_one]
      exact hcard
    have hh := congrArg (Subgroup.map Dbar.subtype) htop
    rw [Sylow.coe_mapSurjective,Subgroup.map_map,← MonoidHom.range_eq_map,range_subtype] at hh
    change (P : Subgroup AY).map (f.comp AY.subtype) = Dbar at hh
    simpa only [U,Subgroup.map_map] using hh
  have hi : Function.Injective (f.comp U.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro u hu
    have hq : QuotientGroup.mk' (pCore 2 C) (inclusion hUC u) = 1 := by
      apply conj_injective_of_center_eq_bot hz
      rw [←normalQuotientAction_inner,map_one]
      exact hu
    have hm : (u : Y) ∈ (pCore 2 C).map C.subtype :=
      mem_map_of_mem C.subtype ((QuotientGroup.eq_one_iff _).mp hq)
    have hd : Disjoint U ((pCore 2 C).map C.subtype) :=
      hpU.disjoint_of_coprime (pCore_isPGroup.map C.subtype) (by decide)
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨u.property,hm⟩))
  have hUc : Nat.card U = 3 := by
    have hh := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    rw [MonoidHom.range_comp,range_subtype,hmap] at hh
    exact hh.trans hcard
  refine ⟨U.map Y.subtype,le_inf ?_ (map_mono hUC),?_,?_⟩
  · exact (map_mono (f := Y.subtype) hUA).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  · rw [card_map_of_injective Y.subtype_injective,hUc]
  · intro hn
    apply hDbar
    change Dbar ≤ normalizer (((residual H).subgroupOf Y).map f : Set _)
    rw [←hmap]
    apply (map_mono (f := f) ?_).trans (le_normalizer_map f)
    rw [←subgroupOf_normalizer_eq ((map_subtype_le _).trans hY.2)]
    exact map_le_iff_le_comap.mp hn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
