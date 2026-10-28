module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.SylowActors
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SolvableActors
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank

/-!
# The actual escaping cubic in the selected Hall--Janko component

The original Cartan and full Sylow generate a solvable quotient action.
The native J₂ solvable-actor theorem forces its nontrivial cyclic odd action
to have order three. The component quotient has three-rank two and a
two-group outer automorphism group. The ambient three-rank bound therefore
makes the selected component's index prime to three. A Sylow three-subgroup
of the original Cartan intersection lies in that same component and maps
onto the whole escaping action. Its order is three, since odd order makes
it disjoint from the two-core and the quotient is centerless.

Finally the entire original intersection A ∩ C injects into that cubic
action, so it is exactly an escaping cubic. The source applications keep
the original W, Sylow, both Hall conditions and quotient maps. The residual
A₅ identification, inversion from the original Sylow and exhaustive row
selection remain obligations; no LocalCartanWitness is asserted here.

Source: Aschbacher--Smith 5.1.13, printed p.637, and A.3.18,
printed pp.51--52, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
variable {G : Type*} [Group G] [Finite G]

private theorem jankoTwo_center_bot {Q : Type*} [Group Q]
    (e : Q ≃* Sporadic.LeechRelated.J2.Carrier) : center Q = ⊥ := by
  apply bot_unique
  intro x hx
  have hh := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center Sporadic.LeechRelated.J2.Carrier at hh
  rw [Sporadic.LeechRelated.J2.OrdinaryLocal.center_eq_bot,mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

/-- The literal escaping action on the same selected J₂ quotient has order
three. Neither a residual model nor a cubic actor is supplied as a premise. -/
theorem janko_two_action_card_three
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) [C.Normal] (hRC : (residual H).subgroupOf Y ≤ C)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    Nat.card ((A.subgroupOf Y).map (normalQuotientAction C (pCore 2 C))) = 3 := by
  obtain ⟨hc,ho,_,_,hne,_⟩ := cartan_action_escape h hH hgen c hY hescape C hRC
  let f₀ := normalQuotientAction C (pCore 2 C)
  let e := hm.some
  let i := MulAut.congr e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfC (x : C) : i (f₀ (x : Y)) = MulAut.conj (q x) := by
    rw [normalQuotientAction_inner,MulAut.congr_conj]
    rfl
  have hTY := hH.1.1.2.trans hY.2
  let S := T.subtype hTY
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let J := (A.subgroupOf Y).map f₀ ⊔ ((T : Subgroup G).subgroupOf Y).map f₀
  let D := (A.subgroupOf Y).map f₀
  let : Group.IsSolvable J := h.cartan_sylow_action_isSolvable c hTY f₀
  let : IsCyclic D := hc
  have hPj : ((P.mapSurjective hq : Sylow 2 Sporadic.LeechRelated.J2.Carrier) : Subgroup _).map
      MulAut.conj ≤ J.map i.toMonoidHom := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    rw [←hfC]
    exact mem_map_of_mem i.toMonoidHom
      (mem_sup_right (mem_map_of_mem f₀ (by rw [hP] at hy; exact hy)))
  have hs : Group.IsSolvable (J.map i.toMonoidHom) :=
    Group.isSolvable_of_surjective (i.toMonoidHom.subgroupMap_surjective J)
  have hd := Sporadic.LeechRelated.J2.SolvableActors.cyclic_odd_aut_card_dvd_three
    (P.mapSurjective hq) (J.map i.toMonoidHom) (D.map i.toMonoidHom) hPj hs
    (map_mono le_sup_left) (by rwa [card_map_of_injective i.injective])
    (isCyclic_of_surjective (i.toMonoidHom.subgroupMap D) (i.toMonoidHom.subgroupMap_surjective D))
  rw [card_map_of_injective i.injective] at hd
  exact ((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left (fun he => hne (card_eq_one.mp he))

/-- The original Cartan has a genuine escaping cubic inside the same selected
J₂ component. Its image is the entire literal quotient action. -/
theorem janko_two_escaping_cubic
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : (residual H).subgroupOf Y ≤ C)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    ∃ D : Subgroup G, D ≤ A ⊓ C.map Y.subtype ∧ Nat.card D = 3 ∧
      ¬ D ≤ normalizer (residual H : Set G) := by
  let f := normalQuotientAction C (pCore 2 C)
  let AY := A.subgroupOf Y
  let Dbar := AY.map f
  have hcard := janko_two_action_card_three h hH hgen c hY hescape C hRC hm
  have hDbar := (cartan_action_escape h hH hgen c hY hescape C hRC).2.2.2.1
  let e := hm.some
  have hz := jankoTwo_center_bot e
  have hr : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by
    rw [primeRank_congr 3 e]
    exact Sporadic.LeechRelated.J2.three_rank_ge_two
  have hrY : primeRank 3 Y ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 Y) pCore_isPGroup]
    exact (Chapter1.Section02.uniqueness_local_quotient_sqtk h.qtke hY.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (C ⧸ pCore 2 C))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    obtain ⟨m,hm⟩ := Sporadic.LeechRelated.J2.outer_isTwoGroup.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right m).coprime_dvd_right hm
  have hindex := cComponent_index_coprime_three_of_quotient C hC hz hr hrY ho
  let P : Sylow 3 AY := default
  let U := (P : Subgroup AY).map AY.subtype
  have hUA : U ≤ AY := map_subtype_le _
  have hpU : IsPGroup 3 U := P.isPGroup'.map AY.subtype
  have hUC : U ≤ C := (le_primeToResidual_of_isPGroup hpU).trans
    (primeToResidual_le C hindex)
  have hmap : U.map f = Dbar := by
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

/-- The cubic just constructed is the whole original intersection A ∩ C.
In particular this exact intersection still escapes the residual normalizer. -/
theorem janko_two_cartan_intersection
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : (residual H).subgroupOf Y ≤ C)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.J2.Carrier)) :
    Nat.card (A ⊓ C.map Y.subtype : Subgroup G) = 3 ∧
      ¬ A ⊓ C.map Y.subtype ≤ normalizer (residual H : Set G) := by
  let f := normalQuotientAction C (pCore 2 C)
  let U := A.subgroupOf Y ⊓ C
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  let j : U →* A := {
    toFun x := ⟨x.val.val,x.property.1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : G)) he))
  have hoU : Odd (Nat.card U) := hoA.of_dvd_nat (card_dvd_of_injective j hj)
  have hi : Function.Injective (f.comp U.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro u hu
    have hq : QuotientGroup.mk' (pCore 2 C) (inclusion (show U ≤ C from inf_le_right) u) = 1 := by
      apply conj_injective_of_center_eq_bot (jankoTwo_center_bot hm.some)
      rw [←normalQuotientAction_inner,map_one]
      exact hu
    have hx : (u : Y) ∈ (pCore 2 C).map C.subtype :=
      mem_map_of_mem C.subtype ((QuotientGroup.eq_one_iff _).mp hq)
    have hd : Disjoint U ((pCore 2 C).map C.subtype) := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := ((pCore_isPGroup (p := 2) (G := C)).map C.subtype).exists_card_eq
      rw [hk]
      exact hoU.coprime_two_right.pow_right k
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨u.property,hx⟩))
  have hUc : Nat.card U ≤ 3 := by
    have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    rw [MonoidHom.range_comp,range_subtype] at he
    rw [he,←janko_two_action_card_three h hH hgen c hY hescape C hRC hm]
    exact card_le_of_le (map_mono (show U ≤ A.subgroupOf Y from inf_le_left))
  have he : U.map Y.subtype = A ⊓ C.map Y.subtype := by
    change (A.subgroupOf Y ⊓ C).map Y.subtype = _
    rw [Subgroup.map_inf _ _ _ Y.subtype_injective,subgroupOf_map_subtype,inf_assoc,
      inf_eq_right.mpr (map_subtype_le C)]
  have hup : Nat.card (A ⊓ C.map Y.subtype : Subgroup G) ≤ 3 := by
    rw [←he,card_map_of_injective Y.subtype_injective]
    exact hUc
  obtain ⟨D,hD,hDc,hDn⟩ := janko_two_escaping_cubic h hH hgen c hY hescape C hC hRC hm
  exact ⟨le_antisymm hup (hDc ▸ card_le_of_le hD),fun hn => hDn (hD.trans hn)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
