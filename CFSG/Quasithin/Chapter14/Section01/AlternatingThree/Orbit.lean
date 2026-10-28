module

public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.Alternating.FourPairOuter
public import Theory.GroupTheory.OuterPGroupSylowSupplement

/-!
# The original normal cubic orbit and its centralizer alternative

The source three-rank and characteristic-two hypotheses give the actual
normal Sylow orbit N of the original A₃ block X. Its A₄ or A₄² marking
makes its center trivial and its outer group a two-group. Hence N, its
centralizer and the original Sylow subgroup generate the local overgroup.
The nontrivial-centralizer branch proves M=Mc and |Ω₁Z(T)|>2; otherwise
the action on this same original orbit is faithful.

Source: Aschbacher--Smith 14.1.10, printed p.978, using C.1.28.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
variable {G : Type*} [Group G] [Finite G]

private theorem center_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hh := (centerCongr e ⟨x,hx⟩).property
  change e x ∈ center B at hh
  rw [hz,mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

omit [Finite G] in
/-- The actual model alternatives give the precise outer and center facts used by the source. -/
theorem cubic_model_structure (N : Subgroup G)
    (hm : Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) :
    N ≠ ⊥ ∧ center N = ⊥ ∧ IsPGroup 2 (MulAut.Outer N) := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hc : Nat.card N = 12 := (Nat.card_congr e.toEquiv).trans
      (alternatingGroup.card_of_card_eq_four (by norm_num))
    refine ⟨fun he => by rw [he,card_bot] at hc; norm_num at hc,
      center_bot_of_equiv e (alternatingGroup.center_eq_bot (by norm_num)),?_⟩
    exact AlternatingFourPair.outer_single_two.of_equiv (MulAut.outerCongr e).symm
  · obtain ⟨e⟩ := hm
    have hc : Nat.card N = 144 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (AlternatingFourPair.A × AlternatingFourPair.A) = 144
      rw [Nat.card_prod,alternatingGroup.card_of_card_eq_four (by norm_num)]
    refine ⟨fun he => by rw [he,card_bot] at hc; norm_num at hc,
      center_bot_of_equiv e AlternatingFourPair.center_eq_bot,?_⟩
    exact AlternatingFourPair.outer_pair_two.of_equiv (MulAut.outerCongr e).symm

/-- The normal orbit is constructed from the original local hypotheses. -/
theorem source_cubic_orbit {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (X : Subgroup M) (hb : ChapterC.IsBlock X) (ha : ChapterC.IsAlternatingBlock X 3) :
    let N := conjugateSpanBy X (T.subtype hM.2 : Subgroup M)
    N.Normal ∧ (Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) := by
  have hf : generalizedFitting M = pCore 2 M :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (hG.evenCharacteristic T M hM.1 hM.2)
  have hr : primeRank 3 M ≤ 2 :=
    (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  exact ChapterC.RankOne.ChiProduct.cubic_orbit_models hf hr (T.subtype hM.2) X hb ha

omit [Finite G] in
private theorem map_local_centralizer (M : Subgroup G) (N : Subgroup M) :
    (centralizer (N : Set M)).map M.subtype = M ⊓ centralizer (N.map M.subtype : Set G) := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    refine ⟨y.property,?_⟩
    rintro n ⟨a,ha,rfl⟩
    exact congrArg M.subtype (hy a ha)
  · rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    intro n hn
    exact Subtype.ext (hc n ⟨n,hn,rfl⟩)

/-- A faithful action is the only remaining branch after the original placement argument. -/
theorem source_centralizer_alternative {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    (N : Subgroup M) [N.Normal]
    (hm : Nonempty (N ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (N ≃* AlternatingFourPair.Model)) :
    (M = Mc ∧ 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))) ∨
      centralizer (N : Set M) = ⊥ := by
  classical
  by_cases hC : centralizer (N : Set M) = ⊥
  · exact Or.inr hC
  left
  obtain ⟨hne,hz,ho⟩ := cubic_model_structure N hm
  let A := N.map M.subtype
  have hAM : A ≤ M := map_subtype_le _
  have hAn : (A.subgroupOf M).Normal := by
    have he : A.subgroupOf M = N := by
      change (N.map M.subtype).comap M.subtype = N
      rw [comap_map_eq,(MonoidHom.ker_eq_bot_iff M.subtype).mpr M.subtype_injective,sup_bot_eq]
    rw [he]
    infer_instance
  have hAe : N ≃* A := N.equivMapOfInjective M.subtype M.subtype_injective
  have hAz : center A = ⊥ := center_bot_of_equiv hAe.symm hz
  have hAne : A ≠ ⊥ := by
    exact (N.map_eq_bot_iff_of_injective M.subtype_injective).not.mpr hne
  have hAC : M ⊓ centralizer (A : Set G) ≠ ⊥ := by
    rw [←map_local_centralizer M N]
    exact ((centralizer (N : Set M)).map_eq_bot_iff_of_injective M.subtype_injective).not.mpr hC
  have hchar : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2 := by
    rintro x ⟨hx,hxc⟩
    have hh : (⟨x,hx⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro q hq
      exact Subtype.ext (hxc q ⟨q,hq,rfl⟩)
    exact ⟨⟨x,hx⟩,hG.evenCharacteristic T M hM.1 hM.2 hh,rfl⟩
  have hgen : (A ⊔ (M ⊓ centralizer (A : Set G))) ⊔ (T : Subgroup G) = M := by
    have hh := congrArg (map M.subtype)
      (normal_centralizer_sup_sylow_eq_top N (T.subtype hM.2) ho)
    simpa only [Subgroup.map_sup,map_local_centralizer,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.2,←MonoidHom.range_eq_map,range_subtype] using hh
  exact conclusion_of_nontrivial_centralizer T hM hu hAM hAn hAne hchar hAz hAC hgen

end CFSG.Quasithin.Chapter14.AlternatingThree
