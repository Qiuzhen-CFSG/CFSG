module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalPreparation
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTransport
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalTwo
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalThree

/-!
# Global noncyclic endpoint of D.2.22

The D.2.14 configurations for every starred actor align with the canonical
order-three support family. In the three-plane case, `Jhat` generation makes every element
normalize each global support factor; in the two-plane case the whole group
permutes the two factors. The three-core fixed space vanishes by
D.2.20, so the original module is moved by O₃. The two-plane and three-plane
normalizer bounds then force `G = O₃ A`; the actor is Sylow and the global
reduced structure is literal on the original module.

Source: Aschbacher–Smith D.2.20–22, printed pp.188–189. The natural Ω⁺₄
marking in the two-plane branch is a separate model bridge; this file proves
the exact group/support endpoint needed before that marking.
-/
public section
namespace CFSG.Quasithin.ChapterD.SourceReduction
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open ElementaryCore.SupportExclusion FittingConfigurations
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
  (f : H →* G) (honto : Function.Surjective f)
  (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
  (hr : 1 < rank A)
  (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
  (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤)
  (hgen : Jhat ρ = ⊤)

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_normalizes_three_supports
    (d : SupportFactors ρ (pCore 3 G) 3) :
    ∀ g : G, ∀ i, g ∈ normalizer (d.ambient i : Set G) := by
  let : IsElementaryAbelian 3 (pCore 3 G) :=
    source_threeCore_elementary ρ hH f honto hf hA hr hF hcore hmoved
  have hall := (source_ratio_and_noncyclic ρ hH f honto hf hA hr hF hcore hmoved).2.2
  have hd : Module.finrank (ZMod 2) V = 6 := by simpa using d.finrank_eq ρ
  intro g i
  have hle : ⊤ ≤ normalizer (d.ambient i : Set G) := by
    rw [← hgen]
    refine sSup_le fun B hB => ?_
    obtain ⟨s,hs⟩ := source_reduced_on_original_module ρ hH f honto hf hB (hall B hB)
      hF hcore hmoved hgen
    obtain ⟨e,he,_⟩ := hs.configurations _
    let E := e.ofSubgroup ρ (show pCore 3 G ≤ pCore 3 G ⊔ B from le_sup_left)
    have hs3 : s = 3 := by have hh := E.finrank_eq ρ; omega
    obtain ⟨j,hj⟩ := E.canonical_eq_factor ρ hf (d.factor_canonical ρ i)
    have hn : B.subgroupOf (pCore 3 G ⊔ B) ≤ normalizer (e.ambient j : Set (pCore 3 G ⊔ B : Subgroup G)) := by
      rcases he with ⟨hs2,_⟩ | ⟨_,he⟩
      · omega
      · exact (he j).1
    rw [hj]
    change B ≤ normalizer ((e.ofSubgroup ρ le_sup_left).ambient j : Set G)
    rw [SupportFactors.ofSubgroup_ambient]
    have hh := (map_mono hn).trans ((e.ambient j).le_normalizer_map (pCore 3 G ⊔ B).subtype)
    rw [map_subgroupOf_eq_of_le (show B ≤ pCore 3 G ⊔ B from le_sup_right)] at hh
    exact hh
  exact hle (mem_top g)

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_generated_by_threeCore_actor : pCore 3 G ⊔ A = ⊤ := by
  let P := pCore 3 G
  let L := P ⊔ A
  let : IsElementaryAbelian 3 P :=
    source_threeCore_elementary ρ hH f honto hf hA hr hF hcore hmoved
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨s,hs⟩ := source_reduced_on_original_module ρ hH f honto hf hA hr hF hcore hmoved hgen
  have hP : Nat.card P = 3 ^ s :=
    (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).toEquiv).symm.trans hs.card_core
  obtain ⟨d,hd,_⟩ := hs.configurations _
  have hAcard := (actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore).1
  rcases hs.rank_cases with rfl | rfl
  · let D := d.ofSubgroup ρ (show P ≤ L from le_sup_left)
    have hL : Nat.card L = 36 := by
      have hdis : Disjoint P A := IsPGroup.disjoint_of_coprime
        (IsElementaryAbelian.isPGroup 3 P) (IsElementaryAbelian.isPGroup 2 A) (by decide)
      rw [card_sup_eq_mul_of_normalizes_of_disjoint P A le_normalizer_of_normal hdis,
        hP,hAcard]
      decide
    have hlow : 1 < cubicRatio ρ := by
      rw [(source_ratio_and_noncyclic ρ hH f honto hf hA hr hF hcore hmoved).2.1]
      norm_num [ENNReal.lt_div_iff_mul_lt]
    exact D.eq_top_of_card_thirty_six ρ hf (D.factor_conj_closed ρ hf) L hL hlow
  · let D := d.ofSubgroup ρ (show P ≤ L from le_sup_left)
    exact (D.three_plane_global hf hP
      (source_normalizes_three_supports ρ hH f honto hf hA hr hF hcore hmoved hgen D)
      (source_involution_threeCore_centralizer_cyclic ρ hH f honto hf hA hr hF hcore hmoved hgen)
      A hAcard).1

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_global_reduced : ∃ s : ℕ, Reduced ρ (pCore 3 G) A s := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨hcard,hfix⟩ := actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore
  have hfaith := actor_faithful_three ρ hf hA hr hF hcore
  have hsupport := source_lemma_D_2_14_hyperplaneSupport ρ hf hA hcard hfix
  obtain ⟨hElem, ⟨s, hs, hcP, _⟩, hcomm⟩ :=
    ElementaryCore.elementary_structure_of_hyperplaneSupport ρ hf (pCore 3 G) A pCore_isPGroup
      hcard le_normalizer_of_normal hfaith hfix hsupport
  exact ⟨s,⟨hf,inferInstance,hElem,hcP,hs,hcard,hA,
    source_generated_by_threeCore_actor ρ hH f honto hf hA hr hF hcore hmoved hgen,
    hfaith,hfix,hcomm,source_threeCore_moved ρ hH f honto hf hA hr hF hcore hmoved hgen,
    hsupport⟩⟩

include hH f honto hf hA hr hF hcore hmoved hgen in
theorem source_noncyclic_global_configurations :
    ∃ s : ℕ, ∃ _h : Reduced ρ (pCore 3 G) A s,
      ∃ d : SupportFactors ρ (pCore 3 G) s, d.Alternatives A ∧
      Module.finrank (ZMod 2) V = 2 * s ∧ cubicRatio ρ = 3 / 2 ∧
      ∃ S : Sylow 2 G, (S : Subgroup G) = A := by
  obtain ⟨s,h⟩ := source_global_reduced ρ hH f honto hf hA hr hF hcore hmoved hgen
  obtain ⟨d,hd,_,hq⟩ := h.configurations ρ
  refine ⟨s,h,d,hd,d.finrank_eq ρ,hq,?_⟩
  let : IsElementaryAbelian 3 (pCore 3 G) := h.elementary
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hdis : Disjoint (pCore 3 G) A := IsPGroup.disjoint_of_coprime
    pCore_isPGroup (IsElementaryAbelian.isPGroup 2 A) (by decide)
  have hG : Nat.card G = 3 ^ s * 4 := by
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint (pCore 3 G) A
      le_normalizer_of_normal hdis
    rw [h.generated,card_top,h.card_core,h.card_actor] at hc
    exact hc
  refine ⟨Sylow.ofCard A ?_,rfl⟩
  rcases h.rank_cases with rfl | rfl <;> rw [h.card_actor,hG] <;> decide +kernel

end CFSG.Quasithin.ChapterD.SourceReduction
