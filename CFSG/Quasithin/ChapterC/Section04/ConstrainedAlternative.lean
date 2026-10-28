module
public import Theory.GroupTheory.CComponent.ConstrainedPrimeJoin
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.CharacteristicTwo
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow

/-!
# The constrained-component alternative in C.4.4

Restrict the moving-component case to K joined with R. Its two-component
orbit makes this join invariant under N(R), so radicality restricts. The
join has characteristic two, and the existing Thompson argument shows
that J(R) fixes K. The displacement argument then proves that either R
normalizes K or its intersection with K is a full Sylow two-subgroup.
The final theorem applies this to the literal C.2.8 subgroups.

Only the intrinsic constrained hypothesis on K is required; characteristic
two is proved in the restricted join. The later exclusion of the Sylow
alternative remains a separate C.4.4 obligation.
Source: Aschbacher--Smith C.2.4(2) and C.4.4, printed pp.144 and 152.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section04Constrained
variable {G : Type*} [Group G] [Finite G]

theorem component_orbit_bound {κ : CFSG.Quasithin.GroupClass}
    (hG : CFSG.Quasithin.IsSQTK κ G) {K : Subgroup G} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    K.Normal ∨ (normalizer (K : Set G)).index = 2 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hKq : IsComponent (G ⧸ pCore 2 G) (K.map q) :=
    ⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),
      IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)⟩
  have hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p (G ⧸ pCore 2 G) ≤ 2 := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  exact cComponent_normal_or_index_two_of_quotient hK (pCore 2 G)
    (hKq.normal_or_index_two_of_odd_rank_le_two hrank)

theorem thompson_le_component_normalizer_of_constrained
    {κ : CFSG.Quasithin.GroupClass} (hG : CFSG.Quasithin.IsSQTK κ G)
    (R M K : Subgroup G) (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hout : ¬ K ≤ M)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (ho : pPrimeCore 2 G = ⊥) (hf : generalizedFitting K = pCore 2 K) :
    Stellmacher.elementaryAbelianMaxJ R ≤ normalizer (K : Set G) := by
  by_cases hn : R ≤ normalizer (K : Set G)
  · exact (sSup_le fun _ hA => hA.1).trans hn
  have hi : (normalizer (K : Set G)).index = 2 := by
    rcases component_orbit_bound hG hK with hnormal | hi
    · let := hnormal
      exact (hn (by rw [normalizer_eq_top]; exact le_top)).elim
    · exact hi
  let J := K ⊔ R
  have hRJ : R ≤ J := le_sup_right
  have hKJ : K ≤ J := le_sup_left
  have hrJ : IsPRadical 2 (R.subgroupOf J) :=
    hr.subgroupOf_of_normalizer_normalizes J hRJ (normalizer_join_of_moved_index_two hi hn)
  have hcJ : (R.subgroupOf J).characteristicNormalizerClosure ≤ M.subgroupOf J :=
    characteristicNormalizerClosure_subgroupOf_le hRJ hcontrol
  have houtJ : ¬ K.subgroupOf J ≤ M.subgroupOf J := by
    intro hh
    exact hout (fun k hk => hh (show (⟨k,hKJ hk⟩ : J) ∈ K.subgroupOf J from hk))
  let e := subgroupOfEquivOfLe hKJ
  let : IsQuasisimple ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have ht := Section02Source.thompson_le_component_normalizer_of_characteristicTwo
    (R.subgroupOf J) (M.subgroupOf J) (K.subgroupOf J) hrJ
    (hK.constrained_join_characteristicTwo hr.isPGroup ho hf) hcJ houtJ (hK.subgroupOf hKJ)
  have hm := (map_mono (f := J.subtype) ht).trans
    ((K.subgroupOf J).le_normalizer_map J.subtype)
  rw [← Stellmacher.elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
    map_subgroupOf_eq_of_le hRJ,map_subgroupOf_eq_of_le hKJ] at hm
  exact hm

theorem sylow_intersection_or_normalizes_of_constrained
    {κ : CFSG.Quasithin.GroupClass} (hG : CFSG.Quasithin.IsSQTK κ G)
    (R M K : Subgroup G) (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hs : IsSylowInNormalClosure R M) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (ho : pPrimeCore 2 G = ⊥) (hf : generalizedFitting K = pCore 2 K) :
    (∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = R ⊓ K) ∨
      R ≤ normalizer (K : Set G) := by
  classical
  by_cases hm : R ≤ normalizer (K : Set G)
  · exact Or.inr hm
  left
  by_cases hKM : K ≤ M
  · exact Section02Source.moved_component_inside_control_sylow hs hK hKM hm
  by_contra hn
  let : (normalizer (K : Set G)).Normal := Section02Source.component_normalizer_normal hG hK
  have hJ := thompson_le_component_normalizer_of_constrained hG R M K hr hcontrol hKM hK ho hf
  have hNM := Section02Source.stabilizer_normalizer_control hr hcontrol hJ
  obtain ⟨y,s,hy,hsR,hp,hwN,hwK,hwout⟩ := Section02Source.moving_component_displacement hr hK hm hn
  exact hwout (Section02Source.displacement_mem_radical_stabilizer hs y s (hNM hy.2) hsR hp hwK hwN)
end CFSG.Quasithin.ChapterC.Section04Constrained

namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

theorem constrained_component_sylow_or_normalized
    (h : HypothesisC28 κ H M L R V) (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K) :
    (∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = R.subgroupOf H ⊓ K) ∨
      R.subgroupOf H ≤ normalizer (K : Set H) := by
  let := hq
  have hRM := h.radical_le
  have hRH := hRM.trans h.local_le
  let MH := M.subgroupOf H
  let RH := R.subgroupOf H
  let e : MH ≃* M := subgroupOfEquivOfLe h.local_le
  let N := normalClosure (R.subgroupOf M : Set M)
  let NH := normalClosure (RH.subgroupOf MH : Set MH)
  have heR : e '' (RH.subgroupOf MH : Set MH) = (R.subgroupOf M : Set M) := by
    ext r
    constructor
    · rintro ⟨s,hs,rfl⟩; exact hs
    · intro hr
      exact ⟨⟨⟨r,h.local_le r.property⟩,r.property⟩,hr,rfl⟩
  have heN : NH.map e.toMonoidHom = N := by
    rw [map_normalClosure _ _ e.surjective]
    change normalClosure (e '' (RH.subgroupOf MH : Set MH)) = N
    rw [heR]
  let eN : NH ≃* N := (e.subgroupMap NH).trans (MulEquiv.subgroupCongr heN)
  obtain ⟨S,hS⟩ := h.sylow_in_normalClosure
  let T : Sylow 2 NH := S.mapSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  have hsy : IsSylowInNormalClosure RH MH := by
    refine ⟨T,?_⟩
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH]
    change (((((S : Subgroup N).map eN.symm.toMonoidHom).map NH.subtype).map MH.subtype).map H.subtype) = R
    rw [map_map,map_map,map_map]
    apply Eq.trans ?_ hS
    rw [map_map]
    congr 1
  exact Section04Constrained.sylow_intersection_or_normalizes_of_constrained h.sqtk
    RH MH K h.isRadical h.characteristic_control hsy hK h.oddCore_eq_bot hf
end CFSG.Quasithin.ChapterC.HypothesisC28
