module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CComponent.ThreeCore
public import Mathlib.GroupTheory.Subgroup.Simple
public import Theory.GroupTheory.ComponentPairNormalizer
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.SpecificGroups.PSL2.PairedOuterThree
/-!
# Three-prime index of a pair of commuting normal factors

Conjugation has centralizer kernel and carries the join onto the full inner
product. Centerless factors divisible by three use both available ranks,
so the centralizer has three-prime order. The exact binary PSL2 paired
outer calculation gives three-prime index; so does three-prime order of
both individual outer quotients. All normality is in the action domain.
Source: Aschbacher--Smith 1.2.2(a), printed p.504, 1 March 2004.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.TwoOrbitThree
variable {G : Type*} [Group G] (L M : Subgroup G) [L.Normal] [M.Normal]

@[expose] noncomputable def pairedConjugation : G →* (MulAut L × MulAut M) :=
  (MulAut.conjNormal : G →* MulAut L).prod (MulAut.conjNormal : G →* MulAut M)

theorem pairedConjugation_ker : (pairedConjugation L M).ker = centralizer ((L ⊔ M : Subgroup G) : Set G) := by
  rw [pairedConjugation,MonoidHom.ker_prod,MulAut.conjNormal_ker_eq_centralizer,
    MulAut.conjNormal_ker_eq_centralizer]
  apply le_antisymm
  · apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mpr inf_le_left) (le_centralizer_iff.mpr inf_le_right)
  · exact le_inf (centralizer_le (show L ≤ L ⊔ M from le_sup_left)) (centralizer_le (show M ≤ L ⊔ M from le_sup_right))

private theorem conj_on_left (hcomm : ⁅L,M⁆ = ⊥) (l : L) :
    pairedConjugation L M l = (MulAut.conj l,1) := by
  apply Prod.ext
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (l : G) * x * (l : G)⁻¹ = x
    have h := commutator_eq_bot_iff_le_centralizer.mp hcomm l.property x x.property
    rw [←h,mul_inv_cancel_right]

private theorem conj_on_right (hcomm : ⁅L,M⁆ = ⊥) (m : M) :
    pairedConjugation L M m = (1,MulAut.conj m) := by
  apply Prod.ext
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (m : G) * x * (m : G)⁻¹ = x
    have h := commutator_eq_bot_iff_le_centralizer.mp hcomm x.property m m.property
    rw [h,mul_inv_cancel_right]
  · apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl

theorem pairedConjugation_map_join (hcomm : ⁅L,M⁆ = ⊥) :
    (L ⊔ M).map (pairedConjugation L M) = (MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M) := by
  apply le_antisymm
  · rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨l,hl,rfl⟩
      rw [show pairedConjugation L M l = (MulAut.conj (⟨l,hl⟩ : L),1) from
        conj_on_left L M hcomm ⟨l,hl⟩]
      exact ⟨⟨⟨l,hl⟩,rfl⟩,one_mem _⟩
    · rintro _ ⟨m,hm,rfl⟩
      rw [show pairedConjugation L M m = (1,MulAut.conj (⟨m,hm⟩ : M)) from
        conj_on_right L M hcomm ⟨m,hm⟩]
      exact ⟨one_mem _,⟨⟨m,hm⟩,rfl⟩⟩
  · rintro ⟨a,b⟩ ⟨⟨l,rfl⟩,⟨m,rfl⟩⟩
    refine ⟨l*m,(L ⊔ M).mul_mem ((show L ≤ L ⊔ M from le_sup_left) l.property) ((show M ≤ L ⊔ M from le_sup_right) m.property),?_⟩
    rw [map_mul,conj_on_left L M hcomm l,conj_on_right L M hcomm m]
    simp

theorem pairedConjugation_comap_inner (hcomm : ⁅L,M⁆ = ⊥) :
    ((MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M)).comap (pairedConjugation L M) =
      L ⊔ M ⊔ centralizer ((L ⊔ M : Subgroup G) : Set G) := by
  rw [←pairedConjugation_map_join L M hcomm,Subgroup.comap_map_eq,pairedConjugation_ker]

theorem join_index_coprime_three [Finite G] (hcomm : ⁅L,M⁆ = ⊥)
    (hC : Nat.Coprime 3 (Nat.card (centralizer ((L ⊔ M : Subgroup G) : Set G))))
    (hO : Nat.Coprime 3 (Nat.card (G ⧸
      ((MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M)).comap (pairedConjugation L M)))) :
    Nat.Coprime 3 (L ⊔ M).index := by
  change Nat.Coprime 3 (((MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M)).comap
    (pairedConjugation L M)).index at hO
  rw [pairedConjugation_comap_inner L M hcomm] at hO
  rw [← relIndex_mul_index (show L ⊔ M ≤ L ⊔ M ⊔ centralizer ((L ⊔ M : Subgroup G) : Set G)
    from le_sup_left)]
  apply Nat.Coprime.mul_right _ hO
  rw [relIndex_sup_left]
  exact hC.coprime_dvd_right (relIndex_dvd_card _ _)

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x,hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz,mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

omit [L.Normal] [M.Normal] in
theorem join_center_eq_bot (hcomm : ⁅L,M⁆ = ⊥)
    (hL : center L = ⊥) (hM : center M = ⊥) : center (L ⊔ M : Subgroup G) = ⊥ := by
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L M
    (disjoint_of_commuting_of_center_eq_bot hcomm hL)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact center_bot_transport e (by rw [Subgroup.center_prod,hL,hM,bot_prod_bot])

private theorem rank_pos_of_dvd {A : Type*} [Group A] [Finite A]
    (hd : 3 ∣ Nat.card A) : 1 ≤ primeRank 3 A := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  by_contra hn
  have hh := (primeRank_le_iff_elementary_card_le A (p := 3) (n := 0)).mp
    (by omega) (zpowers x) inferInstance
  rw [Nat.card_zpowers,hx,pow_zero] at hh
  omega

omit [L.Normal] [M.Normal] in
theorem centralizer_join_coprime_three [Finite G] (hcomm : ⁅L,M⁆ = ⊥)
    (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : 3 ∣ Nat.card L) (hdM : 3 ∣ Nat.card M) (hr : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer ((L ⊔ M : Subgroup G) : Set G))) := by
  apply centralizer_coprime_three_of_rank (L ⊔ M) (join_center_eq_bot L M hcomm hL hM) _ hr
  rw [primeRank_sup_eq_add_of_disjoint_commuting L M
    (disjoint_of_commuting_of_center_eq_bot hcomm hL)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)]
  have := rank_pos_of_dvd hdL
  have := rank_pos_of_dvd hdM
  omega

@[expose] noncomputable def markedAction {S : Type*} [Group S]
    (eL : L ≃* S) (eM : M ≃* S) : G →* (MulAut S × MulAut S) :=
  ((MulAut.congr eL).prodCongr (MulAut.congr eM)).toMonoidHom.comp (pairedConjugation L M)

theorem markedAction_map_join {S : Type*} [Group S]
    (eL : L ≃* S) (eM : M ≃* S) (hcomm : ⁅L,M⁆ = ⊥) :
    (L ⊔ M).map (markedAction L M eL eM) = (MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S) := by
  rw [markedAction,←Subgroup.map_map,pairedConjugation_map_join L M hcomm]
  change ((MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M)).map
    ((MulAut.congr eL).toMonoidHom.prodMap (MulAut.congr eM).toMonoidHom) = _
  ext a
  constructor
  · rintro ⟨⟨b,c⟩,⟨hb,hc⟩,rfl⟩
    exact ⟨MulAut.map_innerSubgroup_congr eL ▸ mem_map_of_mem _ hb,
      MulAut.map_innerSubgroup_congr eM ▸ mem_map_of_mem _ hc⟩
  · rintro ⟨ha,hright⟩
    rw [←MulAut.map_innerSubgroup_congr eL] at ha
    rw [←MulAut.map_innerSubgroup_congr eM] at hright
    obtain ⟨b,hb,he⟩ := ha
    obtain ⟨c,hc,hf⟩ := hright
    exact ⟨(b,c),⟨hb,hc⟩,Prod.ext he hf⟩

theorem markedAction_ker {S : Type*} [Group S]
    (eL : L ≃* S) (eM : M ≃* S) :
    (markedAction L M eL eM).ker = centralizer ((L ⊔ M : Subgroup G) : Set G) := by
  calc
    (markedAction L M eL eM).ker = (pairedConjugation L M).ker :=
      MonoidHom.ker_comp_of_injective (pairedConjugation L M)
        ((MulAut.congr eL).prodCongr (MulAut.congr eM)).toMonoidHom
        ((MulAut.congr eL).prodCongr (MulAut.congr eM)).injective
    _ = _ := pairedConjugation_ker L M

theorem markedAction_comap_inner {S : Type*} [Group S]
    (eL : L ≃* S) (eM : M ≃* S) (hcomm : ⁅L,M⁆ = ⊥) :
    ((MulAut.innerSubgroup S).prod (MulAut.innerSubgroup S)).comap (markedAction L M eL eM) =
      L ⊔ M ⊔ centralizer ((L ⊔ M : Subgroup G) : Set G) := by
  rw [←markedAction_map_join L M eL eM hcomm,Subgroup.comap_map_eq,markedAction_ker]

theorem binary_join_index_coprime_three [Finite G]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (eL : L ≃* Theory.PSL2.Group F) (eM : M ≃* Theory.PSL2.Group F)
    (hcomm : ⁅L,M⁆ = ⊥) (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : 3 ∣ Nat.card L) (hdM : 3 ∣ Nat.card M) (hr : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (L ⊔ M).index := by
  let a := markedAction L M eL eM
  have hC := centralizer_join_coprime_three L M hcomm hL hM hdL hdM hr
  have hk : Nat.Coprime 3 (Nat.card a.ker) := by rwa [markedAction_ker]
  have hrange : primeRank 3 a.range ≤ 2 := by
    apply (primeRank_le_of_surjective_of_coprime 3 a.rangeRestrict a.rangeRestrict_surjective ?_).trans hr
    simpa only [MonoidHom.ker_rangeRestrict] using hk
  have hI : (Theory.PSL2.inner F).prod (Theory.PSL2.inner F) ≤ a.range := by
    rw [show (Theory.PSL2.inner F).prod (Theory.PSL2.inner F) =
      (L ⊔ M).map a from (markedAction_map_join L M eL eM hcomm).symm]
    exact Subgroup.map_le_range _ _
  have ho := Theory.PSL2.PairedOuterThree.quotient_by_inner_preimage_coprime_three F a hI hrange
  change Nat.Coprime 3 (((MulAut.innerSubgroup (Theory.PSL2.Group F)).prod
    (MulAut.innerSubgroup (Theory.PSL2.Group F))).comap a).index at ho
  rw [markedAction_comap_inner L M eL eM hcomm] at ho
  rw [←relIndex_mul_index (show L ⊔ M ≤ L ⊔ M ⊔ centralizer ((L ⊔ M : Subgroup G) : Set G) from le_sup_left)]
  exact (hC.coprime_dvd_right (by rw [relIndex_sup_left]; exact relIndex_dvd_card _ _)).mul_right ho

theorem outer_join_index_coprime_three [Finite G] (hcomm : ⁅L,M⁆ = ⊥)
    (hL : center L = ⊥) (hM : center M = ⊥)
    (hdL : 3 ∣ Nat.card L) (hdM : 3 ∣ Nat.card M) (hr : primeRank 3 G ≤ 2)
    (hoL : Nat.Coprime 3 (MulAut.innerSubgroup L).index)
    (hoM : Nat.Coprime 3 (MulAut.innerSubgroup M).index) :
    Nat.Coprime 3 (L ⊔ M).index := by
  apply join_index_coprime_three L M hcomm
    (centralizer_join_coprime_three L M hcomm hL hM hdL hdM hr)
  change Nat.Coprime 3 (((MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M)).comap
    (pairedConjugation L M)).index
  have hh : Nat.Coprime 3 ((MulAut.innerSubgroup L).prod (MulAut.innerSubgroup M)).index := by
    simpa only [Subgroup.index_prod] using hoL.mul_right hoM
  exact hh.coprime_dvd_right (by rw [index_comap]; exact relIndex_dvd_index_of_normal _ _)

end Theory.GroupTheory.TwoOrbitThree
