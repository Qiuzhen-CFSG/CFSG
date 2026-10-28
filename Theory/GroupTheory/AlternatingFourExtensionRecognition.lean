module
public import GorensteinWalter.AutAlternatingFour
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic

/-!
A normal A₄ and an elementary four-group generate S₄ when their intersection has order two and the generated two-part has trivial centralizer of A₄. The action on A₄ is faithful and has order 24. This retains the actual generated subgroup in Aschbacher–Smith C.6.1, printed p.165.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem alternatingFour_extension_structure (K U V : Subgroup G)
    (e : K ≃* alternatingGroup (Fin 4)) (hUK : U ≤ K)
    (hUN : K ≤ normalizer (U : Set G)) (hU : Nat.card U = 4)
    [IsElementaryAbelian 2 V] (hV : Nat.card V = 4)
    (hVN : V ≤ normalizer (K : Set G))
    (hUV : Nat.card (U ⊓ V : Subgroup G) = 2)
    (hcent : (U ⊔ V) ⊓ centralizer (K : Set G) = ⊥) :
    Nonempty ((K ⊔ V : Subgroup G) ≃* Equiv.Perm (Fin 4)) ∧
      (K ⊔ V) ⊓ centralizer (K : Set G) = ⊥ := by
  have hK : Nat.card K = 12 := (Nat.card_congr e.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by simp))
  have hZ : center K = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4)),card_bot]
  let U₀ := U.subgroupOf K
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer hUN
  have hU₀ : Nat.card U₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv).trans hU
  have hquot : Nat.card (K ⧸ U₀) = 3 := by
    have hh := U₀.index_mul_card
    rw [hU₀,hK,index_eq_card] at hh
    omega
  have htwo : ∀ k ∈ K, k ^ 2 = 1 → k ∈ U := by
    intro k hk hk2
    let k₀ : K := ⟨k,hk⟩
    let q := QuotientGroup.mk' U₀
    have h2 : q k₀ ^ 2 = 1 := by
      rw [←map_pow]
      have he : k₀ ^ 2 = 1 := Subtype.ext hk2
      rw [he,map_one]
    have h3 : q k₀ ^ 3 = 1 := hquot ▸ pow_card_eq_one'
    have he : q k₀ = 1 := by
      simpa only [pow_succ,pow_zero,one_mul,h2] using h3
    exact (QuotientGroup.eq_one_iff k₀).mp he
  have hKV : K ⊓ V = U ⊓ V := by
    apply le_antisymm
    · rintro v ⟨hvK,hvV⟩
      exact ⟨htwo v hvK (elemPow_eq_one_of_isElementaryAbelian v hvV),hvV⟩
    · exact inf_le_inf_right V hUK
  have hE : Nat.card (K ⊔ V : Subgroup G) = 24 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes K V hVN
    rw [hK,hV,hKV,hUV] at hh
    omega
  have hEC : (K ⊔ V) ⊓ centralizer (K : Set G) = ⊥ := by
    apply bot_unique
    rintro z ⟨hz,hzc⟩
    have hm : z ∈ (K : Set G) * (V : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K V hVN]
      exact hz
    obtain ⟨k,hk,v,hv,rfl⟩ := hm
    have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
    have hkv : k * v = v * k := by
      have hh := hzc k hk
      exact mul_left_cancel (show k * (k * v) = k * (v * k) by simpa only [mul_assoc] using hh)
    have hsquare : (k * v) ^ 2 = k ^ 2 := by
      rw [Commute.mul_pow (show Commute k v from hkv),hv2,mul_one]
    have hk2c : k ^ 2 ∈ centralizer (K : Set G) :=
      hsquare ▸ (centralizer (K : Set G)).pow_mem hzc 2
    have hk2z : (⟨k ^ 2,K.pow_mem hk 2⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hk2c a a.property)
    have hk2 : k ^ 2 = 1 := congrArg Subtype.val (hZ.le hk2z)
    exact hcent.le ⟨mul_mem_sup (htwo k hk hk2) hv,hzc⟩
  let E := K ⊔ V
  have hEN : E ≤ normalizer (K : Set G) := sup_le K.le_normalizer hVN
  let a : E →* MulAut K := K.normalizerMonoidHom.comp (inclusion hEN)
  have hai : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro z hz
    have hc : inclusion hEN z ∈ K.normalizerMonoidHom.ker := hz
    rw [normalizerMonoidHom_ker] at hc
    exact Subtype.ext (hEC.le ⟨z.property,hc⟩)
  let b : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  let f : E →* Equiv.Perm (Fin 4) :=
    b.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp a)
  have hfi : Function.Injective f := b.symm.injective.comp ((MulAut.congr e).injective.comp hai)
  have hcard : Nat.card E = Nat.card (Equiv.Perm (Fin 4)) := by
    rw [hE,Nat.card_perm,Nat.card_fin]
    rfl
  exact ⟨⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,hcard⟩)⟩,hEC⟩
end Theory.GroupTheory
