module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCentralizerCore
public import Theory.GroupTheory.NormalizerAction.OmegaCenterCentralizer
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupAction.AutomorphismFixerCardinality
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage

/-!
# Small marked centralizers around a subnormal M₂₂

A subnormal M₂₂ in a group of three-rank at most two has a centralizer
of three-rank zero. If a marked centralizer has order dividing 2304,
this full component centralizer is a two-group. Trivial ambient two-core
then makes it trivial, by generalized-Fitting detection for components.

The centralizer of a nonidentity marker normalizes its component, even
though the component need not be ambient normal. Its faithful action fixes
the same involution of M₂₂. The inner fixer has order 384 and the outer
index divides two, giving an upper bound of 768.

Source application: Aschbacher--Smith, final paragraph of 14.3.20,
printed p.998, and the M₂₂ alternative in 1.1.5(3)(f), printed p.502.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu

/-- The actual abstract automorphism group has inner index dividing two. -/
theorem m22_inner_index_dvd_two : (MulAut.innerSubgroup M22).index ∣ 2 := by
  let N := M22.subgroupOf m22DesignAut
  let : N.Normal := M22_normal_in_m22DesignAut
  have hle : N ≤ (MulAut.innerSubgroup M22).comap m22DesignAutToAut := by
    intro g hg
    refine ⟨⟨g.val, hg⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm]
    rfl
  let q : (m22DesignAut ⧸ N) →* MulAut.Outer M22 :=
    QuotientGroup.map N (MulAut.innerSubgroup M22) m22DesignAutToAut hle
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup M22) x
    obtain ⟨g, rfl⟩ := m22DesignAutToAut_surjective a
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have htwo : Nat.card (m22DesignAut ⧸ N) = 2 := by
    rw [← N.index_eq_card]
    have heq : N = m22EvenDesignAut := by
      ext g
      simp [N, M22, m22EvenDesignAut]
    rw [heq, m22EvenDesignAut_index]
  rw [index_eq_card]
  exact htwo ▸ card_dvd_of_surjective q hq

/-- The full automorphism fixer of an involution has order at most 768. -/
theorem m22_involution_fixer_card_le (t : M22) (ht : orderOf t = 2) :
    Nat.card (fixingSubgroup (MulAut M22) (zpowers t : Set M22)) ≤ 768 := by
  have hb := MulAut.card_fixingSubgroup_le_centralizer_mul_outer_index (zpowers t)
  have hc : centralizer (zpowers t : Set M22) = centralizer ({t} : Set M22) := by
    rw [zpowers_eq_closure,centralizer_closure]
  rw [hc, M22FourNormalizers.involution_centralizer_card t ht] at hb
  have hi := Nat.le_of_dvd (by decide : 0 < 2) m22_inner_index_dvd_two
  omega

private theorem m22_quasisimple : IsQuasisimple M22 := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  have hna : ¬ IsMulCommutative M22 := by
    intro ha
    let := ha
    have he : (⊥ : Subgroup M22) = ⊤ := m22_center_eq_bot.symm.trans center_eq_top
    exact bot_ne_top he
  let : Group.IsPerfect M22 := ⟨
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator M22) inferInstance).resolve_left
      (fun h => hna ((commutator_eq_bot_iff M22).mp h))⟩
  exact ⟨
    ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩

variable {D : Type*} [Group D] [Finite D]

/-- Rank and the small marked centralizer force the full component centralizer to vanish. -/
theorem m22_component_centralizer_eq_bot (j : M22 →* D) (hj : Function.Injective j)
    (hsub : j.range.IsSubnormal) (hrank : primeRank 3 D ≤ 2)
    (hcore : pCore 2 D = ⊥) (t : M22)
    (hcard : Nat.card (centralizer ({j t} : Set D)) ∣ 2304) :
    centralizer (j.range : Set D) = ⊥ := by
  let K := j.range
  let C := centralizer (K : Set D)
  let e : M22 ≃* K := MonoidHom.ofInjective hj
  have hZ : center K = ⊥ := by
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have he : e.symm x ∈ center M22 := ((centerCongr e).symm ⟨x,hx⟩).property
    rw [m22_center_eq_bot,mem_bot] at he
    exact e.symm.injective (he.trans (map_one e.symm).symm)
  have hrK : primeRank 3 K = 2 := (primeRank_congr 3 e).symm.trans m22_primeRank_three
  have hr := ResidualCentralizerRank.primeRank_add_le_of_center_coprime C K le_rfl
    (show Nat.Coprime 3 (Nat.card (center K)) by rw [hZ,Nat.card_unique]; decide)
  have h3 : ¬ 3 ∣ Nat.card C :=
    PrimeRank.eq_zero_iff_not_dvd_card.mp (by omega : primeRank 3 C = 0)
  have hCmark : C ≤ centralizer ({j t} : Set D) :=
    centralizer_le (Set.singleton_subset_iff.mpr ⟨t,rfl⟩)
  have hCcard : Nat.card C ∣ 2304 := (card_dvd_of_le hCmark).trans hcard
  have hc9 : Nat.Coprime (Nat.card C) 9 := by
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three |>.mpr h3).symm.pow_right 2
  have hCtwo : IsPGroup 2 C := IsPGroup.of_card_dvd_pow (n := 8)
    (hc9.dvd_mul_right.mp (show Nat.card C ∣ 2^8 * 9 from hCcard))
  let := m22_quasisimple
  have hcomp : IsComponent D K := ⟨hsub,IsQuasisimple.of_mulEquiv e⟩
  have hCcore : pCore 2 C = ⊥ := hcomp.centralizer_pCore_eq_bot_of_pCore_eq_bot 2 hcore
  have htop : (⊤ : Subgroup C) ≤ pCore 2 C :=
    le_sSup ⟨inferInstance,hCtwo.to_subgroup ⊤⟩
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have hx1 : (⟨x,hx⟩ : C) = 1 := mem_bot.mp ((hCcore ▸ htop) (mem_top _))
  exact congrArg Subtype.val hx1

omit [Finite D] in
/-- A self-centralizing component gives a faithful action of the marked centralizer. -/
theorem m22_marked_centralizer_card_le (j : M22 →* D) (hj : Function.Injective j)
    (hcomp : IsComponent D j.range) (t : M22) (ht : orderOf t = 2)
    (hC : centralizer (j.range : Set D) = ⊥) :
    Nat.card (centralizer ({j t} : Set D)) ≤ 768 := by
  let K := j.range
  let C := centralizer ({j t} : Set D)
  let e : M22 ≃* K := MonoidHom.ofInjective hj
  have hnon : ¬ zpowers (j t) ≤ centralizer (K : Set D) := by
    intro h
    have he : j t = 1 := mem_bot.mp (hC ▸ h (mem_zpowers _))
    have ht1 : t = 1 := hj (he.trans j.map_one.symm)
    simp [ht1] at ht
  have hN : C ≤ normalizer (K : Set D) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using
      hcomp.centralizer_le_normalizer_of_noncentral (zpowers (j t))
        (zpowers_le.mpr ⟨t,rfl⟩) hnon
  let a : C →* MulAut M22 := (MulAut.congr e.symm).toMonoidHom.comp
    (K.normalizerMonoidHom.comp (inclusion hN))
  have hi : Function.Injective K.normalizerMonoidHom := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [normalizerMonoidHom_ker,hC,bot_subgroupOf]
  have ha : Function.Injective a := (MulAut.congr e.symm).injective.comp
    (hi.comp (inclusion_injective hN))
  have hfix (x : C) : a x t = t := by
    apply e.injective
    change e (e.symm (K.normalizerMonoidHom (inclusion hN x) (e t))) = e t
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (x:D) * j t * (x:D)⁻¹ = j t
    rw [mem_centralizer_singleton_iff.mp x.property,mul_inv_cancel_right]
  let f : C →* fixingSubgroup (MulAut M22) (zpowers t : Set M22) :=
    a.codRestrict _ (fun x => by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact (MulAut.mem_fixedSubgroup _ _).mp
        ((zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mpr (hfix x)) :
          zpowers t ≤ (a x).fixedSubgroup) hy))
  have hf : Function.Injective f := by
    intro x y h
    exact ha (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective f hf).trans (m22_involution_fixer_card_le t ht)


/-- The intrinsic M₂₂ obstruction, retaining only subnormality of its actual image. -/
theorem m22_subnormal_marked_centralizer_card_le (j : M22 →* D)
    (hj : Function.Injective j) (hsub : j.range.IsSubnormal)
    (hrank : primeRank 3 D ≤ 2) (hcore : pCore 2 D = ⊥)
    (t : M22) (ht : orderOf t = 2)
    (hcard : Nat.card (centralizer ({j t} : Set D)) ∣ 2304) :
    Nat.card (centralizer ({j t} : Set D)) ≤ 768 := by
  let := m22_quasisimple
  exact m22_marked_centralizer_card_le j hj
    ⟨hsub, IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hj)⟩ t ht
    (m22_component_centralizer_eq_bot j hj hsub hrank hcore t hcard)

end Sporadic.Mathieu
