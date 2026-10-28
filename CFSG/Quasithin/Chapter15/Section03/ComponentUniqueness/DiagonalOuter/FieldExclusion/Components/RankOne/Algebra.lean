module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.RankOne.Automorphisms
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.GroupAction.Invariant

/-!
# The group-theoretic part of the extraspecial rank obstruction

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137; compare the component permutation argument A.3.8,
p.45, and cyclic Sylow transfer I.1.2, p.407.

A perfect group of three-rank one has cyclic Sylow three-subgroups, and
transfer makes its center prime to three. Three distinct such components
would supply independent commuting elements of order three. An element of
order dividing three therefore cannot move one of these components in an
ambient group of three-rank at most two. This proves normalization directly,
without assuming component normality or the hypotheses of A.3.8.

For a normalized component J, an abelian image of the extraspecial group B
centralizes J through B's derived subgroup Z(B). A nontrivial normal subgroup
B intersect J would meet Z(B), contradicting the three-prime center of J.
The three-group fixed-point congruence supplies an element of order three in
J centralized by B. Its product with an elementary nine in B is the actual
elementary subgroup of order 27. The central-quotient automorphism property
is the sole remaining model input in the final conditional theorem.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
universe u
variable {H : Type u} [Group H] [Finite H]

/-- Transfer makes the center of a perfect three-rank-one group prime to three. -/
theorem center_prime_free [Group.IsPerfect H] (hr : primeRank 3 H ≤ 1) :
    ¬ 3 ∣ Nat.card (center H) := by
  let q := QuotientGroup.mk' (center H)
  let P : Sylow 3 H := Classical.choice inferInstance
  have hP := P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  have hq := P.primeRank_quotient_le_one hP (center H)
  simpa only [q, QuotientGroup.ker_mk'] using
    PerfectCentralCovering.not_dvd_card_kernel_of_isCyclic_sylow
      q (QuotientGroup.mk'_surjective _) (by simp [q])
      (fun Q => Q.isCyclic_of_odd_of_primeRank_le_one (by decide) hq)

/-- The actual central quotient of a perfect three-rank-one group still has three-rank one. -/
theorem central_quotient_rank_one [Group.IsPerfect H] (hr : primeRank 3 H = 1) :
    primeRank 3 (H ⧸ center H) = 1 := by
  let P : Sylow 3 H := Classical.choice inferInstance
  have hle := P.primeRank_quotient_le_one
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr.le) (center H)
  have hd : 3 ∣ Nat.card H := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  rw [(center H).card_eq_card_quotient_mul_card_subgroup] at hd
  have hq : 3 ∣ Nat.card (H ⧸ center H) :=
    ((Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp hd).resolve_right (center_prime_free hr.le)
  have hn : primeRank 3 (H ⧸ center H) ≠ 0 :=
    fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hq
  omega

omit [Finite H] in
private theorem prime_element_not_central {J : Subgroup H}
    (hZ : ¬ 3 ∣ Nat.card (center J)) {x : H} (hx : x ∈ J) (ho : orderOf x = 3) :
    x ∉ centralizer (J : Set H) := by
  intro hc
  let z : center J := ⟨⟨x, hx⟩, mem_center_iff.mpr
    (fun j => Subtype.ext (hc j j.property))⟩
  have hz : orderOf z = 3 := by
    exact (orderOf_injective (J.subtype.comp (center J).subtype)
      (J.subtype_injective.comp (center J).subtype_injective) z).symm.trans ho
  exact hZ (hz ▸ orderOf_dvd_natCard z)

private theorem extraspecial_derived [IsExtraspecial 3 H] : _root_.commutator H = center H := by
  let := IsExtraspecial.quotient_elementary_abelian 3 H
  have hl : _root_.commutator H ≤ center H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hd : Nat.card (_root_.commutator H) ∣ 3 :=
    (card_dvd_of_le hl).trans (IsExtraspecial.center_order_p 3 H ▸ dvd_rfl)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · have hb := card_eq_one.mp h
    let : Nontrivial (H ⧸ center H) := IsExtraspecial.quotient_nontrivial 3 H
    exact (QuotientGroup.nontrivial_iff.mp inferInstance
      ((commutator_eq_bot_iff_center_eq_top H).mp hb)).elim
  · exact eq_of_le_of_card_ge hl (by rw [h, IsExtraspecial.center_order_p 3 H])

private theorem extraspecial_nine [IsExtraspecial 3 H]
    (hc : Nat.card H = 27) :
    ∃ E : Subgroup H, IsElementaryAbelian 3 E ∧ Nat.card E = 9 := by
  have hn : ¬ IsCyclic H := by
    intro hn
    let := hn
    have hZ : center H = ⊤ := center_eq_top_iff.mpr inferInstance
    have hz := IsExtraspecial.center_order_p 3 H
    rw [hZ, Nat.card_congr Subgroup.topEquiv.toEquiv, hc] at hz
    omega
  obtain ⟨E, _, hcard, hE⟩ :=
    (IsExtraspecial.isPGroup 3 H).exists_normal_elementary_prime_sq_of_odd_not_isCyclic
      (by decide) hn
  exact ⟨E, hE, hcard⟩

private theorem three_components_rank
    (J K L : Subgroup H) (hJ : IsComponent H J) (hK : IsComponent H K)
    (hL : IsComponent H L) (hJK : J ≠ K) (hJL : J ≠ L) (hKL : K ≠ L)
    (hJr : primeRank 3 J = 1) (hKr : primeRank 3 K = 1) (hLr : primeRank 3 L = 1) :
    3 ≤ primeRank 3 H := by
  let := hJ.2
  let := hK.2
  let := hL.2
  have hj3 : 3 ∣ Nat.card J := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  have hk3 : 3 ∣ Nat.card K := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  have hl3 : 3 ∣ Nat.card L := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hj3
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 hk3
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hl3
  have hxH : orderOf (x : H) = 3 := (orderOf_injective J.subtype J.subtype_injective x).trans hx
  have hyH : orderOf (y : H) = 3 := (orderOf_injective K.subtype K.subtype_injective y).trans hy
  have hzH : orderOf (z : H) = 3 := (orderOf_injective L.subtype L.subtype_injective z).trans hz
  have hJKc := commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hK hJK)
  have hJLc := commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne hL hJL)
  have hKLc := commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne hL hKL)
  let X := zpowers (x : H)
  have hXJ : X ≤ J := zpowers_le.mpr x.property
  have hyX : (y : H) ∉ X := fun hyX =>
    prime_element_not_central (center_prime_free hKr.le) y.property hyH (hJKc (hXJ hyX))
  let : IsElementaryAbelian 3 X :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hxH ▸ pow_orderOf_eq_one (x : H))
  have hXfix : X ≤ centralizer ({(y : H)} : Set H) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((hJKc (hXJ ha)) y y.property).symm
  obtain ⟨hE, hEc⟩ := IsElementaryAbelian.fixed_join_card X y hyH
    (Subgroup.disjoint_zpowers_of_prime_order_not_mem X y hyH hyX) hXfix
    (show Nat.card X = 3 ^ 1 by simpa only [X, Nat.card_zpowers, pow_one] using hxH)
  let E := X ⊔ zpowers (y : H)
  let : IsElementaryAbelian 3 E := hE
  have hEL : E ≤ centralizer (L : Set H) :=
    sup_le (hXJ.trans hJLc) ((zpowers_le.mpr y.property).trans hKLc)
  have hzE : (z : H) ∉ E := fun hzE =>
    prime_element_not_central (center_prime_free hLr.le) z.property hzH (hEL hzE)
  have hEfix : E ≤ centralizer ({(z : H)} : Set H) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((hEL ha) z z.property).symm
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join E z hzH hzE hEfix hEc

open scoped Pointwise in
/-- Every exponent-three subgroup normalizes a three-rank-one component in a group of three-rank at most two. No ambient normality is assumed. -/
theorem component_normalized (B J : Subgroup H)
    (hB : ∀ b : B, b ^ 3 = 1) (hJ : IsComponent H J)
    (hr : primeRank 3 J = 1) (hH : primeRank 3 H ≤ 2) :
    B ≤ normalizer (J : Set H) := by
  intro b hb
  let a := MulAut.conj b
  have ha : a ^ 3 = 1 := by
    dsimp [a]
    rw [← map_pow, show b ^ 3 = 1 from congrArg Subtype.val (hB ⟨b, hb⟩), map_one]
  have hcycle (D : Subgroup H) : a • (a • (a • D)) = D := by
    rw [← mul_smul, ← mul_smul]
    have he : a * (a * a) = 1 := by simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ha
    rw [mul_assoc, he, one_smul]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change a • J = J
  by_contra hn
  have h02 : J ≠ a • (a • J) := by
    intro he
    have hh := congrArg (a • ·) he
    rw [hcycle] at hh
    exact hn hh
  have h12 : a • J ≠ a • (a • J) := by
    intro he
    have hh := congrArg (a⁻¹ • ·) he
    simp only [inv_smul_smul] at hh
    exact hn hh.symm
  have hJ1 : IsComponent H (a • J) := hJ.map_equiv a
  have hJ2 : IsComponent H (a • (a • J)) := hJ1.map_equiv a
  have hr1 : primeRank 3 (a • J : Subgroup H) = 1 :=
    (primeRank_equiv 3 (J.equivMapOfInjective a.toMonoidHom a.injective)).symm.trans hr
  have hr2 : primeRank 3 (a • (a • J) : Subgroup H) = 1 :=
    (primeRank_equiv 3 ((a • J).equivMapOfInjective a.toMonoidHom a.injective)).symm.trans hr1
  have hl := three_components_rank J (a • J) (a • (a • J)) hJ hJ1 hJ2
    (Ne.symm hn) h02 h12 hr hr1 hr2
  omega

private theorem fixed_three (B J : Subgroup H) (hBp : IsPGroup 3 B)
    (hn : B ≤ normalizer (J : Set H)) (hd : 3 ∣ Nat.card J) :
    ∃ x : H, x ∈ J ∧ orderOf x = 3 ∧ x ∈ centralizer (B : Set H) := by
  let i := Subgroup.inclusion hn
  let : MulDistribMulAction B J := MulDistribMulAction.compHom J i
  let C := FixedPoints.subgroup B J
  have hc : 3 ∣ Nat.card C := Nat.modEq_zero_iff_dvd.mp
    ((hBp.card_modEq_card_fixedPoints J).symm.trans hd.modEq_zero_nat)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hc
  refine ⟨((x : C) : J), (x : J).property, ?_, ?_⟩
  · exact (orderOf_injective (J.subtype.comp C.subtype)
      (J.subtype_injective.comp C.subtype_injective) x).trans hx
  · intro b hb
    have hf : (⟨b, hb⟩ : B) • (x : J) = (x : J) := x.property _
    have hf' : b * ((x : J) : H) * b⁻¹ = (x : J) := congrArg Subtype.val hf
    exact mul_inv_eq_iff_eq_mul.mp hf'

private theorem disjoint_of_abelian_action (B J : Subgroup H) [IsExtraspecial 3 B]
    (he : ∀ b : B, b ^ 3 = 1) (hn : B ≤ normalizer (J : Set H))
    (hZ : ¬ 3 ∣ Nat.card (center J))
    (hab : IsMulCommutative (J.normalizerMonoidHom.comp (inclusion hn)).range) :
    Disjoint B J := by
  let ρ := J.normalizerMonoidHom.comp (inclusion hn)
  let : IsMulCommutative ρ.range := hab
  let : CommGroup ρ.range := IsMulCommutative.instCommGroup
  have hZker : center B ≤ ρ.ker := by
    rw [← extraspecial_derived]
    intro x hx
    have hh := Abelianization.commutator_subset_ker ρ.rangeRestrict hx
    exact congrArg Subtype.val hh
  let D := J.subgroupOf B
  let : D.Normal := normal_subgroupOf_of_le_normalizer hn
  suffices hd : D = ⊥ by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hxD : (⟨x, hx.1⟩ : B) ∈ D := hx.2
    rw [hd, mem_bot] at hxD
    exact congrArg Subtype.val hxD
  by_contra hd
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hd
  let : Fact (IsPGroup 3 B) := ⟨IsExtraspecial.isPGroup 3 B⟩
  obtain ⟨x, hxne, hxZ⟩ := exists_nontrivial_center_mem_normal D (p := 3)
  have hx1 : (x : B) ≠ 1 := fun hh => hxne (Subtype.ext hh)
  have hx3 : orderOf (x : B) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      (orderOf_dvd_of_pow_eq_one (he x)) with h | h
    · exact (hx1 (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hxH : orderOf ((x : B) : H) = 3 :=
    (orderOf_injective B.subtype B.subtype_injective (x : B)).trans hx3
  have hxker : ρ (x : B) = 1 := hZker hxZ
  apply prime_element_not_central hZ (show ((x : B) : H) ∈ J from x.property) hxH
  intro j hj
  have hh := congrArg (fun a : MulAut J => a ⟨j, hj⟩) hxker
  have hh' : ((x : B) : H) * j * ((x : B) : H)⁻¹ = j := congrArg Subtype.val hh
  exact (mul_inv_eq_iff_eq_mul.mp hh').symm

/-- An abelian conjugation image supplies an actual elementary subgroup of order 27. The center and divisibility assumptions concern the normalized subgroup J. -/
theorem elementary_twentyseven_of_action (B J : Subgroup H) [IsExtraspecial 3 B]
    (hc : Nat.card B = 27) (he : ∀ b : B, b ^ 3 = 1)
    (hn : B ≤ normalizer (J : Set H)) (hZ : ¬ 3 ∣ Nat.card (center J))
    (hd : 3 ∣ Nat.card J)
    (hab : IsMulCommutative (J.normalizerMonoidHom.comp (inclusion hn)).range) :
    ∃ E : Subgroup H, IsElementaryAbelian 3 E ∧ Nat.card E = 27 := by
  have hdis := disjoint_of_abelian_action B J he hn hZ hab
  obtain ⟨x, hxJ, hx3, hxf⟩ := fixed_three B J (IsExtraspecial.isPGroup 3 B) hn hd
  have hxB : x ∉ B := by
    intro hx
    have hh := disjoint_iff.mp hdis
    have hx1 : x = 1 := mem_bot.mp (hh ▸ (show x ∈ B ⊓ J from ⟨hx, hxJ⟩))
    simp only [hx1, orderOf_one] at hx3
    omega
  obtain ⟨A, hA, hAc⟩ := extraspecial_nine (H := B) hc
  let := hA
  let E := A.map B.subtype
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map _
  have hEc : Nat.card E = 3 ^ 2 := by
    rw [show Nat.card E = Nat.card A from card_map_of_injective B.subtype_injective, hAc]
    decide
  have hfix : E ≤ centralizer ({x} : Set H) := by
    intro e heE
    exact mem_centralizer_singleton_iff.mpr (hxf e (map_subtype_le A heE))
  obtain ⟨hF, hFc⟩ := IsElementaryAbelian.fixed_join_card E x hx3
    (Subgroup.disjoint_zpowers_of_prime_order_not_mem E x hx3 (fun hx => hxB (map_subtype_le A hx)))
    hfix hEc
  exact ⟨E ⊔ zpowers x, hF, hFc⟩

omit [Finite H] in
private theorem abelian_action_of_cubic (B J : Subgroup H)
    (he : ∀ b : B, b ^ 3 = 1) (hn : B ≤ normalizer (J : Set H))
    (ha : CubicAutomorphismsAbelian J) :
    IsMulCommutative (J.normalizerMonoidHom.comp (inclusion hn)).range := by
  let ρ := J.normalizerMonoidHom.comp (inclusion hn)
  apply ha ρ.range
  rintro ⟨a, b, rfl⟩
  apply Subtype.ext
  exact (map_pow ρ b 3).symm.trans ((congrArg ρ (he b)).trans ρ.map_one)

/-- Conditional rank exclusion from the intrinsic automorphism property of the simple central quotient. The property remains a model proof obligation. -/
theorem rank_one_excluded_of_cubic (B J : Subgroup H) [IsExtraspecial 3 B]
    (hc : Nat.card B = 27) (he : ∀ b : B, b ^ 3 = 1)
    (hJ : IsComponent H J) (hH : primeRank 3 H ≤ 2)
    (ha : CubicAutomorphismsAbelian (J ⧸ center J)) : primeRank 3 J ≠ 1 := by
  intro hr
  let := hJ.2
  have hn := component_normalized B J he hJ hr hH
  have hJ3 : 3 ∣ Nat.card J := by
    by_contra hd
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega
  obtain ⟨E, hE, hEc⟩ := elementary_twentyseven_of_action B J hc he hn
    (center_prime_free hr.le) hJ3
    (abelian_action_of_cubic B J he hn (cubic_of_central_quotient ha))
  let := hE
  have hl : 3 ≤ primeRank 3 H := IsElementaryAbelian.primeRank_ge_of_card E hEc
  omega


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
