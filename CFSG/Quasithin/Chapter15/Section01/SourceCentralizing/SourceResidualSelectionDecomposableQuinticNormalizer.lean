module

public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PGroup.OrderNineAutomorphismPrimes
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Quasithin.Rank

/-!
# Five-subgroups normalizing a cubic residual

Let Y be a normal two-perfect subgroup of K with Y/O₂(Y) of order three.
If K has three-rank at most two, every five-subgroup normalizing K also
normalizes Y. In K/O₂(K), the normal cubic image of Y lies in Ω₁Z(O₃).
That characteristic elementary group has order at most nine, so it admits
no nontrivial five-group action. Two-perfect containment then lifts through
O₂(K). No assumption on the five-part of an action kernel is used.

This is the ambient lifting step for the proper diagonal module in the
prime-five decomposable case of Aschbacher--Smith 15.1.14.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15
namespace DecomposableQuinticControl

private theorem normal_cubic_fixed_by_five_action
    {K P : Type*} [Group K] [Finite K] [Group P] [Finite P]
    (Y : Subgroup K) [Y.Normal] (hY : Nat.card Y = 3)
    (hr : primeRank 3 K ≤ 2) (hP : IsPGroup 5 P) (a : P →* MulAut K) :
    ∀ p : P, ∀ y : K, y ∈ Y → a p y = y := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let R := pCore 3 K
  let Z := center R
  let U := omega₁ Z (p := 3)
  let E := (U.map Z.subtype).map R.subtype
  let : U.Characteristic := omega₁_characteristic Z
  let : E.Characteristic := inferInstance
  let : IsElementaryAbelian 3 U := IsElementaryAbelian.omega₁_of_isMulCommutative Z
  let : IsElementaryAbelian 3 (U.map Z.subtype) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.map _
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by simpa using hY)
  have hYR : Y ≤ R := le_sSup ⟨inferInstance, hYp⟩
  let : Normalizes R Y := ⟨le_normalizer_of_normal⟩
  have hfix := actsTrivially_of_isPGroup_on_cyclic_prime_order
    (A := R) (G := Y) (by decide : Nat.Prime 3) pCore_isPGroup
    (isCyclic_of_prime_card hY) hY
  have hYE : Y ≤ E := by
    intro y hy
    let z : Z := ⟨⟨y, hYR hy⟩, by
      apply mem_center_iff.mpr
      intro r
      apply Subtype.ext
      have he := congrArg Subtype.val (hfix r (⟨y, hy⟩ : Y))
      change (r : K) * y * (r : K)⁻¹ = y at he
      exact mul_inv_eq_iff_eq_mul.mp he⟩
    have hz : z ∈ U := by
      apply subset_closure
      change z ^ (3 ^ 1) = 1
      apply Subtype.ext
      apply Subtype.ext
      have he := congrArg Subtype.val (pow_card_eq_one' (x := (⟨y, hy⟩ : Y)))
      simpa only [hY, pow_one, coe_pow, OneMemClass.coe_one] using he
    exact mem_map_of_mem R.subtype (mem_map_of_mem Z.subtype hz)
  have hEcard : Nat.card E ≤ 9 :=
    (primeRank_le_iff_elementary_card_le K).mp hr E inferInstance
  have hcop : Nat.Coprime 5 (Nat.card (MulAut E)) := by
    apply Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5) |>.mpr
    intro hd
    have he := prime_dvd_mulAut_card_le_nine
      (IsElementaryAbelian.isPGroup 3 E) hEcard (by decide : Nat.Prime 5) hd
    omega
  let b := (MulAut.characteristic E).comp a
  have hb : b = 1 := by
    apply MonoidHom.ext
    intro p
    obtain ⟨n, hn⟩ := hP p
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (hcop.pow_left n)
    · exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hn, map_one])
    · exact orderOf_dvd_natCard (b p)
  intro p y hy
  have he := DFunLike.congr_fun (DFunLike.congr_fun hb p) (⟨y, hYE hy⟩ : E)
  exact congrArg Subtype.val he

private theorem normal_cubic_residual_stable_by_five_action
    {K P : Type*} [Group K] [Finite K] [Group P] [Finite P]
    (Y : Subgroup K) [Y.Normal] (hpY : IsPPerfect 2 Y)
    (hY : Nat.card (Y ⧸ pCore 2 Y) = 3) (hr : primeRank 3 K ≤ 2)
    (hP : IsPGroup 5 P) (a : P →* MulAut K) (p : P) :
    Y.map (a p).toMonoidHom ≤ Y := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := Y.map q
  let : B.Normal := (inferInstance : Y.Normal).map q (QuotientGroup.mk'_surjective _)
  have hB : Nat.card B = 3 :=
    (Nat.card_congr ((inferInstance : Y.Normal).isSubnormal.quotientCoreImageEquiv 2).toEquiv).symm.trans hY
  let b := (quotientAut (pCore 2 K)).comp a
  have hfix := normal_cubic_fixed_by_five_action B hB
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup).trans hr)
    hP b
  apply isPPerfect_le_of_map_le_of_kernel_normalizes q _ Y
    (hpY.of_surjective ((a p).toMonoidHom.subgroupMap Y)
      ((a p).toMonoidHom.subgroupMap_surjective Y))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) le_normalizer_of_normal
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have he := hfix p (q y) (mem_map_of_mem q hy)
  change quotientAut (pCore 2 K) (a p) (q y) = q y at he
  rw [quotientAut_apply_mk] at he
  exact he ▸ mem_map_of_mem q hy

/-- A five-subgroup normalizing a group of three-rank at most two also
normalizes each normal two-perfect subgroup with cubic two-core quotient. -/
public theorem five_normalizes_cubic_residual
    {G : Type*} [Group G] [Finite G] (P K Y : Subgroup G)
    (hYK : Y ≤ K) (hn : K ≤ normalizer (Y : Set G))
    (hpY : IsPPerfect 2 Y) (hY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hr : primeRank 3 K ≤ 2) (hP : IsPGroup 5 P)
    (hPK : P ≤ normalizer (K : Set G)) : P ≤ normalizer (Y : Set G) := by
  let YK := Y.subgroupOf K
  let : YK.Normal := (normal_subgroupOf_iff_le_normalizer hYK).mpr hn
  let e := subgroupOfEquivOfLe hYK
  have hpYK : IsPPerfect 2 YK := hpY.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcYK : Nat.card (YK ⧸ pCore 2 YK) = 3 := by
    let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    exact (Nat.card_congr eQ.toEquiv).trans hY
  let a : P →* MulAut K := K.normalizerMonoidHom.comp (inclusion hPK)
  apply le_normalizer_iff.mpr
  intro p hp y hy
  have h := normal_cubic_residual_stable_by_five_action YK hpYK hcYK hr hP a ⟨p, hp⟩
  exact h (mem_map_of_mem (a ⟨p, hp⟩).toMonoidHom (show (⟨y, hYK hy⟩ : K) ∈ YK from hy))

end DecomposableQuinticControl
end CFSG.Quasithin.Chapter15
