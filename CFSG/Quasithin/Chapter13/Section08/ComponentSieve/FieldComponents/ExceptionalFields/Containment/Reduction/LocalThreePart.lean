module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PrimeSection
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# The local three-part step in the exceptional noncontainment argument

The identities B L₁ = B_C L₁ and B_C = O³(B) or O³(B)L₀ reduce
B L₁ to O³(B)L₁. When O³(B) has three-prime order, its image modulo
the normal subgroup L₁ has three-prime order too. Consequently the
three-generated residual O^{3′}(B) lies in L₁.

Its three-part equals that of B. If it carries the whole three-part
of L₁/O₂(L₁), its image fills that quotient. Relative normality and
two-perfectness then put all of L₁ in B. Thus noncontainment forces
the ordinary order-three case to fail and gives |B|₃ = 3 in the
order-nine case. The intrinsic exceptional Borel order calculations
are separate obligations; no reduction conclusion is assumed here.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955;
Notation 13.2.1 and 13.7.3(9) supply the earlier local data.
-/

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
variable {G : Type*} [Group G] [Finite G]

private theorem val_two_kernel {A C : Type*} [Group A] [Group C]
    [Finite A] [Finite C] (f : A →* C) (hk : IsPGroup 2 f.ker) :
    (Nat.card A).factorization 3 = (Nat.card f.range).factorization 3 := by
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  rw [← f.ker.card_mul_index, index_ker, hn,
    Nat.factorization_mul (pow_ne_zero n (by decide)) Nat.card_pos.ne']
  simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]

omit [Finite G] in
public theorem threeGenerated_le_of_join (B L₁ : Subgroup G)
    (hn : B ⊔ L₁ ≤ normalizer (L₁ : Set G))
    (hj : B ⊔ L₁ = residualIn 3 B ⊔ L₁)
    (hr : Nat.Coprime 3 (Nat.card (residualIn 3 B))) :
    (primeToResidual 3 B).map B.subtype ≤ L₁ := by
  let J := B ⊔ L₁
  let N := L₁.subgroupOf J
  let R := (residualIn 3 B).subgroupOf J
  have hLJ : L₁ ≤ J := le_sup_right
  have hRJ : residualIn 3 B ≤ J := (map_subtype_le _).trans le_sup_left
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hsup : R ⊔ N = ⊤ := by
    rw [← subgroupOf_sup hRJ hLJ, ← hj, subgroupOf_self]
  have hcR : Nat.Coprime 3 (Nat.card R) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hRJ).toEquiv]
  have hcN : Nat.Coprime 3 N.index := by
    rw [← relIndex_top_right, ← hsup, relIndex_sup_right]
    exact hcR.of_dvd_right (relIndex_dvd_card _ _)
  let f : B →* J := inclusion le_sup_left
  have hc : Nat.Coprime 3 (N.comap f).index := by
    rw [index_comap]
    exact hcN.of_dvd_right (relIndex_dvd_index_of_normal _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact primeToResidual_le (N.comap f) hc hx

public theorem threeGenerated_three_valuation (B : Subgroup G) :
    (Nat.card B).factorization 3 =
      (Nat.card ((primeToResidual 3 B).map B.subtype)).factorization 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := primeToResidual_index_coprime (G := B) 3
  rw [card_map_of_injective B.subtype_injective]
  rw [← (primeToResidual 3 B).card_mul_index,
    Nat.factorization_mul Nat.card_pos.ne' (index_ne_zero_of_finite)]
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (Nat.prime_three.coprime_iff_not_dvd.mp hc),
    add_zero]

private theorem seed_le_of_full_three_part (L₁ Y : Subgroup G) (hY : Y ≤ L₁)
    (hn : L₁ ≤ normalizer (Y : Set G)) (hp : IsPPerfect 2 L₁)
    (n : ℕ) (hq : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ^ n)
    (hv : n ≤ (Nat.card Y).factorization 3) : L₁ ≤ Y := by
  let N := Y.subgroupOf L₁
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let q := QuotientGroup.mk' (pCore 2 L₁)
  let f := q.comp (inclusion hY)
  have hk : IsPGroup 2 f.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hY)
  have hv' : n ≤ (Nat.card f.range).factorization 3 := by
    rwa [← val_two_kernel f hk]
  have hdiv : 3 ^ n ∣ Nat.card f.range :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr hv'
  have hrange : f.range = ⊤ := eq_top_of_card_eq _ (by
    apply Nat.dvd_antisymm
    · exact f.range.card_subgroup_dvd_card
    · rwa [hq])
  have hmap : N.map q = ⊤ := by
    have hf : (inclusion hY).range = N := inclusion_range hY
    rw [← hf, ← MonoidHom.range_comp]
    exact hrange
  have hsup : N ⊔ pCore 2 L₁ = ⊤ := by
    have h := congrArg (Subgroup.comap q) hmap
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using h
  have htop := hp N inferInstance (isPGroup_quotient_of_sup_eq_top N (pCore 2 L₁)
    pCore_isPGroup hsup)
  intro x hx
  exact (show (⟨x, hx⟩ : L₁) ∈ N from htop ▸ trivial)

omit [Finite G] in
/-- The theta subgroup is normal in its defining local overgroup. -/
public theorem theta_normalized (J L₁ : Subgroup G)
    (htheta : L₁ = closure {x : G | x ∈ J ∧ orderOf x = 3}) :
    J ≤ normalizer (L₁ : Set G) := by
  rw [htheta]
  apply le_normalizer_closure_iff.mpr
  intro g hg x hx
  apply subset_closure
  refine ⟨J.mul_mem (J.mul_mem hg hx.1) (J.inv_mem hg), ?_⟩
  exact ((MulAut.conj g).orderOf_eq x).trans hx.2

omit [Finite G] in
/-- The two printed centralizer identities give the required join, in both
ordinary and covered cases. B_C remains the literal two-residual. -/
public theorem borel_join_threeResidual (B L₁ L L₀ : Subgroup G) (hL₀ : L₀ ≤ L₁)
    (hprod : B ⊔ L₁ = centralizingResidual B L₁ L ⊔ L₁)
    (hBC : centralizingResidual B L₁ L = residualIn 3 B ∨
      centralizingResidual B L₁ L = residualIn 3 B ⊔ L₀) :
    B ⊔ L₁ = residualIn 3 B ⊔ L₁ := by
  rcases hBC with h | h
  · rw [hprod, h]
  · rw [hprod, h, sup_assoc, sup_eq_right.mpr hL₀]

omit [Finite G] in
/-- Establish the genuine source containment O^{3′}(B) ≤ L₁, from theta
and the B_C identities, without identifying O³ and O^{3′}. -/
public theorem threeGenerated_le_seed (B L₁ L L₀ : Subgroup G) (hL₀ : L₀ ≤ L₁)
    (htheta : L₁ = closure {x : G | x ∈ B ⊔ L₁ ∧ orderOf x = 3})
    (hprod : B ⊔ L₁ = centralizingResidual B L₁ L ⊔ L₁)
    (hBC : centralizingResidual B L₁ L = residualIn 3 B ∨
      centralizingResidual B L₁ L = residualIn 3 B ⊔ L₀)
    (hr : Nat.Coprime 3 (Nat.card (residualIn 3 B))) :
    (primeToResidual 3 B).map B.subtype ≤ L₁ :=
  threeGenerated_le_of_join B L₁ (theta_normalized _ _ htheta)
    (borel_join_threeResidual B L₁ L L₀ hL₀ hprod hBC) hr

/-- Three-divisibility makes the three-generated residual nontrivial. -/
public theorem threeGenerated_ne_bot (B : Subgroup G) (h3 : 3 ∣ Nat.card B) :
    (primeToResidual 3 B).map B.subtype ≠ ⊥ := by
  have hval : 1 ≤ (Nat.card B).factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp h3
  rw [threeGenerated_three_valuation B] at hval
  intro h
  simp only [h, card_bot, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply] at hval
  omega

/-- A proper, relatively normal three-generated subgroup cannot carry the
whole three-part of a two-perfect seed with elementary three quotient. -/
public theorem borel_three_valuation_lt_of_outside
    (B K L₁ : Subgroup G) (hBK : B ≤ K) (hout : ¬ L₁ ≤ K)
    (hY : (primeToResidual 3 B).map B.subtype ≤ L₁)
    (hL₁B : L₁ ≤ normalizer (B : Set G)) (hp : IsPPerfect 2 L₁)
    (n : ℕ) (hq : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ^ n) :
    (Nat.card B).factorization 3 < n := by
  by_contra! hv
  let Y := (primeToResidual 3 B).map B.subtype
  have hn : L₁ ≤ normalizer (Y : Set G) := hL₁B.trans
    (normalizer_le_normalizer_characteristic_image B (primeToResidual 3 B))
  have hvY : n ≤ (Nat.card Y).factorization 3 := by
    rwa [← threeGenerated_three_valuation B]
  exact hout ((seed_le_of_full_three_part L₁ Y hY hn hp n hq hvY).trans
    ((map_subtype_le _).trans hBK))

/-- The ordinary local quotient is excluded, and the remaining three-part
is exactly three. The two quotient orders are the genuine earlier local
alternatives, not a hypothesis containing this reduction. -/
public theorem noncontainment_three_part
    (B K L₁ : Subgroup G) (hBK : B ≤ K) (hout : ¬ L₁ ≤ K)
    (hY : (primeToResidual 3 B).map B.subtype ≤ L₁)
    (hL₁B : L₁ ≤ normalizer (B : Set G)) (hp : IsPPerfect 2 L₁)
    (h3 : 3 ∣ Nat.card B)
    (hlocal : Nat.card (L₁ ⧸ pCore 2 L₁) = 3 ∨
      Nat.card (L₁ ⧸ pCore 2 L₁) = 9) :
    Nat.card (L₁ ⧸ pCore 2 L₁) = 9 ∧ 3 ^ (Nat.card B).factorization 3 = 3 := by
  have hlo := (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp h3
  rcases hlocal with h | h
  · have hlt := borel_three_valuation_lt_of_outside B K L₁ hBK hout hY hL₁B hp 1
      (by simpa only [pow_one] using h)
    omega
  · have hlt := borel_three_valuation_lt_of_outside B K L₁ hBK hout hY hL₁B hp 2 h
    have he : (Nat.card B).factorization 3 = 1 := by omega
    exact ⟨h, by rw [he, pow_one]⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
