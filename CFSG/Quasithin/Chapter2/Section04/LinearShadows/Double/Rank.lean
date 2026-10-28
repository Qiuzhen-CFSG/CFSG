module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank.MatrixWitnesses
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.CoprimeRank
public import CFSG.Quasithin.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Quasithin.LocalRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The odd-rank obstruction in the two-block linear shadow

The final step on printed p.541 requires odd prime rank two in the actual PSL₃
section. The diagonal torus gives this when the prime is different from three;
at three the diagonal and coordinate three-cycle commute only projectively.
A coprime two-core quotient preserves odd prime rank. The disjoint centralizing
factor then supplies the third rank in the literal join K ∨ D₁.

Source: Aschbacher–Smith, §2.4, printed pp.540–541. This module proves the
rank obstruction; construction and recognition of its section remain separate.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix Theory.SpecificGroups.SignedThreeCubicRank
namespace CFSG.Quasithin.Chapter2.LinearDouble

variable {F : Type*} [Field F] [Finite F]

/-- Every prime divisor of the multiplicative field order gives rank two in PSL₃. -/
theorem psl_three_prime_rank {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card F - 1) : 2 ≤ primeRank p PSL(3,F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by simpa only [Nat.card_units] using hd)
  by_cases hp3 : p = 3
  · rcases hp3 with rfl
    have hu3 : (u : F) ^ 3 = 1 := congrArg Units.val (hu ▸ pow_orderOf_eq_one u)
    have hune : (u : F) ≠ 1 := by
      intro he
      have hone : u = 1 := Units.ext he
      simp [hone] at hu
    exact projective_rank (u : F) hu3 hune
      ProjectiveSpecialLinearGroup.toPGL ProjectiveSpecialLinearGroup.toPGL_injective
      (QuotientGroup.mk (diagonal (u : F) hu3))
      (QuotientGroup.mk (cycle (F := F))) rfl rfl
  · have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
    have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
    have hpow (a : rootsOfUnity p F) : a ^ p = 1 :=
      Subtype.ext ((mem_rootsOfUnity p a.val).mp a.property)
    have hcop : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr
      (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
    let f : (rootsOfUnity p F × rootsOfUnity p F) →* PSL(3,F) :=
      (PSL3.CartanActions.torusMap F).comp
        ((rootsOfUnity p F).subtype.prodMap (rootsOfUnity p F).subtype)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a,b⟩ hab
      have h := (PSL3.CartanActions.BorelQuotient.torusMap_eq_one_iff F
        ((a : Fˣ), (b : Fˣ))).mp hab
      have ha3 : a ^ 3 = 1 := Subtype.ext h.2
      have ha : a = 1 := by
        apply orderOf_eq_one_iff.mp
        apply Nat.dvd_one.mp
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hpow a))
          (orderOf_dvd_of_pow_eq_one ha3)
      exact Prod.ext ha ((Subtype.ext h.1).symm.trans ha)
    exact primeRank_ge_of_elementary_embedding
      (fun a => Prod.ext (hpow a.1) (hpow a.2))
      (by rw [Nat.card_prod, hc, pow_two]) f hf

variable {G : Type*} [Group G] [Finite G]

/-- The literal two-core quotient and an independent centralizing factor give rank three. -/
theorem rank_three_of_linear_section (K D : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,F))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card F - 1)
    (hdD : p ∣ Nat.card D) (hdis : Disjoint K D)
    (hcomm : K ≤ centralizer (D : Set G)) :
    3 ≤ primeRank p (K ⊔ D : Subgroup G) := by
  let : Fact p.Prime := ⟨hp⟩
  have hK : 2 ≤ primeRank p K := by
    have h := psl_three_prime_rank (F := F) hp hd
    rw [← Theory.GroupTheory.primeRank_equiv p e,
      primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup] at h
    exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := D) p hdD
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  have hD : 1 ≤ primeRank p D := IsElementaryAbelian.primeRank_ge_of_card (zpowers x)
    (by simp only [Nat.card_zpowers, hx, pow_one])
  rw [primeRank_sup_eq_add_of_disjoint_commuting K D hdis hcomm p]
  omega

/-- The constructed rank contradicts strong quasithinness of the actual product. -/
theorem false_of_linear_section (K D : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* PSL(3,F))
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card F - 1)
    (hdD : p ∣ Nat.card D) (hdis : Disjoint K D)
    (hcomm : K ≤ centralizer (D : Set G))
    (hSQ : IsStronglyQuasithin (K ⊔ D : Subgroup G)) : False := by
  have hl := rank_three_of_linear_section K D e hp ho hd hdD hdis hcomm
  have hu := hSQ p hp ho
  omega

/-- Source p.541 for the actual K = ⟨L₂,L₂ˣ⟩. Faithfulness proves disjointness,
and the actual normalizer of R₁ supplies the odd-rank bound. The model
identification remains the preceding component-recognition obligation. -/
theorem false_of_conjugate_generated_linear_section [CharP F 2] (R D L : Subgroup G) (x : G)
    (hG : IsQuasithin G) (hR : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hDN : D ≤ normalizer (R : Set G))
    (hfaith : Function.Injective (R.normalizerMonoidHom.comp (inclusion hDN)))
    (hL : L ≤ centralizer ((R ⊔ D : Subgroup G) : Set G))
    (hxR : x ∈ normalizer (R : Set G)) (hxD : x ∈ normalizer (D : Set G))
    (hcard : Nat.card D = Nat.card F - 1) (hF : 2 < Nat.card F)
    (e : ((L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) ⧸
      pCore 2 (L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G)) ≃* PSL(3,F)) :
    False := by
  let K := L ⊔ L.map (MulAut.conj x⁻¹).toMonoidHom
  have hx : x ∈ normalizer ((R ⊔ D : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq] at hxR hxD ⊢
    change R.map (MulAut.conj x).toMonoidHom = R at hxR
    change D.map (MulAut.conj x).toMonoidHom = D at hxD
    change (R ⊔ D).map (MulAut.conj x).toMonoidHom = _
    rw [Subgroup.map_sup, hxR, hxD]
  have hK : K ≤ centralizer ((R ⊔ D : Subgroup G) : Set G) := by
    apply sup_le hL
    have hi := normalizer_le_normalizer_centralizer (R ⊔ D) hx
    have hii := (normalizer ((centralizer ((R ⊔ D : Subgroup G) : Set G)) : Set G)).inv_mem hi
    have hm := mem_normalizer_iff_map_conj_eq.mp hii
    exact (map_mono hL).trans hm.le
  have hKD : K ≤ centralizer (D : Set G) := hK.trans (centralizer_le (show (D : Set G) ⊆ (R ⊔ D : Subgroup G) from fun _ hd => (le_sup_right : D ≤ R ⊔ D) hd))
  have hKR : K ≤ centralizer (R : Set G) := hK.trans (centralizer_le (show (R : Set G) ⊆ (R ⊔ D : Subgroup G) from fun _ hr => (le_sup_left : R ≤ R ⊔ D) hr))
  have hd : Disjoint K D := by
    apply disjoint_def.mpr
    intro d hdK hdD
    have hk : (⟨d, hDN hdD⟩ : normalizer (R : Set G)) ∈ R.normalizerMonoidHom.ker := by
      rw [normalizerMonoidHom_ker]
      exact hKR hdK
    have he : R.normalizerMonoidHom.comp (inclusion hDN) ⟨d,hdD⟩ = 1 := hk
    exact congrArg Subtype.val (hfaith (he.trans (map_one _).symm))
  obtain ⟨p, hp, hpF⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  have ho : Odd p := by
    apply hp.odd_of_ne_two
    intro he
    subst p
    let : Fintype F := Fintype.ofFinite F
    have htwo : 2 ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card, Nat.dvd_iff_mod_eq_zero]
      exact FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
    have hdiv := Nat.dvd_sub htwo hpF
    have hpos := Nat.card_pos (α := F)
    have hsub : Nat.card F - (Nat.card F - 1) = 1 := by omega
    rw [hsub] at hdiv
    omega
  have hlow := rank_three_of_linear_section K D e hp ho hpF (hcard ▸ hpF) hd hKD
  have hloc : IsTwoLocal (normalizer (R : Set G)) := ⟨R,hne,hR,rfl⟩
  have hbound := CFSG.Quasithin.isQuasithin_iff_twoLocal.mp hG
    (normalizer (R : Set G)) hloc p hp ho
  have hle := primeRank_mono p (sup_le (hKR.trans (centralizer_le_normalizer _)) hDN)
  omega

end CFSG.Quasithin.Chapter2.LinearDouble
