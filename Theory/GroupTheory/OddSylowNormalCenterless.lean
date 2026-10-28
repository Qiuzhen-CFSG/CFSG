module
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Abelian odd Sylow subgroups near a normal rank-one factor

A normal centerless factor K and its centralizer form a direct product.
When K has odd-prime rank one and the ambient group has rank at most two,
the centralizer has rank at most one. Both factors therefore have cyclic
Sylow subgroups at that prime. A two-group outer automorphism group puts
every odd-prime subgroup in this direct product, forcing commutativity.

The second theorem carries this argument through the original embedded
two-core of K. Coprime Sylow transport retains the actual ambient group.
Source application: Aschbacher--Smith, proof of 12.3.13, printed p.811.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A normal centerless rank-one factor leaves cyclic odd Sylow factors. -/
theorem sylow_commutative_of_normal_centerless_rank_one
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (K : Subgroup G) [K.Normal] (hz : center K = ⊥)
    (hrK : primeRank p K = 1) (hrG : primeRank p G ≤ 2)
    (hout : IsPGroup 2 (MulAut.Outer K))
    (P : Sylow p G) : IsMulCommutative P := by
  let C := centralizer (K : Set G)
  have hdis : Disjoint K C := by
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨hxK,hxC⟩
    have hx : (⟨x,hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (hxC k k.property)
    rw [hz,mem_bot] at hx
    exact congrArg Subtype.val hx
  have hcomm : K ≤ centralizer (C : Set G) := le_centralizer_iff.mp le_rfl
  have hrC : primeRank p C ≤ 1 := by
    have h := K.primeRank_sup_eq_add_of_disjoint_commuting C hdis hcomm p
    have hu := (_root_.primeRank_le_of_injective p (K ⊔ C).subtype
      (K ⊔ C).subtype_injective).trans hrG
    omega
  let a : P →* MulAut.Outer K :=
    ((QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (MulAut.conjNormal : G →* MulAut K)).comp (P : Subgroup G).subtype
  have ha : ∀ x : P, a x = 1 := by
    have hd := IsPGroup.disjoint_of_coprime
      (P.isPGroup'.of_surjective a.rangeRestrict a.rangeRestrict_surjective)
      (hout.to_subgroup ⊤) (Nat.coprime_two_right.mpr hp)
    intro x
    exact (Subgroup.disjoint_def.mp hd) ⟨x,rfl⟩ (mem_top _)
  have hPC : (P : Subgroup G) ≤ K ⊔ C := by
    intro x hx
    rw [← MulAut.conjNormal_comap_innerSubgroup K]
    exact (QuotientGroup.eq_one_iff (MulAut.conjNormal (H := K) x)).mp (ha ⟨x,hx⟩)
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K C hdis hcomm
  let f : P →* K × C := e.symm.toMonoidHom.comp (inclusion hPC)
  have hf : Function.Injective f := e.symm.injective.comp (inclusion_injective hPC)
  let fK := (MonoidHom.fst K C).comp f
  let fC := (MonoidHom.snd K C).comp f
  have hcyc {B : Type u} [Group B] [Finite B] (b : P →* B)
      (hr : primeRank p B ≤ 1) : IsCyclic b.range := by
    obtain ⟨Q,hQ⟩ :=
      (P.isPGroup'.of_surjective b.rangeRestrict b.rangeRestrict_surjective).exists_le_sylow
    let : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one hp hr
    exact isCyclic_of_le hQ
  let : IsCyclic fK.range := hcyc fK hrK.le
  let : IsCyclic fC.range := hcyc fC hrC
  refine ⟨⟨fun x y => hf ?_⟩⟩
  apply Prod.ext
  · change fK (x * y) = fK (y * x)
    simpa only [map_mul,Subgroup.coe_mul,MonoidHom.coe_rangeRestrict] using
      congrArg Subtype.val (mul_comm' (fK.rangeRestrict x) (fK.rangeRestrict y))
  · change fC (x * y) = fC (y * x)
    simpa only [map_mul,Subgroup.coe_mul,MonoidHom.coe_rangeRestrict] using
      congrArg Subtype.val (mul_comm' (fC.rangeRestrict x) (fC.rangeRestrict y))

/-- The same conclusion for a normal factor with a two-core kernel. -/
theorem sylow_commutative_of_normal_twoCore_quotient_rank_one
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (K : Subgroup G) [K.Normal] (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : primeRank p (K ⧸ pCore 2 K) = 1) (hrG : primeRank p G ≤ 2)
    (hout : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)))
    (P : Sylow p G) : IsMulCommutative P := by
  let N := K.pCoreIn 2
  let : N.Normal := inferInstanceAs (((pCore 2 K).map K.subtype).Normal)
  let q := QuotientGroup.mk' N
  let B := K.map q
  let : B.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective N)
  have hker : (q.subgroupMap K).ker = pCore 2 K := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact comap_map_eq_self_of_injective K.subtype_injective _
  let e : (K ⧸ pCore 2 K) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
        (q.subgroupMap_surjective K))
  have hzB : center B = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have h := (centerCongr e.symm ⟨b,hb⟩).property
    change e.symm b ∈ center (K ⧸ pCore 2 K) at h
    rw [hz,mem_bot] at h
    exact e.symm.map_eq_one_iff.mp h
  have hrB : primeRank p B = 1 := by rw [← primeRank_congr p e,hrK]
  have hrQ : primeRank p (G ⧸ N) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p hp N (isPGroup_pCoreIn 2 K)).trans hrG
  have hoB : IsPGroup 2 (MulAut.Outer B) :=
    hout.of_equiv (MulAut.outerCongr e)
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective N)
  let : IsMulCommutative Q :=
    sylow_commutative_of_normal_centerless_rank_one hp B hzB hrB hrQ hoB Q
  have hc : Nat.Coprime p (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (isPGroup_pCoreIn 2 K).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hp).pow_right n
  let eP := Sylow.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective N) hc P Q
  let : CommGroup P := MonoidHom.commGroupOfInjective eP.toMonoidHom eP.injective
  exact ⟨inferInstance⟩
end Subgroup
