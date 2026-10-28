module
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitAutomizer
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# A normal two-core cannot displace a component Borel

A nonidentity odd-order element in M ∩ K prevents O₂(M) from moving K
to a commuting, disjoint component. Its commutator with a proposed mover
lies in O₂(M), while commuting factors make that commutator have odd order.
It is therefore trivial, putting the original element in the factor
intersection. This supplies the missing factor-preservation step in the
paired Bender source argument.

Source: Aschbacher–Smith E.2.7, printed p.219, the assertion V ≤ K₁K₁ᵗ.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]

theorem pCoreIn_le_component_normalizer_of_odd_element
    (M K : Subgroup H) (hK : IsComponent H K) (hC : K.IsCComponent)
    (hrad : solvableRadical H = ⊥) (b : H) (hbK : b ∈ K) (hbM : b ∈ M)
    (hb : b ≠ 1) (hodd : Nat.Coprime 2 (orderOf b)) :
    M.pCoreIn 2 ≤ normalizer (K : Set H) := by
  intro x hx
  by_contra hn
  let D := K.map (MulAut.conj x).toMonoidHom
  have hne : K ≠ D := by
    intro he
    exact hn (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : ⁅K,D⁆ = ⊥ := hK.commutator_eq_bot_of_ne (hK.map_conj x) hne
  have hd : Disjoint K D := hC.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hrad hc
  let c := MulAut.conj x b
  have hcD : c ∈ D := mem_map_of_mem _ hbK
  have hcomm : Commute b c := (commutator_eq_bot_iff_le_centralizer.mp hc hbK c hcD).symm
  let z := c * b⁻¹
  have hz : z ∈ M.pCoreIn 2 := by
    have hnQ : M ≤ normalizer (M.pCoreIn 2 : Set H) := by
      apply le_normalizer_iff.mpr
      intro g hg y hy
      obtain ⟨a,ha,rfl⟩ := hy
      exact ⟨⟨g,hg⟩ * a * (⟨g,hg⟩ : M)⁻¹,
        (inferInstance : (pCore 2 M).Normal).conj_mem a ha ⟨g,hg⟩,rfl⟩
    have hi := (mem_normalizer_iff.mp (hnQ hbM) x⁻¹).mp ((M.pCoreIn 2).inv_mem hx)
    have hh := (M.pCoreIn 2).mul_mem hx hi
    simpa only [z,c,MulAut.conj_apply,mul_assoc] using hh
  have hzpow : z ^ orderOf b = 1 := by
    rw [show z = c * b⁻¹ from rfl,(hcomm.symm.inv_right).mul_pow]
    have hcpow : c ^ orderOf b = 1 := by
      change (MulAut.conj x b) ^ orderOf b = 1
      rw [← map_pow,pow_orderOf_eq_one,map_one]
    rw [hcpow,inv_pow,pow_orderOf_eq_one,inv_one,one_mul]
  obtain ⟨k,hk⟩ := isPGroup_pCoreIn 2 M ⟨z,hz⟩
  have hz2 : orderOf z ∣ 2^k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hodd.pow_left k) hz2 (orderOf_dvd_of_pow_eq_one hzpow))
  have hcb : c = b := mul_inv_eq_one.mp hz1
  exact hb (disjoint_def.mp hd hbK (hcb ▸ hcD))

/-- A nontrivial two-perfect seed supplies the required odd element. -/
theorem pCoreIn_le_component_normalizer_of_pPerfect
    (M K B : Subgroup H) (hK : IsComponent H K) (hC : K.IsCComponent)
    (hrad : solvableRadical H = ⊥) (hBK : B ≤ K) (hBM : B ≤ M)
    (hB : B ≠ ⊥) (hp : IsPPerfect 2 B) :
    M.pCoreIn 2 ≤ normalizer (K : Set H) := by
  have hn : ¬ IsPGroup 2 B := by
    intro h
    have hi := hp.hom_eq_one_of_isPGroup h (MonoidHom.id B)
    apply hB
    apply eq_bot_iff.mpr
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hi ⟨x,hx⟩)
  have hsub : ¬ (Nat.card B).primeFactors ⊆ (2 : ℕ).primeFactors := by
    simpa only [← isPGroup_iff_primeFactors_card_subset (G := B) (by decide : 2 ≠ 0)] using hn
  obtain ⟨p,hpB,hp2⟩ := Finset.not_subset.mp hsub
  obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hpB
  have hne : p ≠ 2 := by
    intro he
    apply hp2
    rw [he]
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hbn : (b:H) ≠ 1 := by
    intro he
    have he' : b = 1 := Subtype.ext he
    rw [he',orderOf_one] at hb
    exact hprime.ne_one hb.symm
  exact pCoreIn_le_component_normalizer_of_odd_element M K hK hC hrad b
    (hBK b.property) (hBM b.property) hbn
    (by rw [← Subgroup.orderOf_mk b.val b.property,hb]
        exact (Nat.coprime_primes Nat.prime_two hprime).mpr hne.symm)
end Subgroup
