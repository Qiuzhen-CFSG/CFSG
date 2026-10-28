module
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PrimeOrderLift

/-!
# A cubic centralizing a component bounds its three-rank

A subgroup with cubic two-core quotient supplies an order-three element.
Its image still has order three modulo the ambient two-core. If it acts
trivially on the intrinsic core quotient of a centerless normal subgroup,
this image centralizes the corresponding ambient image. Rank saturation
then rules out three-rank two in the normal subgroup.

The proof uses the actual core-quotient embedding and a coprime-order lift;
it does not assume rank monotonicity for arbitrary quotient maps.
Source: Aschbacher–Smith A.3.18 and 14.7.41, pp.51–52 and p.1061,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The centralizing cubic consumes one of the two available independent three-directions. -/
theorem threeRank_le_one_of_cubic_core_centralizes
    (A C : Subgroup G) [C.Normal]
    (hA : Nat.card (A ⧸ pCore 2 A) = 3)
    (hz : center (C ⧸ pCore 2 C) = ⊥)
    (hr : primeRank 3 G ≤ 2)
    (hfix : A ≤ (normalQuotientAction C (pCore 2 C)).ker) :
    primeRank 3 (C ⧸ pCore 2 C) ≤ 1 := by
  by_contra hnot
  have htwo : 2 ≤ primeRank 3 (C ⧸ pCore 2 C) := by omega
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := C.map q
  let e : (C ⧸ pCore 2 C) ≃* B := coreQuotientEquivImage 2 C
  have hzB : center B = ⊥ := by
    apply bot_unique
    intro z hz'
    have hh := (centerCongr e).symm ⟨z,hz'⟩ |>.property
    have he : e.symm z = 1 := hz.le hh
    exact e.symm.map_eq_one_iff.mp he
  have hrB : 2 ≤ primeRank 3 B := by rwa [←primeRank_congr 3 e]
  have hc := centralizer_coprime_three_of_rank B hzB hrB
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup).trans hr)
  have hdiv : 3 ∣ Nat.card A := by
    have hd := card_quotient_dvd_card (pCore 2 A)
    rwa [hA] at hd
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
  have haG : orderOf (a : G) = 3 := (Subgroup.orderOf_coe a).trans ha
  have hqa : orderOf (q a) = 3 := by
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    exact (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk (a : G)
      (by rw [haG]; decide)).trans haG
  have hcent : q a ∈ centralizer (B : Set (G ⧸ pCore 2 G)) := by
    intro z hz'
    obtain ⟨c,hc,rfl⟩ := hz'
    let c' : C := ⟨c,hc⟩
    have he := MulEquiv.congr_fun
      (show normalQuotientAction C (pCore 2 C) a = 1 from hfix a.property)
      (QuotientGroup.mk' (pCore 2 C) c')
    rw [normalQuotientAction_apply_mk] at he
    change QuotientGroup.mk' (pCore 2 C) (MulAut.conjNormal (a : G) c') =
      QuotientGroup.mk' (pCore 2 C) c' at he
    have hh := congrArg (fun y => (e y : G ⧸ pCore 2 G)) he
    rw [coreQuotientEquivImage_apply_mk,coreQuotientEquivImage_apply_mk] at hh
    change q ((a : G)*c*(a : G)⁻¹) = q c at hh
    rw [map_mul,map_mul,map_inv] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  exact Nat.prime_three.coprime_iff_not_dvd.mp hc
    (hqa ▸ Subgroup.orderOf_dvd_natCard _ hcent)
end Subgroup
