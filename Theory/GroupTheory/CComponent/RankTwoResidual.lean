module
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentCoprimeRankNormal

/-!
# The ordinary cubic residual from a rank-two C-component

Normality is derived on the actual two-core image by the rank bound, then
reflected through the solvable two-core. The ordinary centerless, outer-two
case of A.3.18 follows on the original subgroup, without assuming normality.
-/
public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

theorem IsCComponent.eq_primeToResidual_three_of_rank_outer_two
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) (hrG : primeRank 3 G ≤ 2)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) :
    K = primeToResidual 3 G := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hb : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨(hK.map_quotient (pCore 2 G)).subnormal,inferInstance⟩
  have hcz : center B = ⊥ := by
    apply le_bot_iff.mp
    intro b hb
    have he : e.symm b = 1 := hz.le ((centerCongr e).symm ⟨b,hb⟩).property
    exact e.symm.map_eq_one_iff.mp he
  have hcop : Nat.Coprime 3 (Nat.card (center B)) := by rw [hcz,card_bot]; decide
  have hrB : 2 ≤ primeRank 3 B := by rwa [←primeRank_congr 3 e]
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrG
  let : B.Normal := hb.normal_of_coprime_center_primeRank 3 hcop (by omega)
  let : K.Normal := cComponent_normal_of_quotient_normal hK (pCore 2 G) inferInstance
  exact hK.eq_primeToResidual_three_of_outer_twoGroup hz hrK hrG ho
end Subgroup

