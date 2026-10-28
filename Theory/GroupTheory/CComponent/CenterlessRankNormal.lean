module
public import Theory.GroupTheory.CComponent.RankTwoResidual

/-!
# Normality from a centerless component quotient of cubic rank two

Pass through the ambient two-core to an ordinary component. Distinct
conjugates would contribute cubic rank at least four. The ambient rank-two
bound forces normality, which lifts through the solvable two-core.

Source: Aschbacher–Smith A.3.8(3), printed p.46; the component-normality
step in 15.3.17 and 15.3.20, printed pp.1126–1127.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

theorem IsCComponent.normal_of_centerless_core_threeRank
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) (hrG : primeRank 3 G ≤ 2) : K.Normal := by
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
  exact cComponent_normal_of_quotient_normal hK (pCore 2 G) inferInstance
end Subgroup
