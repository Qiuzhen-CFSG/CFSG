module
public import Theory.GroupTheory.CComponent.CenterlessRankNormal

/-!
# C-component normality from odd prime rank and a coprime core center

Passing through the ambient two-core gives an ordinary component. Two
distinct commuting conjugates have additive p-ranks when their center has
order prime to p. Thus rank at least two in an ambient group of p-rank at
most two forces normality, which lifts through the ambient two-core.

Source: Aschbacher–Smith A.3.8(3), printed p.46. The actual consumer is the
SL₃ row of C.4.5, where an odd torus prime may differ from three.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}
theorem IsCComponent.normal_of_coprime_core_center_primeRank
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))))
    (hrK : 2 ≤ primeRank p (K ⧸ pCore 2 K))
    (hrG : primeRank p G ≤ 2) : K.Normal := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hb : IsComponent (G ⧸ pCore 2 G) B :=
    ⟨(hK.map_quotient (pCore 2 G)).subnormal,inferInstance⟩
  have hcz : Nat.Coprime p (Nat.card (center B)) := by
    rwa [← Nat.card_congr (centerCongr e).toEquiv]
  have hrB : 2 ≤ primeRank p B := by rwa [← primeRank_congr p e]
  have hrQ : primeRank p (G ⧸ pCore 2 G) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup p hp _ pCore_isPGroup).trans hrG
  let : B.Normal := hb.normal_of_coprime_center_primeRank p hcz (by omega)
  exact cComponent_normal_of_quotient_normal hK (pCore 2 G) inferInstance
end Subgroup
