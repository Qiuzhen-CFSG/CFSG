/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.V.Semidirect
public import Submission.BenderSuzuki.External.Huppert.V.SamePrime

/-!
# Huppert V.8.12

Book-order entry file for the fixed-point-free cyclic and same-prime tools used
before V.8.13.

Principal exported declarations include:
* `hkt_frobenius_complement_cyclic_prime_of_fixedPoint_hypotheses`
* `hkt_fixedPointSubgroup_zpowers_eq_bot_of_distinct_elementary_prime_product`
* `hkt_same_prime_v812_product_identity_core`
* `hkt_same_prime_fixedPoint_quotient_contradiction`
-/

namespace BenderSuzuki
namespace External


universe u
/-- Huppert V.8.12, cyclic Frobenius-complement interface. -/
public theorem huppert_V_8_12_frobenius_complement_cyclic_prime_of_fixedPoint_hypotheses
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    [MulDistribMulAction G M] [Nontrivial M]
    (K R : Subgroup G)
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hsolvG : IsSolvable G)
    (hnilM : Group.IsNilpotent M)
    (hcop : Nat.Coprime (Nat.card G) (Nat.card M))
    (hfixK : fixedPointSubgroup (↥K) M = ⊥)
    (hfixR : ∀ x : R, x ≠ 1 →
      fixedPointSubgroup (↥(Subgroup.zpowers (x : G))) M = fixedPointSubgroup (↥R) M) :
    IsCyclic R ∧ Nat.Prime (Nat.card R) :=
  hkt_frobenius_complement_cyclic_prime_of_fixedPoint_hypotheses
    (G := G) (M := M) K R hfrob hsolvG hnilM hcop hfixK hfixR

end External
end BenderSuzuki
