module
public import Theory.Quasithin.CentralExtensionRankFour
public import Theory.GroupTheory.PrimeRankInvolutionLift

/-!
# Involution-centralizer rank in odd central quotients

The rank-four lifting theorem bounds every odd-prime rank in an involution
centralizer of the central quotient of a quasithin group by three. An
actual elementary subgroup attaining the rank supplies the lifting witness.
The conclusion does not assert quasithinness of the quotient.

Source: Aschbacher–Smith A.2.15(2), printed p.37, used in A.2.17.
-/

open Subgroup
namespace CentralExtension
variable {G : Type*} [Group G] [Finite G]
/-- An odd central quotient of a quasithin group has every odd-prime
involution-centralizer rank at most three. This is a rank bound, not quotient
quasithinness. -/
public theorem primeRank_involutionCentralizer_le_three_of_odd_center
    {H : Type*} [Group H] [Finite H] {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (iso : G ⧸ center G ≃* H) (ho : Odd (Nat.card (center G)))
    (hqt : IsQuasithin G) {z : H} (hz : orderOf z = 2) :
    primeRank r (centralizer ({z} : Set H)) ≤ 3 := by
  by_contra hn
  obtain ⟨E, hE, hc⟩ := exists_elementaryAbelian_card_primeRank
    (G := centralizer ({z} : Set H)) (p := r)
  let := hE
  apply CentralExtension.not_isQuasithin_of_center_quotient_model iso ho hr hz
    E.subtype E.subtype_injective _ hqt
  rw [hc]
  exact pow_le_pow_right' (Fact.out : r.Prime).one_lt.le (by omega)

end CentralExtension
