module
public import Theory.SpecificGroups.PSL3.BinaryCubicRankParity
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.QuasithinBasic

/-!
# Cubic rank in centerless binary special linear three-space

The center of SL₃(q) has order gcd(3,q−1). If it is trivial, the binary
field degree is odd. The actual central projection is then an isomorphism,
and the quadratic-torus Sylow theorem bounds three-rank by one.

The original A₆ section in Section12.6 supplies three-rank at least two,
so the simple canonical component cannot be any of the B.5.1 SL₃ rows.
Source: Aschbacher--Smith, 12.6.17, printed p.827, using B.5.1, pp.99--103,
and the rank-one torus calculation in A.3.18, pp.51--53.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SL3
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem binary_threeRank_le_one_of_center_eq_bot (hF : Nat.card F = 2 ^ n)
    (hz : center SL(3,F) = ⊥) : primeRank 3 SL(3,F) ≤ 1 := by
  have hc : Nat.gcd 3 (Nat.card F - 1) = 1 := by
    have hh := Atlas.ExceptionalSupport.card_sl_center (ι := Fin 3) (F := F)
    simpa only [hz,card_bot,Fintype.card_fin] using hh.symm
  have hn : Odd n := by
    apply Nat.not_even_iff_odd.mp
    intro he
    have hd : 3 ∣ Nat.card F - 1 := hF ▸ (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr he
    have hh := Nat.dvd_gcd (dvd_refl 3) hd
    rw [hc] at hh
    norm_num at hh
  let e : SL(3,F) ≃* PSL(3,F) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  rw [primeRank_equiv 3 e]
  exact Matrix.PSL3.BinaryCubicRankParity.rank_le_one_of_odd hF hn
end Matrix.SL3
