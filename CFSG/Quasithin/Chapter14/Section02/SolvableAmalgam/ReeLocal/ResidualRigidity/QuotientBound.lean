module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity.LinearResidual
/-!
# Bounding the ambient quotient by its involution orbit

A faithful binary actor with cyclic Sylow two-subgroup of order at most four
has odd residual. If its order is divisible by five, any residual larger than
five is cyclic of order fifteen and acts regularly. An intransitive nonidentity
orbit therefore bounds the whole actor by twenty. This uses the proved
odd-order theorem through `LinearResidual`, without ambient solvability.

Source: Aschbacher--Smith 14.2.21, printed p.989, residual-enlargement step.
-/

open Subgroup
open CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity

/-- A larger odd residual would force the forbidden regular orbit. -/
public theorem card_le_twenty_of_intransitive
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (T : Sylow 2 A) (hT : IsCyclic T) (hTc : Nat.card T ≤ 4)
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ) (hV : Nat.card V = 16)
    (hfive : 5 ∣ Nat.card A) (v : V) (hv : v ≠ 1)
    (hno : ¬ (∀ y : V, y ≠ 1 → ∃ a : A, ρ a v = y)) : Nat.card A ≤ 20 := by
  let R := pResidual 2 A
  have hp : IsPGroup 2 (A ⧸ R) := isPGroup_quotient_pResidual 2
  have hc : Nat.card R * Nat.card (A ⧸ R) = Nat.card A := R.card_mul_index
  have h5 : 5 ∣ Nat.card R := by
    rw [← hc] at hfive
    rcases (by decide : Nat.Prime 5).dvd_mul.mp hfive with h | h
    · exact h
    · obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [hn] at h
      have := (by decide : Nat.Prime 5).dvd_of_dvd_pow h
      norm_num at this
  have hRc : Nat.card R ≤ 5 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := R) 5 h5
    let K := zpowers a
    have hK : Nat.card K = 5 := (Nat.card_zpowers a).trans ha
    by_cases htop : K = ⊤
    · simpa only [htop, card_top] using hK.le
    · obtain ⟨_, _, hreg⟩ := cyclic_fifteen_regular T hT ρ hρ hV K hK (lt_top_iff_ne_top.mpr htop)
      exact (hno (fun y hy => by
        obtain ⟨b, hb, _⟩ := hreg v y hv hy
        exact ⟨b, hb⟩)).elim
  have hindex : Nat.card (A ⧸ R) ≤ Nat.card T := by
    let U := T.mapSurjective (QuotientGroup.mk'_surjective R)
    have hU : (U : Subgroup (A ⧸ R)) = ⊤ :=
      (U.is_maximal' (hp.to_subgroup ⊤) le_top).symm
    let f := (QuotientGroup.mk' R).comp T.toSubgroup.subtype
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, he⟩ := hU.ge (mem_top y)
      exact ⟨⟨x, hx⟩, he⟩
    exact Nat.card_le_card_of_surjective f hf
  nlinarith
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
