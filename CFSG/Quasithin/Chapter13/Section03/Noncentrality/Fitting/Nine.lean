module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.XiPrime
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.Rank
public import Theory.ElementaryAbelian.PrimePlane

/-!
# The elementary-nine quotient in 13.3.14(d)

The extraspecial alternative is excluded by an actual elementary subgroup
of order 27. The cubic residual of L₊ and its nontrivial two-core action
supply the inverter and cubic used in the checked extraspecial construction.
This contradicts the three-rank bound. The remaining elementary alternative
has an actual isomorphism with C₃ × C₃.

The Ξ-minus application first proves p=3 and then identifies the original
residual's intrinsic two-core quotient with that plane. The earlier Ξ-minus
membership and cubic action must still be constructed; the D.2.17 versus
3.1.8 ratio contradiction is not asserted here.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.3.14(d), printed p.892, PDF p.909. The intrinsic extraspecial rank
construction is reused from the A.1.33 application in the 13.8.13 development.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]

/-- Exclude the extraspecial alternative using the original cubic residual L₊. -/
theorem star_nine_of_cubic_residual (H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (D : Subgroup (Star H)) [D.Normal] (hD : Chapter1.XiOddQuotient 3 D)
    (hr : primeRank 3 (Star H) ≤ 2)
    (hm : (pCore 2 Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)) ≠ ⊥) :
    IsElementaryAbelian 3 D ∧ Nat.card D = 9 ∧
      Nonempty (D ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  rcases hD with ⟨he, hc⟩ | ⟨he, hc, hexp⟩
  · let := he
    exact ⟨he, hc, IsElementaryAbelian.nonempty_mulEquiv_plane_of_card hc⟩
  · exfalso
    let := he
    have hp (x : D) : x ^ 3 = 1 := by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one x
    obtain ⟨E, _, hE, hcE⟩ :=
      Section08.SolvableExclusion.Three.Extraspecial.elementary_of_cubic_residual
        D ⊤ hc hp le_top hL hL3 (starMap H Lplus hLH) (fun _ => mem_top _) hm
    let := hE
    have hlo : 3 ≤ Group.rank E := IsElementaryAbelian.rank_ge_of_card (p := 3)
      (by simpa using hcE)
    have hup := (rank_le_primeRank_of_abelian_pGroup 3 E hE.isPGroup
      hE.toIsMulCommutative).trans hr
    omega

/-- For the actual residual, prove p=3 and identify its two-core quotient with E₉. -/
theorem star_nine_of_XiMinus (T H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (D : Subgroup (Star H)) [D.Normal] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hD : Chapter1.XiOddQuotient p D) (hr : primeRank 3 (Star H) ≤ 2)
    (hminus : (starResidual H D).map H.subtype ∈ Chapter3.XiMinus G T)
    (h3 : 3 ∣ Nat.card (Chapter3.xiQuotientAutomizer ((starResidual H D).map H.subtype)))
    (hm : (pCore 2 Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)) ≠ ⊥) :
    p = 3 ∧ IsElementaryAbelian 3 D ∧ Nat.card D = 9 ∧
      Nonempty ((starResidual H D ⧸ pCore 2 (starResidual H D)) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  let : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp (hD.one_lt_card Fact.out)
  have hp3 := prime_eq_three_of_starResidual_XiMinus T H D hp hD.isPGroup hminus h3
  subst p
  obtain ⟨he, hc, ⟨e⟩⟩ := star_nine_of_cubic_residual H Lplus hLH hL hL3 D hD hr hm
  exact ⟨rfl, he, hc, ⟨(oddStarResidualCoreEquiv H D hp hD.isPGroup).trans e⟩⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
