module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddCartan

/-!
# The actual odd-exponent quotient in the Chapter12 application

The completed residual maximality and nonfaithfulness producer supplies the
premises for the direct-product quotient of HD_L. The isomorphism keeps the
original H and Cartan representatives, and the resulting quotient has binary
rank exactly four. Every involution modulo its two-core already has its lift
in H; the last theorem applies this to the literal displacement contract.

This supplies the quotient structure and rank used in 5.1.17. The natural/TI
construction and the nine-dimensional displacement estimate remain with
qt-d-1222-linear-field-parity; no parity conclusion is asserted here.
Source: Aschbacher–Smith 5.1.17, printed p.641, used in 12.2.2, printed p.795
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The source product with its two literal inclusions and no residual callback. -/
theorem rankOne_odd_join_quotient_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n) :
    ∃ e : ((H ⧸ pCore 2 H) × A) ≃*
        ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)),
      ∀ (x : H) (a : A),
        e (QuotientGroup.mk' (pCore 2 H) x, a) =
          QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
            ⟨(x : G) * (a : G), mul_mem_sup x.property a.property⟩ := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact odd_join_quotient_product hi hH c hodd hm hf hlinear

/-- The rank clause needed by the selected parity seed is exactly four. -/
theorem rankOne_odd_join_quotient_two_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n) :
    primeRank 2 ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) = 4 := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact odd_join_quotient_two_rank hi hH c hodd hm hf hlinear

/-- Reduction of the actual displacement obligation, without assuming order-two lifts. -/
theorem rankOne_odd_displacement_iff_on_outside
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hodd : Odd n) (U : Subgroup G) :
    LargeDisplacement (setup T L U H A) ↔
      ∀ y ∈ H, y ^ 2 ∈ H.pCoreIn 2 → y ∉ H.pCoreIn 2 →
        9 ≤ displacement (setup T L U H A) y := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact largeDisplacement_iff_on_outside_of_odd hi hH c hodd hm hf hlinear U

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
