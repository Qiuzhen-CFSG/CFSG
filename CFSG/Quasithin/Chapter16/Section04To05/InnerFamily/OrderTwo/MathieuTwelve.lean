module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.MathieuTwelve.ModelInputs
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.Reductions
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis

/-!
# Conditional assembly of the M₁₂ order argument

The common reduction leaves |R| = 4. Split on O₂(L). The nontrivial-cover
branch uses the actual factorization and I.2.2(5b); the centerless branch uses
the Sylow-centralizer commutator and automorphism generation. The ambient
arguments and the transition Z(L) = O₂(L) are proved, with the latter obtained
from the genuine even-type hypothesis.

Two model obligations remain: `MarkedResidualInvolution` and
`CenterlessLocalCalculation`. The theorem below names these additional inputs
explicitly and does not claim the unconditional M₁₂ branch of 16.4.9(1).
The center bound is the M₁₂ specialization of 16.1.2(2), the relative-normalizer
inputs are 16.4.2(1), and the lifting input is the applicable clause of I.2.2(5b).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.9(1), printed p.1189, case (III).
-/

@[expose] public section

open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.MathieuTwelve
open OuterResidual
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- Assemble both cover cases once the two genuine model calculations have been proved.
The arbitrary group class permits direct specialization to KnownSimple.IsKnownSimple. -/
theorem card_two_of_model_calculations (hG : Hypothesis1611 K G)
    (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hrout : r ∉ centralizer (L : Set G) ⊔ L)
    (htransfer : OuterResidualTransfer L g R)
    (hC : Nat.card (residualCentralizer L r) = 4)
    [IsElementaryAbelian 2 (residualCentralizer L r)]
    (e : R ≃* ↥(commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G)))
    (hn : commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    (hZcard : Nat.card (center L) ≤ 2)
    (hlift : pCore 2 L ≠ ⊥ → NonTwoCentralInvolutionLifting L)
    (hmark : Nat.card R = 4 → MarkedResidualInvolution L r)
    (hmodel : Nat.card R = 4 → center L = ⊥ → CenterlessLocalCalculation h r) :
    Nat.card R = 2 := by
  have hZ : center L = pCore 2 L :=
    hG.evenType.component_center_eq_twoCore h.involution h.component
  have hres := htransfer r hr hr2 hrout
  rcases card_two_or_four_of_residualCentralizer_card_four h hr hr2 hres hC with hc | hc
  · exact hc
  have hcard : Nat.card R = Nat.card (residualCentralizer L r) := hc.trans hC.symm
  have hm := hmark hc
  exfalso
  by_cases hO : pCore 2 L = ⊥
  · obtain ⟨hgen, hcomm⟩ := hmodel hc (hZ.trans hO)
    obtain ⟨s, u, hs2, hum, hu⟩ := lift_marked_residual_involution h hres hcard hm
    have hsinner : actionMap (h.le_sylow.trans h.sylow_normalizes) s ∈ actionImage L L :=
      hu ▸ (centerQuotientEquivActionImage L u).property
    obtain ⟨v, hv, c, hcC, he⟩ := inner_factorization h s hs2 hsinner
    exact trivial_cover_contradiction h hr hres hc e hn hgen s.property hs2 hv.2
      hcC.1.2 he (hcomm s hs2 u hum hu v hv c hcC.1 he)
  · have hZne : center L ≠ ⊥ := fun he => hO (hZ.symm.trans he)
    have hZtwo : Nat.card (center L) = 2 := by
      have hpos : 0 < Nat.card (center L) := Nat.card_pos
      have hne : Nat.card (center L) ≠ 1 := fun he => hZne ((center L).eq_bot_iff_card.mpr he)
      omega
    exact cover_contradiction h hres hcard e hZtwo (hlift hO) hm

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.MathieuTwelve
