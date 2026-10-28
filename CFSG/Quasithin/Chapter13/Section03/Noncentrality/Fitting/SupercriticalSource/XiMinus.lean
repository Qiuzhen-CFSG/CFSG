module

public import CFSG.Quasithin.Chapter3.Section02.SourceXiMinus
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.XiSource

/-!
# The original starred residual gives the elementary-nine source quotient

The actual selected residual moves the original omega-center module by the
rank-one centralizing-residual bound. A.4.8 therefore gives its faithful
signalizer module. The general 3.2.13 implication supplies Xi-minus, and the
constructed binary-tetrahedral actor supplies the ambient cubic automizer.
The existing rank argument then gives p=3 and the literal E₉ quotient.

The universal preceding 3.1.8(1) theorem and the separate starred-family
placement from 1.3.4/13.3.2 remain explicit. No Xi-minus, faithful-module,
actor-model, automizer or elementary-nine conclusion is assumed.
Source: Aschbacher–Smith, Lemma 13.3.14(d), printed p.892.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem star_residual_nine_of_starred_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    (H Lplus U : Subgroup G) (hH : H ∈ Chapter1.He G) (hLH : Lplus ≤ H)
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (D : Subgroup (Star H)) [D.Normal] {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hD : Chapter1.XiOddQuotient p D) (hrD : primeRank p D = 2)
    (hr : primeRank 3 (Star H) ≤ 2)
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : primeRank p (centralizingResidual U) ≤ 1)
    (hstar : (starResidual H D).map H.subtype ∈ Chapter1.XiStar G (T : Subgroup G))
    (hm : (pCore 2 Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)) ≠ ⊥) :
    p = 3 ∧ IsElementaryAbelian 3 D ∧ Nat.card D = 9 ∧
      Nonempty ((starResidual H D ⧸ pCore 2 (starResidual H D)) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  have hmove := starResidual_moves_of_rank H U D hp hD.isPGroup (by omega) hY
  have hfaith := star_residual_faithful H U D hH hU hmove
  have hminus := Chapter3.SourceXiMinus.source_XiStarF_subset_XiMinus_of_318 hG h318 T
    ⟨⟨hstar.1, hfaith⟩, hstar⟩
  exact star_residual_nine_of_XiMinus T H Lplus hLH hL hL3 D hp hD hrD.le hr hminus hm

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
