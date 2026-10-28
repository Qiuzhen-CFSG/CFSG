module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Automizer
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Nine

/-!
# The source-selected faithful Ξ member and its ambient cubic automizer

From the original moving two-core and the preceding parabolic and rank
hypotheses, select a characteristic odd subgroup and its actual moving
residual. The residual belongs to Ξ-f and has a cubic ambient automizer.
The elementary-nine application then discharges the automizer input of the
existing source theorem; its genuine preceding Ξ-minus membership remains
explicit. The 1.3.4/13.3.2 list exclusion and 3.2.13 are separate earlier
source steps, not asserted by this module.

Source: Aschbacher–Smith 13.3.14(d), printed p.892.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem source_selected_XiF_cubic
    (T : Sylow 2 G) (H Lplus U : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hTH : (T : Subgroup G) ≤ H) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hp : Odd p) (hr : primeRank p (Star H) ≤ 2)
    (hm : ¬ (star H Lplus hLH).pCoreIn 2 ≤ centralizer (pCore p (Star H) : Set (Star H)))
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ∃ (D : Subgroup (Star H)) (hD : D.Characteristic),
      letI : D.Characteristic := hD
      let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
      D ≤ pCore p (Star H) ∧ primeRank p D = 2 ∧ Chapter1.XiOddQuotient p D ∧
      (pCore 2 Lplus).map a ≠ ⊥ ∧
      Nonempty (a.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((((T : Subgroup G).subgroupOf Lplus).map a) ≃* QuaternionGroup 2) ∧
      ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥ ∧
      (starResidual H D).map H.subtype ∈ Chapter1.XiF G (T : Subgroup G) ∧
      3 ∣ Nat.card (Chapter3.xiQuotientAutomizer ((starResidual H D).map H.subtype)) := by
  obtain ⟨D, hD, hle, hrD, hmodel, hmove, hfull, hsyl, hmoved, hXi⟩ :=
    source_selected_XiF T H Lplus U hH hTH hLH hTL hL hL3 hp hr hm hU hY
  let : D.Characteristic := hD
  exact ⟨D, hD, hle, hrD, hmodel, hmove, hfull, hsyl, hmoved, hXi,
    star_residual_cubic_automizer H Lplus hLH D hp hmodel.isPGroup hfull⟩

theorem star_residual_nine_of_XiMinus
    (T H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (D : Subgroup (Star H)) [D.Normal] (hp : Odd p)
    (hD : Chapter1.XiOddQuotient p D) (hrD : primeRank p D ≤ 2)
    (hr : primeRank 3 (Star H) ≤ 2)
    (hminus : (starResidual H D).map H.subtype ∈ Chapter3.XiMinus G T)
    (hm : (pCore 2 Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)) ≠ ⊥) :
    p = 3 ∧ IsElementaryAbelian 3 D ∧ Nat.card D = 9 ∧
      Nonempty ((starResidual H D ⧸ pCore 2 (starResidual H D)) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  have hmodel := (actual_actor_models hp hD.isPGroup hrD hL hL3 _ hm).1
  exact star_nine_of_XiMinus T H Lplus hLH hL hL3 D hp hD hr hminus
    (star_residual_cubic_automizer H Lplus hLH D hp hD.isPGroup hmodel) hm

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
