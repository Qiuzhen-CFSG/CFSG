module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.XiSource
public import CFSG.Quasithin.Chapter3.Section02.SourceXiMinus
/-!
# Original selected residual: starred placement, Xi-minus and E₉

The genuine moving-core source selects D, constructs the full SL₂(3)
action, and identifies the image of the original T∩L₊ with Q₈. The new
starred-placement theorem removes the formerly separate Xi-star premise.
The earlier universal 3.1.8(1) implication then gives Xi-minus, and the
actual cubic automizer and odd-rank bound force p=3 and D≃E₉.

The earlier 13.3.2(1--2) list/normality and universal 3.1.8(1) implications
remain explicit. Two-perfectness and the cubic quotient of L₊ are the
preceding parabolic source facts, and the centralizing-residual bound is
13.3.14(b). No chosen D, actor model, starred membership, Xi-minus or E₉
conclusion is assumed. Q₈ is the image of T∩L₊, not the whole ambient T.

Source: Aschbacher--Smith, Lemma 13.3.14(d), printed p.892.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem source_selected_XiStarF_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T) (H Lplus U : Subgroup G)
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
      (starResidual H D).map H.subtype ∈ Chapter1.XiStarF G (T : Subgroup G) ∧
      3 ∣ Nat.card (Chapter3.xiQuotientAutomizer ((starResidual H D).map H.subtype)) := by
  obtain ⟨D,hD,hle,hrD,hmodel,hmove,hfull,hsyl,hmoved,hXi,hthree⟩ :=
    source_selected_XiF_cubic T H Lplus U hH hTH hLH hTL hL hL3 hp hr hm hU hY
  let : D.Characteristic := hD
  exact ⟨D,hD,hle,hrD,hmodel,hmove,hfull,hsyl,hmoved,
    source_XiF_subset_XiStarF hG T h1332 hXi,hthree⟩

theorem source_selected_nine_XiMinus
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T) (h318 : Chapter3.SourceTheorem318One G)
    (H Lplus U : Subgroup G)
    (hH : H ∈ Chapter1.He G) (hTH : (T : Subgroup G) ≤ H) (hLH : Lplus ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (Lplus : Set G))
    (hL : IsPPerfect 2 Lplus) (hL3 : Nat.card (Lplus ⧸ pCore 2 Lplus) = 3)
    (hp : Odd p) (hr : primeRank p (Star H) ≤ 2) (hr3 : primeRank 3 (Star H) ≤ 2)
    (hm : ¬ (star H Lplus hLH).pCoreIn 2 ≤ centralizer (pCore p (Star H) : Set (Star H)))
    (hU : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hY : primeRank p (centralizingResidual U) ≤ 1) :
    ∃ (D : Subgroup (Star H)) (hD : D.Characteristic),
      letI : D.Characteristic := hD
      let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
      p = 3 ∧ D ≤ pCore p (Star H) ∧ IsElementaryAbelian 3 D ∧ Nat.card D = 9 ∧
      Nonempty (a.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((((T : Subgroup G).subgroupOf Lplus).map a) ≃* QuaternionGroup 2) ∧
      ⁅U, (starResidual H D).map H.subtype⁆ ≠ ⊥ ∧
      (starResidual H D).map H.subtype ∈ Chapter1.XiStarF G (T : Subgroup G) ∧
      (starResidual H D).map H.subtype ∈ Chapter3.XiMinus G (T : Subgroup G) ∧
      Nonempty ((starResidual H D ⧸ pCore 2 (starResidual H D)) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  obtain ⟨D,hD,hle,hrD,hmodel,hmove,hfull,hsyl,hmoved,hXi,_⟩ :=
    source_selected_XiStarF_cubic hG T h1332 H Lplus U hH hTH hLH hTL hL hL3 hp hr hm hU hY
  let : D.Characteristic := hD
  have hminus := Chapter3.SourceXiMinus.source_XiStarF_subset_XiMinus_of_318 hG h318 T hXi
  obtain ⟨hp3,hEA,hcard,he⟩ :=
    star_residual_nine_of_XiMinus T H Lplus hLH hL hL3 D hp hmodel hrD.le hr3 hminus hmove
  exact ⟨D,hD,hp3,hle,hEA,hcard,hfull,hsyl,hmoved,hXi,hminus,he⟩
end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
