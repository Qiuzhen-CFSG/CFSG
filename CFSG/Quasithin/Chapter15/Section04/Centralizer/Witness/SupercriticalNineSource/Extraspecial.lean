module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.Ternary
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.CubicInverter
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ExtraspecialExtensions
public import Theory.SpecificGroups.HeisenbergPrime.Recognition

/-!
# Excluding the exponent-three extraspecial branch

The original cubic actor in X has nontrivial Frattini action. Coprime
centralizer lifting inside X provides a commuting actor inducing inversion.
Their actual images in the source quotient satisfy A.1.33(1), contradicting
the ternary rank bound. This uses neither A.1.33(2) at three nor a cubic lift
from an arbitrary quotient extension.

Source: Aschbacher--Smith 15.4.10, printed p.1159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource Matrix.GeneralLinearGroup.PrimeThreeFiveResidual

private theorem quotient_action_kernel_congr {V : Type*} [Group V]
    (A B : Subgroup V) [A.Characteristic] [B.Characteristic] (h : A = B) :
    (quotientAut A).ker = (quotientAut B).ker := by
  subst B
  rfl

/-- In rank at most two the actual source ternary shape is elementary. -/
theorem ternary_shape_elementary
    {Q X : Type*} [Group Q] [Finite Q] [Group X] [Finite X]
    (hr : primeRank 3 Q ≤ 2) (hX : IsPPerfect 2 X)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (f : X →* Q)
    (P : Subgroup Q) [P.Normal] (hs : Chapter1.XiOddQuotient 3 P)
    (hne : (pCore 2 X).map ((MulAut.conjNormal : Q →* MulAut P).comp f) ≠ ⊥) :
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 := by
  rcases hs with hs | ⟨hs, hc, hexp⟩
  · exact hs
  · let : IsExtraspecial 3 P := hs
    let a := (MulAut.conjNormal : Q →* MulAut P).comp f
    let b := (quotientAut (center P)).comp a
    let : IsElementaryAbelian 3 (P ⧸ center P) :=
      IsExtraspecial.quotient_elementary_abelian 3 P
    have hcard : Nat.card (P ⧸ center P) = 9 := by
      have hh := (center P).index_mul_card
      change Nat.card (P ⧸ center P) * Nat.card (center P) = Nat.card P at hh
      rw [IsExtraspecial.center_order_p 3 P, hc] at hh
      omega
    have hb : (pCore 2 X).map b ≠ ⊥ := by
      have hh := twoCore_frattini_image_ne_bot (by decide : 3 ≠ 2)
        (IsExtraspecial.isPGroup 3 P) a hne
      have hk : ((quotientAut (frattini P)).comp a).ker = b.ker := by
        rw [← MonoidHom.comap_ker, quotient_action_kernel_congr _ _
          (IsExtraspecial.frattini_eq_center (p := 3))]
        rfl
      intro hb
      apply hh
      rw [Subgroup.map_eq_bot_iff, hk]
      exact (Subgroup.map_eq_bot_iff _).mp hb
    obtain ⟨x, t, hx, hxV, htx, ht⟩ := exists_commuting_inverter hcard hX hX3 b hb
    have hfx : orderOf (f x) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (hx ▸ orderOf_map_dvd f x) with h | h
      · exfalso
        apply hxV
        change quotientAut (center P) (MulAut.conjNormal (f x)) = 1
        rw [orderOf_eq_one_iff.mp h, map_one, map_one]
      · exact h
    have hmodel : Nonempty (P ≃* HeisenbergPrime 3) :=
      HeisenbergPrime.nonempty_mulEquiv_of_card_prime_cube hc
        (fun z => by rw [← hexp]; exact Monoid.pow_exponent_eq_one z)
        (IsExtraspecial.commutator_eq_center (p := 3)).le (by
          intro hn
          have hh : center P = ⊤ := center_eq_top_iff.mpr hn
          have hcc := IsExtraspecial.center_order_p 3 P
          rw [hh, Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv, hc] at hcc
          norm_num at hcc)
    have hlarge := ChapterA.RankActions.primeRank_gt_two_of_extraspecial_inverter P
      hmodel.some (by decide : 3 ≠ 2) (f t) (f x) ht hfx
      (mem_centralizer_singleton_iff.mpr (by simpa only [map_mul] using (congrArg f htx).symm)) hxV
    omega

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
