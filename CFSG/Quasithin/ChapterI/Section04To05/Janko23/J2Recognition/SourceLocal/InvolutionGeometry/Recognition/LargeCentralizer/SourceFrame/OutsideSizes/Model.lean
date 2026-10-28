module

public import Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.GroupTheory.MinusExtraspecialA5Fusion.Model
import all Theory.SpecificGroups.MinusExtraspecial.ModelFixedFour
import all CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.OutsideSizes.Calculation

/-!
# Four fixed elements of an even outer involution

A nonidentity even involution on the five singular points is a double
transposition. The coordinate certificate therefore counts its fixed
subgroup as four. The internal imports deliberately reuse the coordinate
conversion and action compatibility proofs of the existing cocycle
calculation; these coordinates do not enter this module's public theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 46.8 and 46.11, pp.253–255.
-/

open Subgroup
open MinusExtraspecial MinusExtraspecial.FixedFourCalculation
open MinusExtraspecial.FixedFourCalculation.Outside
namespace J2OutsideSizesCalculation

public theorem fixed_card (a : MulAut Model) (ha : a ^ 2 = 1)
    (heven : Equiv.Perm.sign (fivePointAction a) = 1)
    (hne : fivePointAction a ≠ 1) :
    Nat.card (a.toMonoidHom.eqLocus (MonoidHom.id Model)) = 4 := by
  let ap : alternatingGroup (Fin 5) := ⟨fivePointAction a, heven⟩
  have hap : orderOf ap = 2 := orderOf_eq_prime
    (Subtype.ext (by change fivePointAction a ^ 2 = 1; rw [← map_pow, ha, map_one]))
    (fun hh => hne (congrArg Subtype.val hh))
  have hs : (fivePointAction a).support.card = 4 := by
    rw [← Equiv.Perm.sum_cycleType,
      alternatingGroup.involution_cycleType_of_degree_le_six (by decide) ap hap]
    rfl
  have hr := relations_aut a
  simp only [relations, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, and_assoc] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
  have hi : Outside.invol (encode (a (generators 0))) (encode (a (generators 1)))
      (encode (a (generators 2))) (encode (a (generators 3))) := by
    apply List.all_eq_true.mpr
    intro g _
    apply beq_iff_eq.mpr
    apply equiv.injective
    change decode (word _ _ _ _ (word _ _ _ _ g)) = decode g
    rw [decode_word, decode_word]
    have hh := congrArg (fun b : MulAut Model => b (decode g)) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hm := (moved_eq a).trans hs
  have hc := calculation_all (encode (a (generators 0))) h1 _ h2 h3 _ h4 h5 h6
    _ h7 h8 h9 h10 hi hm
  let f := word (encode (a (generators 0))) (encode (a (generators 1)))
    (encode (a (generators 2))) (encode (a (generators 3)))
  let e : {x : B // f x = x} ≃ a.toMonoidHom.eqLocus (MonoidHom.id Model) :=
    Equiv.subtypeEquiv equiv (fun x => by
      change f x = x ↔ a (decode x) = decode x
      rw [← decode_word a x]
      exact equiv.injective.eq_iff.symm)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact count_eq_card f hc
end J2OutsideSizesCalculation
