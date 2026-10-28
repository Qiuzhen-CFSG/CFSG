module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.ClassicalRows
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.TrialityNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ReeNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFiveNative
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LocalGeometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.BinaryOrders
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.PlaneCore

/-!
# Twisted reduced rows at the original quintic pair

The triality arms have Borel index at least nine, while the central local
SL₂ quotient and solvable first endpoint force the binary field and index
three. For unitary four, the plane SL₂ quotient is always nonsolvable;
the point quotient forces the binary parameter, whose endpoint order is
prime to five. Generated quasithinness first restricts the entire unitary
five family to field four, where both Borel indices exceed five.

For Ree four the quintic Borel index forces parameter zero, retaining the
binary model and both orientations. Its opposite solvability is used by the
catalogue consumer. No TYPE assertion is converted to a marked comparison.

Source: Aschbacher–Smith F.1.12(I)(4)–(7), pp.263–264; DGS Theorem A,
pp.99–100 and (15.1)–(15.3), pp.226–231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
open DGS85.OriginalExtension
variable {G : Type*} [Group G] {K R S : Subgroup G}

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics in
/-- Both genuine triality orientations contradict the original quintic endpoint. -/
theorem not_triality (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5) (m : ℕ) (hm : 0 < m) (b : Bool)
    (e : Iso (reducedAmalgam ![K,R] S) (TrialityNative.amalgam m hm b)) : False := by
  have hh := model_left_index h hSK hi _ _ e.toParabolicEquiv
  rw [OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hh
  cases b
  · change (2^m)^3 + 1 = 5 at hh
    have hlo : 2 ≤ 2^m := Nat.pow_le_pow_right (n := 2) (by decide) hm
    have := Nat.pow_le_pow_left hlo 3
    omega
  · change 2^m + 1 = 5 at hh
    let P := binaryParameters m hm
    let : Group.IsSolvable (Parabolics.parabolic P .central) :=
      model_left_solvable h hSK hi e.left
    let : Group.IsSolvable (localFactor P .central) :=
      Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (localFactor_le_parabolic P .central))
    let f := (localFactorCentralQuotientEquivPSL2 P rfl).trans
      (Theory.PSL2.sl2QuotientEquiv _).symm
    have hs := sl2_card_le_two_of_solvable
      (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)
    rw [GaloisField.card P.prime P.exponent (by change m ≠ 0; omega)] at hs
    change 2^m ≤ 2 at hs
    omega

open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds in
/-- The literal full Borel index forces the binary Ree parameter. -/
theorem ree_parameter_zero (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5) (m : ℕ) (b : Bool)
    (e : Iso (reducedAmalgam ![K,R] S) (ReeNative.amalgam m b)) : m = 0 := by
  by_contra hm
  have hh := model_left_index h hSK hi _ _ e.toParabolicEquiv
  rw [SourceCompletion.borel_relIndex m (by omega)] at hh
  have hlo : 8 ≤ 2^(2*m+1) :=
    Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ 2*m+1)
  cases b
  · change 2^(2*m+1) + 1 = 5 at hh
    omega
  · change (2^(2*m+1))^2 + 1 = 5 at hh
    nlinarith

open GreenBook.LieModels.UnitaryFour in
/-- Both unitary-four orientations are excluded by their actual local quotients. -/
theorem not_unitaryFour (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K)
    (hi : S.relIndex K = 5) (m : ℕ) (hm : 1 ≤ m) (b : Bool)
    (e : Iso (reducedAmalgam ![K,R] S) (UnitaryFourNative.amalgam m hm b)) : False := by
  have hs := model_left_solvable h hSK hi e.left
  cases b
  · let : Group.IsSolvable (planeParabolic m hm) := hs
    let : Group.IsSolvable (L2 m hm) :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective (L2_le_planeParabolic m hm))
    let f := L2QuotientEquivSL2 m hm
    have hc := sl2_card_le_two_of_solvable
      (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)
    rw [GaloisField.card 2 (2*m) (by omega)] at hc
    have hlo : 4 ≤ 2^(2*m) := show 2^2 ≤ 2^(2*m) from
      Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ 2*m)
    omega
  · let : Group.IsSolvable (pointParabolic m hm) := hs
    let : Group.IsSolvable (PointLocal.ProjectiveLocal m hm) :=
      Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (PointLocal.projectiveLocal_le_pointParabolic m hm))
    let f := (PointLocal.projectiveQuotientByTwoCoreEquivPSL m hm).trans
      (Theory.PSL2.sl2QuotientEquiv _).symm
    have hc := sl2_card_le_two_of_solvable
      (Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective)
    rw [PointLocal.fixedField_card m hm] at hc
    have hm1 : m = 1 := by
      by_contra hn
      have hlo : 4 ≤ 2^m := show 2^2 ≤ 2^m from
        Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ m)
      omega
    subst m
    have hd := model_left_five_dvd h hSK hi e.left
    change 5 ∣ Nat.card (pointParabolic 1 hm) at hd
    rw [BinaryCompletion.point_card] at hd
    norm_num at hd

/-- Quasithinness of the original generated group excludes the full unitary-five family. -/
theorem not_unitaryFive [Finite G] (h : HypothesisF11 ![K,R] S)
    (hqt : IsQuasithin (generated ![K,R] S)) (hSK : S ≤ K) (hi : S.relIndex K = 5)
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : GreenBook.UnitaryFive.Model q)
    (b : Bool) (e : Iso (reducedAmalgam ![K,R] S) (UnitaryFiveNative.amalgam M b)) : False := by
  have hP (i : Fin 2) : parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) i ≤
      generated ![K,R] S := by
    apply (SuzukiContainment.reduced_parabolic_le h i).trans
    rw [← parabolics_generate ![K,R] S]
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hq4 : q = 4 := by
    cases b
    · exact M.field_size_eq_four_of_parabolic_embedding hq heven hqt
        ((inclusion (hP 1)).comp e.right.symm.toMonoidHom)
        ((inclusion_injective (hP 1)).comp e.right.symm.injective)
    · exact M.field_size_eq_four_of_parabolic_embedding hq heven hqt
        ((inclusion (hP 0)).comp e.left.symm.toMonoidHom)
        ((inclusion_injective (hP 0)).comp e.left.symm.injective)
  subst q
  have hh := model_left_index h hSK hi _ _ e.toParabolicEquiv
  cases b
  · change M.overlap.relIndex M.rightParabolic = 5 at hh
    have hj := M.overlap_rightParabolic_index
    change M.overlap.relIndex M.rightParabolic = 17 at hj
    omega
  · change M.overlap.relIndex M.leftParabolic = 5 at hh
    have hj := M.overlap_index_eq_sixtyFive
    change M.overlap.relIndex M.leftParabolic = 65 at hj
    omega

end CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
