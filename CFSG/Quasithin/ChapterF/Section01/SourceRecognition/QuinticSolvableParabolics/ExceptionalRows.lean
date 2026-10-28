module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.ClassicalRows
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.QuinticBinaryConsumers
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.Catalogue

/-!
# Reversed exceptional rows cannot have a quintic first endpoint

The reversed comparison identifies the original first endpoint with the
model's full second parabolic. In six rows its actual two-core quotient
is PSL₂(2); the inclusion-induced original local quotient embedding rules
this out. The two Hall–Janko second parabolics have orders 1152 and 2304,
which are prime to five. The latter order follows from adjoining the
specified outer involution to the same embedded inner parabolic.

Only the supplied parabolic equivalence is used. Its compatibility is
never strengthened to an amalgam isomorphism. The other orientation has
a solvable right endpoint, used in the final catalogue application.

Source: Aschbacher–Smith F.1.12(I)(8)–(13), pp.262–264, with the concrete
Tits correction; DGS Theorem A, pp.99–100 and (15.3), pp.229–231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
open DGS85.OriginalExtension DGS85.Assembly.BinaryQuotients GreenBook
variable {G : Type*} [Group G] {K R S : Subgroup G}

private theorem no_binary_left_model (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5)
    {X : Type*} [Group X]
    (e : parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) 0 ≃* X)
    (hx : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 2) : False := by
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := hx
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hc : ClassicalGroup.IsPSL
      (parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) 0 ⧸
        pCore 2 (parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) 0)) 2 2 :=
    ⟨F,inferInstance,inferInstance,hF,⟨q.trans f⟩⟩
  rw [h.quintic_reducedSylow_eq hSK] at hc
  exact quintic_no_binary_full_left h hSK hi hc

private theorem no_psl_two_left_model (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5)
    {X : Type*} [Group X]
    (e : parabolic ![K,R] (SuzukiContainment.reducedSylow ![K,R] S) 0 ≃* X)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (f : (X ⧸ pCore 2 X) ≃* PSL(2,F)) : False :=
  no_binary_left_model h hSK hi e ⟨F,inferInstance,inferInstance,hF,⟨f⟩⟩

/-- All eight exceptional rows in the reversed orientation contradict the actual quintic quotient or order. -/
theorem not_reversed_exceptional (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) (c : ExceptionalModels.Case)
    (he : ExceptionalModels.ParabolicModel c (reducedAmalgam ![K,R] S).reverse) : False := by
  cases c with
  | g2Derived =>
    obtain ⟨e⟩ := he
    exact no_psl_two_left_model h hSK hi e.right (by simp)
      Atlas.G2.ExceptionalLocalQuotients.derivedSecondQuotientEquiv
  | g2Full =>
    obtain ⟨e⟩ := he
    exact no_psl_two_left_model h hSK hi e.right (by simp)
      ExceptionalModels.G2.fullSecondQuotientEquiv
  | tits =>
    obtain ⟨e⟩ := he
    have f := Tits.ExceptionalParabolics.secondLocalFactorCoreQuotientEquiv
    rw [Tits.ExceptionalParabolics.secondLocalFactor_eq] at f
    exact no_psl_two_left_model h hSK hi e.right (by simpa using ReeF4.field_card 0) f
  | reeFull =>
    obtain ⟨e⟩ := he
    exact no_psl_two_left_model h hSK hi e.right (by simpa using ReeF4.field_card 0)
      Tits.ExceptionalParabolics.FullRee.secondCoreQuotientEquiv
  | m12 =>
    obtain ⟨e⟩ := he
    apply no_binary_left_model h hSK hi e.right
    rw [MathieuTwelve.P_eq_L]
    exact MathieuTwelve.local_calculations.2.2.1
  | autM12 =>
    obtain ⟨e⟩ := he
    let f := e.right.trans AutMathieuTwelve.ambientIso.right.symm
    apply no_binary_left_model h hSK hi f
    rw [AutMathieuTwelve.P_eq_L]
    exact AutMathieuTwelve.local_calculations.2.2.2.2.1
  | j2 =>
    obtain ⟨e⟩ := he
    have hd := model_left_five_dvd h hSK hi e.right
    rw [HallJanko.j2Model_P_one,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer.card_p₂] at hd
    norm_num at hd
  | autJ2 =>
    obtain ⟨e⟩ := he
    let f := e.right.trans HallJanko.extensionAutAmalgamIso.right.symm
    have hd := model_left_five_dvd h hSK hi f
    rw [HallJanko.extensionModel_P_one] at hd
    open Sporadic.LeechRelated.J2.ExceptionalParabolics in
      rw [card_sup_zpowers_of_normalizing_involution _ _ SecondParabolic.outerElement_sq
        (fun hh => SecondParabolic.outerElement_not_mem_range ((Seed.p₂.map_le_range intoExtension) hh))
        SecondParabolic.Overlap.outerElement_normalizes_p₂,
        card_map_of_injective SecondParabolic.intoExtension_injective, PairNormalizer.card_p₂] at hd
    norm_num at hd

end CFSG.Quasithin.ChapterF.Source.QuinticSolvableParabolics
