module
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.RankOneSections.Exclusion
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The Hermitian quotient cannot be an outer section above field four

For n > 1 the order of PSL3(2^(2n)) does not divide |GL8(2)|. The cases n = 2,3
use exact orders; for n >= 4 even the scalar-kernel lower bound exceeds |GL8(2)|.
The complete Theorem B outer profile is either solvable or has a Sylow Frattini
quotient of order at most 256. It therefore excludes this nonsolvable simple
quotient from the outer group. Perfect central descent preserves the conclusion
for the original quasisimple cover.

The Chapter 12 OddNormalizers extension applies this to the actual selected
component. No claim for n = 1 is made: the field-four order divides |GL8(2)|.
The remaining ambient arguments belong to qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith, 4.4.10--11, printed p.621 (refs/quasithin.pdf),
using the existing Theorem B model inspection and exact projective matrix order.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections

/-- For half-degree greater than one, the actual Hermitian component quotient
cannot occur as a section of GL8(2). The field-four endpoint is not asserted. -/
theorem linearThree_order_not_dvd_GL_eight
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^(2*n)) :
    ¬ Nat.card PSL(3,F) ∣ 5348063769211699200 := by
  rw [Matrix.PSL3.LinearThree.card_projective,hF]
  intro hd
  have hn4 : n < 4 := by
    by_contra! h
    have hq : 256 ≤ 2^(2*n) :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 8 ≤ 2*n)
    have hnum := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have hden : Nat.gcd 3 (2^(2*n)-1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hb := (Nat.div_le_div_right hnum (c := 3)).trans
      (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
    have hb' : 5348063769211699200 <
        ((2^(2*n))^3 * ((2^(2*n))^3-1) * ((2^(2*n))^2-1)) /
          Nat.gcd 3 (2^(2*n)-1) := lt_of_lt_of_le (by norm_num) hb
    exact (not_lt_of_ge (Nat.le_of_dvd (by norm_num) hd)) hb'
  interval_cases n <;> norm_num at hd

private theorem simple_no_hermitian_section
    {S Q F : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    [Group Q] [Finite Q] [IsSimpleGroup Q] [Field F] [Finite F]
    (hna : ¬ IsMulCommutative S) (hm : ChapterA.Section02.IsTheoremBModel S)
    (hQ : ¬ Group.IsSolvable Q) (eQ : Q ≃* PSL(3,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^(2*n))
    (U : Subgroup (MulAut.Outer S)) (f : U →* Q) : ¬ Function.Surjective f := by
  intro hf
  rcases model_profile hna hm with hsol | ⟨P,hP⟩
  · let : Group.IsSolvable (MulAut.Outer S) := hsol
    exact hQ (Group.isSolvable_of_surjective hf)
  · let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
      ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
    have hd := MulAut.simple_outer_section_card_dvd_GL_eight P hP hQ U f hf
    rw [Nat.card_congr eQ.toEquiv] at hd
    exact linearThree_order_not_dvd_GL_eight hn hF hd

/-- No component outer group has the original PSL3(2^(2n)) quotient as a
section for n > 1. The original quasisimple cover is retained. -/
theorem no_hermitian_outer_section
    {K Q F : Type*} [Group K] [Finite K] [IsQuasisimple K]
    [Group Q] [Finite Q] [IsSimpleGroup Q] [Field F] [Finite F]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (hQ : ¬ Group.IsSolvable Q) (eQ : Q ≃* PSL(3,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^(2*n))
    (U : Subgroup (MulAut.Outer K)) (f : U →* Q) : ¬ Function.Surjective f := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let e := MulEquiv.refl (K ⧸ center K)
  let j := MulAut.centralQuotientOuter e
  let a := U.equivMapOfInjective j (MulAut.centralQuotientOuter_injective e)
  intro hf
  exact simple_no_hermitian_section (Group.IsPerfect.not_isMulCommutative _) hm hQ eQ hn hF
    (U.map j) (f.comp a.symm.toMonoidHom) (hf.comp a.symm.surjective)

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
