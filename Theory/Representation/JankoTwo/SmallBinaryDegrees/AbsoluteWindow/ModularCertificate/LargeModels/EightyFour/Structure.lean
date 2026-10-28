module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour.OrbitChecks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Descent
import Mathlib.Tactic.NoncommRing

/-!
# The degree-84 rank-one certificate and presentation relations

The ATLAS generator pair satisfies all five literal relators. The checked
constant-first degree-83 polynomial in the recorded algebra element is vλ.
Its column and row orbits span, as certified by both basis inverses. Therefore
the generated algebra is the full matrix algebra over every field of
characteristic two. No characteristic-polynomial or irreducibility answer is
used. Source and original data: LargeModels/source/README.md.
-/

@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
open Binary Matrix
open Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization
universe u
variable (F : Type u) [Field F] [CharP F 2]

theorem a_squared : (eval F 84 a) ^ 2 = 1 := by
  rw [pow_two, chain_0, one_eq]

theorem b_cubed : (eval F 84 b) ^ 3 = 1 := by
  rw [pow_succ', pow_two, chain_1, chain_2, one_eq]

private theorem power_seven {M : Type*} [Monoid M] (x : M) :
    x ^ 7 = (x * x * x) * (x * x * x) * x := by
  simp only [← pow_two, ← pow_succ, ← pow_mul]

private theorem power_six {M : Type*} [Monoid M] (x : M) :
    x ^ 6 = (x * x * x) * (x * x * x) := by
  simp only [← pow_two, ← pow_succ, ← pow_mul]

private theorem power_twelve {M : Type*} [Monoid M] (x : M) :
    x ^ 12 = ((x * x * x) * (x * x * x)) * ((x * x * x) * (x * x * x)) := by
  simp only [← pow_two, ← pow_succ, ← pow_mul]

theorem ab_seventh : (eval F 84 a * eval F 84 b) ^ 7 = 1 := by
  rw [chain_3, power_seven, chain_4, chain_5, chain_6, chain_7, one_eq]

theorem comm_twelfth :
    (eval F 84 a * eval F 84 bb * eval F 84 a * eval F 84 b) ^ 12 = 1 := by
  rw [chain_8, chain_9, chain_10, power_twelve, chain_11, chain_12, chain_13,
    chain_14, one_eq]

theorem long_sixth :
    (eval F 84 a * eval F 84 b * eval F 84 a * eval F 84 b * eval F 84 a *
      eval F 84 bb * eval F 84 a * eval F 84 b * eval F 84 a * eval F 84 bb) ^ 6 = 1 := by
  have hw : eval F 84 a * eval F 84 b * eval F 84 a * eval F 84 b * eval F 84 a *
      eval F 84 bb * eval F 84 a * eval F 84 b * eval F 84 a * eval F 84 bb =
      (eval F 84 a * eval F 84 b) * (eval F 84 a * eval F 84 b) * eval F 84 a *
      eval F 84 bb * (eval F 84 a * eval F 84 b) * eval F 84 a * eval F 84 bb := by
    simp only [mul_assoc]
  rw [hw, chain_3, chain_4, chain_15, chain_16, chain_17, chain_18, chain_19,
    power_six, chain_20, chain_21, chain_22, one_eq]

def unitA : (Matrix (Fin 84) (Fin 84) F)ˣ :=
  ⟨eval F 84 a, eval F 84 a,
    by simpa only [pow_two] using a_squared F,
    by simpa only [pow_two] using a_squared F⟩

def unitB : (Matrix (Fin 84) (Fin 84) F)ˣ :=
  ⟨eval F 84 b, eval F 84 bb,
    (chain_2 F).trans (one_eq F),
    _root_.mul_eq_one_comm.mp ((chain_2 F).trans (one_eq F))⟩

/-- All five relators use the literal ATLAS inverses and word convention. -/
theorem relations : Presentation.Relations (unitA F) (unitB F) := by
  intro i
  apply Units.ext
  fin_cases i
  · exact a_squared F
  · exact b_cubed F
  · exact ab_seventh F
  · exact comm_twelfth F
  · exact long_sixth F

/-- The nonzero terms in the discovery record's literal algebra-word sum. -/
def sourceAlgebraElement {R : Type*} [Semiring R] (A B : R) : R :=
  B * A * A * A * A * B * A + B + A * A * A * B * A * B * A * A + A * A +
    B * A * B * B * A + B * A * B * A * B * B

theorem algebraElement_eq_source :
    sourceAlgebraElement (eval F 84 a) (eval F 84 b) = eval F 84 algebraElement := by
  have hI (M : Matrix (Fin 84) (Fin 84) F) : eval F 84 one * M = M := by
    rw [one_eq, one_mul]
  simp only [sourceAlgebraElement, algebraElement, chain_0 F, chain_1 F, chain_3 F, chain_15 F,
    chain_23 F, chain_24 F, chain_25 F, chain_26 F, chain_27 F, chain_28 F,
    chain_29 F, chain_30 F, chain_31 F, chain_32 F, chain_33 F, chain_34 F,
    chain_35 F, chain_36 F, chain_37 F, chain_38 F, chain_39 F, hI]

/-- The source polynomial, with its nonzero constant-first coefficients. -/
def polynomialValue {R : Type*} [Ring R] (T : R) : R :=
  1 + T ^ 3 + T ^ 9 + T ^ 10 + T ^ 12 + T ^ 13 + T ^ 14 +
    T ^ 15 + T ^ 16 + T ^ 17 + T ^ 19 + T ^ 21 + T ^ 25 + T ^ 31 +
    T ^ 32 + T ^ 35 + T ^ 38 + T ^ 39 + T ^ 47 + T ^ 48 + T ^ 50 +
    T ^ 51 + T ^ 52 + T ^ 56 + T ^ 57 + T ^ 58 + T ^ 60 + T ^ 62 +
    T ^ 63 + T ^ 64 + T ^ 65 + T ^ 66 + T ^ 67 + T ^ 69 + T ^ 71 +
    T ^ 73 + T ^ 76 + T ^ 77 + T ^ 79 + T ^ 80 + T ^ 82 + T ^ 83

/-- A block-Horner expression for the same polynomial, saving dense products. -/
def blockValue {R : Type*} [Ring R] (T : R) : R :=
  ((1 + T ^ 3) + T ^ 8 *
    ((T + T ^ 2 + T ^ 4 + T ^ 5 + T ^ 6 + T ^ 7) + T ^ 8 *
    ((1 + T + T ^ 3 + T ^ 5) + T ^ 8 *
    ((T + T ^ 7) + T ^ 8 *
    ((1 + T ^ 3 + T ^ 6 + T ^ 7) + T ^ 8 *
    ((T ^ 7) + T ^ 8 *
    ((1 + T ^ 2 + T ^ 3 + T ^ 4) + T ^ 8 *
    ((1 + T + T ^ 2 + T ^ 4 + T ^ 6 + T ^ 7) + T ^ 8 *
    ((1 + T + T ^ 2 + T ^ 3 + T ^ 5 + T ^ 7) + T ^ 8 *
    ((T + T ^ 4 + T ^ 5 + T ^ 7) + T ^ 8 *
    (1 + T ^ 2 + T ^ 3)))))))))))

theorem polynomialValue_eq_blockValue {R : Type*} [Ring R] (T : R) :
    polynomialValue T = blockValue T := by
  unfold polynomialValue blockValue
  noncomm_ring

/-- Checked evaluation, independent of any characteristic-polynomial claim. -/
theorem rankOne_identity :
    polynomialValue (eval F 84 algebraElement) =
      vecMulVec (vector F 84 column) (vector F 84 row) := by
  unfold algebraElement
  have h2 : (eval F 84 m39) ^ 2 = eval F 84 t2 := by
    simpa only [pow_two] using chain_40 F
  have h3 : (eval F 84 m39) ^ 3 = eval F 84 t3 := by
    rw [pow_succ, h2]
    exact chain_41 F
  have h4 : (eval F 84 m39) ^ 4 = eval F 84 t4 := by
    rw [pow_succ, h3]
    exact chain_42 F
  have h5 : (eval F 84 m39) ^ 5 = eval F 84 t5 := by
    rw [pow_succ, h4]
    exact chain_43 F
  have h6 : (eval F 84 m39) ^ 6 = eval F 84 t6 := by
    rw [pow_succ, h5]
    exact chain_44 F
  have h7 : (eval F 84 m39) ^ 7 = eval F 84 t7 := by
    rw [pow_succ, h6]
    exact chain_45 F
  have h8 : (eval F 84 m39) ^ 8 = eval F 84 t8 := by
    rw [pow_succ, h7]
    exact chain_46 F
  rw [polynomialValue_eq_blockValue]
  unfold blockValue
  simp only [h2, h3, h4, h5, h6, h7, h8, ← one_eq F,
    chain_47 F, chain_48 F, chain_49 F, chain_50 F, chain_51 F, chain_52 F,
    chain_53 F, chain_54 F, chain_55 F, chain_56 F, chain_57 F, chain_58 F,
    chain_59 F, chain_60 F, chain_61 F, chain_62 F, chain_63 F, chain_64 F,
    chain_65 F, chain_66 F, chain_67 F, chain_68 F, chain_69 F, chain_70 F,
    chain_71 F, chain_72 F, chain_73 F, chain_74 F, chain_75 F, chain_76 F,
    chain_77 F, chain_78 F, chain_79 F, chain_80 F, chain_81 F, chain_82 F,
    chain_83 F, chain_84 F, chain_85 F, chain_86 F, chain_87 F, chain_88 F,
    chain_89 F, chain_90 F, chain_91 F]
  simpa only [rankOneMatrix] using outer_eq F

theorem algebraElement_mem (S : Subalgebra F (Matrix (Fin 84) (Fin 84) F))
    (ha : eval F 84 a ∈ S) (hb : eval F 84 b ∈ S) :
    eval F 84 algebraElement ∈ S := by
  have hone : eval F 84 one ∈ S := by rw [one_eq]; exact S.one_mem
  have hab : eval F 84 ab ∈ S := (chain_3 F) ▸ S.mul_mem ha hb
  have hab2 : eval F 84 ab2 ∈ S := (chain_4 F) ▸ S.mul_mem hab hab
  have hab3 : eval F 84 ab3 ∈ S := (chain_5 F) ▸ S.mul_mem hab2 hab
  have hab6 : eval F 84 ab6 ∈ S := (chain_6 F) ▸ S.mul_mem hab3 hab3
  have hm23 : eval F 84 m23 ∈ S := (chain_23 F) ▸ S.mul_mem hb ha
  have hm29 : eval F 84 m29 ∈ S := (chain_29 F) ▸ S.mul_mem hm23 hb
  have hm30 : eval F 84 m30 ∈ S := (chain_30 F) ▸ S.mul_mem hm29 hb
  have hm31 : eval F 84 m31 ∈ S := (chain_31 F) ▸ S.mul_mem hm30 ha
  have hm32 : eval F 84 m32 ∈ S := (chain_32 F) ▸ S.mul_mem hm29 ha
  have hm33 : eval F 84 m33 ∈ S := (chain_33 F) ▸ S.mul_mem hm32 hb
  have hm34 : eval F 84 m34 ∈ S := (chain_34 F) ▸ S.mul_mem hm33 hb
  have hm35 : eval F 84 m35 ∈ S := (chain_35 F) ▸ S.add_mem hab6 hb
  have hm36 : eval F 84 m36 ∈ S := (chain_36 F) ▸ S.add_mem hm35 hab2
  have hm37 : eval F 84 m37 ∈ S := (chain_37 F) ▸ S.add_mem hm36 hone
  have hm38 : eval F 84 m38 ∈ S := (chain_38 F) ▸ S.add_mem hm37 hm31
  have hm39 : eval F 84 m39 ∈ S := (chain_39 F) ▸ S.add_mem hm38 hm34
  exact hm39

omit [CharP F 2] in
theorem polynomialValue_mem {R : Type*} [Ring R] [Algebra F R]
    (S : Subalgebra F R) {T : R} (ht : T ∈ S) : polynomialValue T ∈ S := by
  unfold polynomialValue
  repeat' apply S.add_mem
  all_goals first | exact S.one_mem | exact S.pow_mem ht _

theorem rankOne_mem (S : Subalgebra F (Matrix (Fin 84) (Fin 84) F))
    (ha : eval F 84 a ∈ S) (hb : eval F 84 b ∈ S) :
    vecMulVec (vector F 84 column) (vector F 84 row) ∈ S := by
  rw [← rankOne_identity F]
  exact polynomialValue_mem F S (algebraElement_mem F S ha hb)


theorem left_orbit (S : Subalgebra F (Matrix (Fin 84) (Fin 84) F))
    (ha : eval F 84 a ∈ S) (hb : eval F 84 b ∈ S) (i : Fin 84) :
    ∃ W ∈ S, W.mulVec (vector F 84 column) = fun k => eval F 84 p k i :=
  column_reachable F 84 a b ta tb pt p column leftParents leftLetters
    (transpose_a F) (transpose_b F) (transpose_p F) left_orbit_check S ha hb i

theorem right_orbit (S : Subalgebra F (Matrix (Fin 84) (Fin 84) F))
    (ha : eval F 84 a ∈ S) (hb : eval F 84 b ∈ S) (i : Fin 84) :
    ∃ W ∈ S, vecMul (vector F 84 row) W = eval F 84 q i :=
  row_reachable F 84 a b q row rightParents rightLetters right_orbit_check S ha hb i

/-- The concrete generated algebra is the entire matrix algebra. -/
theorem density :
    Algebra.adjoin F ({eval F 84 a, eval F 84 b} : Set (Matrix (Fin 84) (Fin 84) F)) = ⊤ := by
  let S := Algebra.adjoin F ({eval F 84 a, eval F 84 b} : Set (Matrix (Fin 84) (Fin 84) F))
  have ha : eval F 84 a ∈ S := Algebra.subset_adjoin (by simp)
  have hb : eval F 84 b ∈ S := Algebra.subset_adjoin (by simp)
  exact top_of_rankOne S (vector F 84 column) (vector F 84 row)
    (eval F 84 p) (eval F 84 pi) (eval F 84 q) (eval F 84 qi)
    (rankOne_mem F S ha hb) (left_orbit F S ha hb) (right_orbit F S ha hb)
    (left_inverse F) (right_inverse F)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
