module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.IntersectionResidual.ModelFacts
public import Theory.SpecificGroups.SL2.BinaryTetrahedralHom
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# The local prime three in odd PSL₂

Choose x² + y² = −1 over the odd prime field. The quaternion matrices
A = [0,1;−1,0] and B = [x,y;y,−x], together with
T = (−I + A − B − AB)/2, satisfy the binary tetrahedral relations.
In PSL₂ the quaternion image is a nontrivial two-group and T has order
three and normalizes that image. Its normalizer is the required two-local.
Transport through the given field and group isomorphisms supplies precisely
the odd-model prime used in Lemma 16.2.9.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.2.9, printed p.1175. The binary tetrahedral
presentation is the existing GLS3 5.2.4 construction; the matrices and
local-prime deduction here are checked directly.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.OddLinear
variable {F : Type*} [Field F]

private def a : SL(2,F) := ⟨!![0, 1; -1, 0], by simp⟩
private def b (x y : F) (h : x^2 + y^2 = -1) : SL(2,F) :=
  ⟨!![x,y; y,-x], by simp [det_fin_two]; linear_combination -h⟩
private def t (x y : F) (h : x^2 + y^2 = -1) (h2 : (2 : F) ≠ 0) : SL(2,F) :=
  ⟨!![(-1-x-y)/2, (1-y+x)/2; (-1-y+x)/2, (-1+x+y)/2], by
    simp only [Matrix.det_fin_two_of]
    field_simp
    linear_combination -2 * h⟩

private theorem relations (x y : F) (h : x^2+y^2 = -1) (h2 : (2 : F) ≠ 0) :
    (a : SL(2,F)) ^ 4 = 1 ∧ (b x y h)^2 = a^2 ∧
      b x y h * a = a⁻¹ * b x y h ∧ (t x y h h2)^3 = 1 ∧
      t x y h h2 * a * (t x y h h2)⁻¹ = b x y h * a ∧
      t x y h h2 * b x y h * (t x y h h2)⁻¹ = a⁻¹ := by
  have hinv : ((a : SL(2,F))⁻¹).val = !![0,-1;1,0] := by
    change Matrix.adjugate (a : SL(2,F)).val = _
    simp [a, adjugate_fin_two]
  have htinv : ((t x y h h2)⁻¹).val =
      !![(-1+x+y)/2, -(1-y+x)/2; -(-1-y+x)/2, (-1-x-y)/2] := by
    change Matrix.adjugate (t x y h h2).val = _
    simp [t, adjugate_fin_two]
    constructor <;> ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply Subtype.ext
  all_goals simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.SpecialLinearGroup.coe_one, hinv, htinv]
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [a,b,t, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals grind

private theorem a_projective_ne_one :
    QuotientGroup.mk' (center SL(2,F)) a ≠ 1 := by
  intro ha
  obtain ⟨r, _, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ((QuotientGroup.eq_one_iff a).mp ha)
  have he01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) he
  simp [Matrix.scalar_apply, Matrix.diagonal, a] at he01

private theorem t_projective_ne_one (x y : F) (h : x^2+y^2 = -1) (h2 : (2 : F) ≠ 0) :
    QuotientGroup.mk' (center SL(2,F)) (t x y h h2) ≠ 1 := by
  intro ht
  obtain ⟨r, _, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff (t x y h h2)).mp ht)
  have he01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) he
  have he10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) he
  simp [Matrix.scalar_apply, Matrix.diagonal, t] at he01 he10
  field_simp at he01 he10
  have : (2 : F) = 0 := by linear_combination he10 - he01
  exact h2 this

/-- The binary tetrahedral matrices give a nontrivial two-group normalized
by an element of order three in the actual projective group. -/
private theorem local_prime_of_coordinates [Finite F]
    (x y : F) (h : x^2+y^2 = -1) (h2 : (2 : F) ≠ 0) :
    IsOddLocalPrime 3 PSL(2,F) := by
  obtain ⟨ha, hb, hba, ht, hta, htb⟩ := relations x y h h2
  obtain ⟨f, hfa, _, hft⟩ :=
    GLS3.Chapter5.SchurPresentation.exists_binaryTetrahedral_hom
      (a : SL(2,F)) (b x y h) (t x y h h2) ha hb hba ht hta htb
  let E := QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
    Multiplicative (ZMod 3)
  let j : QuaternionGroup 2 →* E := SemidirectProduct.inl
  let P := j.range
  let phi : E →* PSL(2,F) := (QuotientGroup.mk' (center SL(2,F))).comp f
  let Q := P.map phi
  let s : E := SemidirectProduct.inr (Multiplicative.ofAdd 1)
  have hQne : Q ≠ ⊥ := by
    intro he
    have haQ : QuotientGroup.mk' (center SL(2,F)) a ∈ Q := by
      have hm := mem_map_of_mem phi (show j (QuaternionGroup.a 1) ∈ P from ⟨QuaternionGroup.a 1, rfl⟩)
      change QuotientGroup.mk' (center SL(2,F)) (f (j (QuaternionGroup.a 1))) ∈ Q at hm
      rwa [hfa] at hm
    rw [he, mem_bot] at haQ
    exact a_projective_ne_one haQ
  have hQ : IsPGroup 2 Q := by
    have hQuaternion : IsPGroup 2 (QuaternionGroup 2) :=
      IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
    exact (hQuaternion.of_surjective j.rangeRestrict j.rangeRestrict_surjective).map phi
  have hPn : P.Normal := by
    dsimp [P,j]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hs : phi s ∈ normalizer (Q : Set PSL(2,F)) := by
    apply P.le_normalizer_map phi
    refine ⟨s, ?_, rfl⟩
    rw [normalizer_eq_top_iff.mpr hPn]
    trivial
  have hsval : phi s = QuotientGroup.mk' (center SL(2,F)) (t x y h h2) :=
    congrArg (QuotientGroup.mk' (center SL(2,F))) hft
  have hs3 : orderOf (phi s) = 3 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · rw [hsval, ← map_pow, ht, map_one]
    · rw [hsval]
      exact t_projective_ne_one x y h h2
  refine ⟨by decide, by decide, normalizer (Q : Set PSL(2,F)),
    ⟨Q,hQne,hQ,rfl⟩, ?_⟩
  have he : orderOf (⟨phi s, hs⟩ : normalizer (Q : Set PSL(2,F))) = 3 := by
    rwa [← orderOf_coe]
  rw [← he]
  exact orderOf_dvd_natCard _

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.OddLinear


namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

/-- Every odd prime-field PSL₂ has three as a local prime. -/
theorem linear_odd_local_prime {F : Type*} [Field F] [Finite F]
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (hc : Nat.card F = r) :
    IsOddLocalPrime 3 PSL(2,F) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact r.Prime := ⟨hr⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : CharP F r := charP_of_card_eq_prime (by simpa [Nat.card_eq_fintype_card] using hc)
  have htwo : (2 : F) ≠ 0 := by
    intro he
    have hd : r ∣ 2 := (CharP.cast_eq_zero_iff F r 2).mp he
    have hr2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd
    exact (Nat.not_even_iff_odd.mpr ho) (hr2 ▸ even_two)
  obtain ⟨x,y,hxy⟩ := CharP.sq_add_sq F r (-1)
  exact OddLinear.local_prime_of_coordinates (x : F) (y : F) (by simpa using hxy) htwo

/-- The exact prime p = 3 in Lemma 16.2.9 for the odd linear alternative,
transported to the central quotient required by A.1.34. -/
theorem linear_odd_quotient_local_prime {X : Type*} [Group X] [IsQuasisimple X]
    {r : ℕ} (hr : r.Prime) (ho : Odd r) (h : ClassicalGroup.IsPSL X 2 r) :
    IsOddLocalPrime 3 (X ⧸ center X) := by
  have hc := center_eq_bot_of_linear_odd ho h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let eQ : X ⧸ center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact (linear_odd_local_prime hr ho hF).of_mulEquiv (e.symm.trans eQ.symm)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry

end
