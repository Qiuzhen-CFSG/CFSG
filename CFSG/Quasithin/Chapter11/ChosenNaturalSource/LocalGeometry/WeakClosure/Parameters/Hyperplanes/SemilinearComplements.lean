module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison
public import Mathlib.Tactic.FinCases
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.ComplementMaximality
public import Theory.FieldTheory.QuadraticFrobenius

/-!
# Semilinear corrections of orthogonal complements over the field of four elements

The Frobenius twist of a quadratic refinement of the symplectic form differs
by the square of one linear functional. A symplectic transvection corrects
that defect. On the five-dimensional orthogonal cover, the natural coordinate
and the quadratic value determine a vector, so the correction preserves the
whole field complement. Scalar and symplectic factors extend the calculation
to every semilinear natural operator.

OriginalSupplement applies this to the original binary hyperplane through
its actual central-cover map; no splitting of that quotient is required.
Source: Aschbacher--Smith, 11.2.2, printed p.767.
-/

open Matrix.PSp4Three
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SemilinearComplements
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

local notation "aa" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "bb" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "cc" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "dd" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

omit [Finite F] in
theorem quadratic_coordinates (Q : QuadraticForm F (Vector 2 F))
    (hp : Q.polarBilin = form) (x : Vector 2 F) :
    Q x = x aa * x cc + x bb * x dd +
      (Q (Matrix.PSp4Three.e 0) * (x aa)^2 + Q (Matrix.PSp4Three.e 1) * (x bb)^2 +
       Q (f 0) * (x cc)^2 + Q (f 1) * (x dd)^2) := by
  have hx : x = x aa • Matrix.PSp4Three.e 0 + x bb • Matrix.PSp4Three.e 1 + x cc • f 0 + x dd • f 1 := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [Matrix.PSp4Three.e,f]
  conv_lhs => rw [hx]
  simp only [QuadraticMap.map_add Q, ←QuadraticMap.polarBilin_apply_apply Q, hp,
    map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    Q.map_smul, smul_eq_mul, form_e_right, form_f_right]
  simp only [Matrix.PSp4Three.e,f,Pi.single_apply, if_pos, Sum.inl.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, CharTwo.neg_eq]
  norm_num
  ring

omit [CharP F 2] in
theorem fourth_power (hF : Nat.card F = 4) (x : F) : x^4=x := by
  let := Fintype.ofFinite F
  simpa only [←Nat.card_eq_fintype_card,hF] using FiniteField.pow_card x

theorem trace_square (hF : Nat.card F = 4) (x : F) : (x^2+x)^2=x^2+x := by
  rw [CharTwo.add_sq,←pow_mul,show 2*2=4 from rfl,fourth_power hF,add_comm]


def correctingVector (Q : QuadraticForm F (Vector 2 F)) : Vector 2 F :=
  Sum.elim ![(Q (f 0))^2 + Q (f 0), (Q (f 1))^2 + Q (f 1)]
    ![(Q (Matrix.PSp4Three.e 0))^2 + Q (Matrix.PSp4Three.e 0), (Q (Matrix.PSp4Three.e 1))^2 + Q (Matrix.PSp4Three.e 1)]

theorem correctingVector_value (hF : Nat.card F = 4)
    (Q : QuadraticForm F (Vector 2 F)) (hp : Q.polarBilin = form) :
    (Q (correctingVector Q))^2 = Q (correctingVector Q) := by
  rw [quadratic_coordinates Q hp]
  simp only [correctingVector, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [CharTwo.add_sq,mul_pow,trace_square hF]
  ring_nf
  have h3 : (3 : F) = 1 := by linear_combination (CharTwo.two_eq_zero (R := F))
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, h3, mul_one]


theorem frobenius_defect (hF : Nat.card F = 4)
    (Q : QuadraticForm F (Vector 2 F)) (hp : Q.polarBilin = form) (x : Vector 2 F) :
    (Q (fun i => (x i)^2))^2 = Q x + (form x (correctingVector Q))^2 := by
  rw [quadratic_coordinates Q hp (fun i => (x i)^2),quadratic_coordinates Q hp x]
  simp only [form_apply, Fin.sum_univ_two,correctingVector,Sum.elim_inl,Sum.elim_inr,
    Matrix.cons_val_zero,Matrix.cons_val_one,CharTwo.sub_eq_add]
  simp only [CharTwo.add_sq,mul_pow,trace_square hF,←pow_mul,show 2*2=4 from rfl,fourth_power hF]
  ring_nf
  simp only [CharTwo.two_eq_zero,mul_zero,add_zero]

omit [CharP F 2] in
theorem exists_nonbinary (hF : Nat.card F = 4) : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hh : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ,←Nat.card_eq_fintype_card,hF]
    have := Finset.card_le_two (a := (0 : F)) (b := 1)
    omega
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hh
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha
  exact ⟨a,ha⟩

theorem exists_correction_parameter (hF : Nat.card F = 4) (q : F) (hq : q^2=q) :
    ∃ t : F, t^2*q+t=1 := by
  rcases eq_zero_or_one_of_sq_eq_self hq with rfl | rfl
  · exact ⟨1,by ring⟩
  obtain ⟨a,ha0,ha1⟩ := exists_nonbinary hF
  have hh : a*(a-1)*(a^2+a+1)=0 := by linear_combination fourth_power hF a
  have hh' : a^2+a+1=0 := (mul_eq_zero.mp hh).resolve_left (mul_ne_zero ha0 (sub_ne_zero.mpr ha1))
  refine ⟨a,?_⟩
  rw [mul_one]
  exact (by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh')

theorem frobenius_corrected_by_symplectic (hF : Nat.card F = 4)
    (Q : QuadraticForm F (Vector 2 F)) (hp : Q.polarBilin = form) :
    ∃ g : Sp 2 F, ∀ x, Q (g • x) = (Q (fun i => (x i)^2))^2 := by
  obtain ⟨t,ht⟩ := exists_correction_parameter hF (Q (correctingVector Q))
    (correctingVector_value hF Q hp)
  refine ⟨transvection (correctingVector Q) t,fun x => ?_⟩
  rw [transvection_apply,ClassicalOrthogonal.Quadratic.add_smul,hp,frobenius_defect hF Q hp]
  linear_combination (form x (correctingVector Q))^2 * ht

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SemilinearComplements

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SemilinearComplements
open Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.ComplementMaximality
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
/-- The first coordinate and the odd quadratic value determine the full vector. -/
theorem cover_ext {x y : Space (K := F)} (hfirst : x.1 = y.1)
    (hform : formB 2 F x = formB 2 F y) : x = y := by
  apply Prod.ext hfirst
  apply CharTwo.sq_injective
  rw [formB_apply, formB_apply, hfirst] at hform
  exact add_left_cancel hform

def fieldCover (σ : F ≃+* F) : Space (K := F) →+ Space (K := F) where
  toFun x := (fun i => σ (x.1 i), σ x.2)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

omit [CharP F 2] [Finite F] in
theorem fieldCover_form (σ : F ≃+* F) (x : Space (K := F)) :
    formB 2 F (fieldCover σ x) = σ (formB 2 F x) := by
  simp [fieldCover, formB_apply, formD_apply, map_mul]

omit [Finite F] in
theorem mem_complement_iff (Q : Submodule F (Space (K := F)))
    (hQ : IsCompl Q radical) (x : Space (K := F)) :
    x ∈ Q ↔ formB 2 F x = naturalForm Q hQ x.1 := by
  let e := complementProjection Q hQ
  have hfirst (v : Natural (K := F)) : (e.symm v).val.1 = v := e.apply_symm_apply v
  constructor
  · intro hx
    have he : e.symm x.1 = (⟨x,hx⟩ : Q) := e.symm_apply_apply ⟨x,hx⟩
    change formB 2 F x = formB 2 F (e.symm x.1).val
    rw [he]
  · intro hx
    have he : x = (e.symm x.1).val := cover_ext (hfirst _).symm hx
    exact he.symm ▸ (e.symm x.1).property

theorem fieldAut_cases (hF : Nat.card F = 4) (σ : F ≃+* F) :
    σ = 1 ∨ σ = frobeniusEquiv F 2 := by
  by_cases h : σ = 1
  · exact Or.inl h
  right
  apply FiniteField.involution_eq_frobenius_of_card_square (by simpa using hF)
  exact orderOf_eq_prime
    (FiniteField.ringAut_sq_of_card_prime_pow (by decide : Nat.Prime 2)
      (by decide : 2 ≤ 2) (by simpa using hF) σ) h

theorem fieldCover_correction (hF : Nat.card F = 4)
    (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical)
    (σ : F ≃+* F) :
    ∃ g : Sp 2 F, ∀ x ∈ Q, fullAction g (fieldCover σ x) ∈ Q := by
  rcases fieldAut_cases hF σ with rfl | rfl
  · refine ⟨1,fun x hx => ?_⟩
    have he : fieldCover (1 : F ≃+* F) x = x := rfl
    simpa only [map_one, Module.End.one_apply, he] using hx
  · obtain ⟨g,hg⟩ := frobenius_corrected_by_symplectic hF
      (naturalForm Q hQ) (naturalForm_polar Q hQ)
    refine ⟨g, fun x hx => ?_⟩
    apply (mem_complement_iff Q hQ _).mpr
    rw [fullAction_preserves, fieldCover_form]
    change (formB 2 F x)^2 = naturalForm Q hQ (g • (fun i => (x.1 i)^2))
    rw [hg]
    have he : (fun i => ((x.1 i)^2)^2) = x.1 := by
      funext i
      rw [←pow_mul, show 2*2=4 from rfl, fourth_power hF]
    rw [he, (mem_complement_iff Q hQ x).mp hx]

variable [Algebra (ZMod 2) F]

def semilinearCover (a : Fˣ) (g : Sp 2 F) (σ : F ≃+* F) :
    Space (K := F) →ₗ[ZMod 2] Space (K := F) :=
  (((a.val • fullAction g).restrictScalars (ZMod 2)).comp
    ((fieldCover σ).toZModLinearMap 2))

theorem semilinearCover_first (a : Fˣ) (g : Sp 2 F) (σ : F ≃+* F)
    (x : Space (K := F)) :
    (semilinearCover a g σ x).1 = a.val • (g • (fun i => σ (x.1 i))) := rfl

theorem semilinearCover_form (a : Fˣ) (g : Sp 2 F) (σ : F ≃+* F)
    (x : Space (K := F)) :
    formB 2 F (semilinearCover a g σ x) = a.val^2 * σ (formB 2 F x) := by
  change formB 2 F (a.val • fullAction g (fieldCover σ x)) = _
  rw [QuadraticMap.map_smul, smul_eq_mul, fullAction_preserves, fieldCover_form]
  ring

theorem semilinearCover_correction (hF : Nat.card F = 4)
    (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical)
    (a : Fˣ) (g : Sp 2 F) (σ : F ≃+* F) :
    ∃ k : Sp 2 F, ∀ x ∈ Q, fullAction k (semilinearCover a g σ x) ∈ Q := by
  obtain ⟨h,hh⟩ := fieldCover_correction hF Q hQ σ
  refine ⟨h * g⁻¹, fun x hx => ?_⟩
  change fullAction (h*g⁻¹) (a.val • fullAction g (fieldCover σ x)) ∈ Q
  rw [map_smul, ←Module.End.mul_apply, ←map_mul, inv_mul_cancel_right]
  exact Q.smul_mem a.val (hh x hx)

/-- The explicit lift intertwines every pair of operators intertwined downstairs. -/
theorem semilinearCover_intertwines (a : Fˣ) (g l l' : Sp 2 F) (σ : F ≃+* F)
    (he : ∀ v : Natural (K := F),
      a.val • (g • (fun i => σ ((l • v) i))) =
        l' • (a.val • (g • (fun i => σ (v i)))))
    (x : Space (K := F)) :
    semilinearCover a g σ (fullAction l x) =
      fullAction l' (semilinearCover a g σ x) := by
  apply cover_ext
  · exact he x.1
  · rw [semilinearCover_form, fullAction_preserves, fullAction_preserves,
      semilinearCover_form]
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SemilinearComplements
