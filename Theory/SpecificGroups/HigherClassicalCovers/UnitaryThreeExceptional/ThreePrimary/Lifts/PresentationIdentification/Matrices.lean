module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Lifts.Presentation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Marked normal forms in antidiagonal SU₄(3)

The six ternary exponents combine into two arbitrary field-nine parameters
and two trace-zero parameters. Four entries of the Hermitian preservation
equation force every upper unitriangular SU matrix into this ordered root
product. Conversely the entries recover all six exponents uniquely.

The projection to the fixed projective carrier is faithful on matrices with
top-left entry one: any scalar relating two such matrices is one. Thus this
calculation retains the literal scalar quotient and coordinate projection.
Source: GLS3 chapter 2, unitary conventions, and §6.1; the local calculation
used for Aschbacher--Smith I.1.4(5), printed p.408.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourThree.IsotropicStabilizers
@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts

abbrev Parameters := Fin 6 → Fin 3

def rootProduct (v : Parameters) : CoordinateSU :=
  rootSU 0 ^ (v 0).val * rootSU 1 ^ (v 1).val * rootSU 2 ^ (v 2).val *
    rootSU 3 ^ (v 3).val * rootSU 4 ^ (v 4).val * rootSU 5 ^ (v 5).val

def shortParameter (v : Parameters) : K := ⟨v 0, v 1⟩
def middleParameter (v : Parameters) : K := ⟨v 3, v 4⟩
def longParameter (v : Parameters) : K := ⟨0, v 2⟩
def highParameter (v : Parameters) : K := ⟨0, v 5⟩

def collectedMatrix (a b c d : K) : Mat :=
  !![1,a,a*b+c,-a*star c+d; 0,1,b,-star c; 0,0,1,-star a; 0,0,0,1]

private theorem first_pair (r s : Fin 3) :
    rootMatrix 0 ^ r.val * rootMatrix 1 ^ s.val =
      !![1,(⟨r,s⟩ : K),0,0; 0,1,0,0; 0,0,1,-star (⟨r,s⟩ : K); 0,0,0,1] := by
  fin_cases r <;> fin_cases s <;> decide +kernel
private theorem middle_pair (r s : Fin 3) :
    rootMatrix 3 ^ r.val * rootMatrix 4 ^ s.val =
      !![1,0,(⟨r,s⟩ : K),0; 0,1,0,-star (⟨r,s⟩ : K); 0,0,1,0; 0,0,0,1] := by
  fin_cases r <;> fin_cases s <;> decide +kernel
private theorem long_power (r : Fin 3) :
    rootMatrix 2 ^ r.val =
      !![1,0,0,0; 0,1,(⟨0,r⟩ : K),0; 0,0,1,0; 0,0,0,1] := by
  fin_cases r <;> decide +kernel
private theorem high_power (r : Fin 3) :
    rootMatrix 5 ^ r.val =
      !![1,0,0,(⟨0,r⟩ : K); 0,1,0,0; 0,0,1,0; 0,0,0,1] := by
  fin_cases r <;> decide +kernel

theorem rootProduct_matrix (v : Parameters) :
    (rootProduct v).val.val = collectedMatrix
      (shortParameter v) (longParameter v) (middleParameter v) (highParameter v) := by
  change rootMatrix 0 ^ (v 0).val * rootMatrix 1 ^ (v 1).val * rootMatrix 2 ^ (v 2).val *
    rootMatrix 3 ^ (v 3).val * rootMatrix 4 ^ (v 4).val * rootMatrix 5 ^ (v 5).val = _
  rw [mul_assoc (_ * _ * _) (rootMatrix 3 ^ _) (rootMatrix 4 ^ _),
    first_pair, middle_pair, long_power, high_power]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [collectedMatrix, shortParameter, middleParameter, longParameter, highParameter,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- The marked scalar quotient is faithful on matrices with top-left entry one. -/
theorem coordinateProjection_injective_at_unit_entry {g h : CoordinateSU}
    (hg : g.val.val 0 0 = 1) (hh : h.val.val 0 0 = 1)
    (he : coordinateProjection g = coordinateProjection h) : g = h := by
  have hp := coordinateEquiv.injective he
  have hpgl : ProjGenLinGroup.mk g.val = ProjGenLinGroup.mk h.val := congrArg Subtype.val hp
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hpgl
  have he00 := congrArg (fun A : GL (Fin 4) K => A.val 0 0) hu
  have hu1 : u = 1 := by
    apply Units.ext
    simpa [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar,
      Matrix.mul_diagonal, hg, hh] using he00
  apply Subtype.ext
  simpa only [hu1, map_one, mul_one] using hu

theorem rootProduct_injective : Function.Injective rootProduct := by
  intro v w he
  have hm := congrArg (fun g : CoordinateSU => g.val.val) he
  rw [rootProduct_matrix, rootProduct_matrix] at hm
  have ha : shortParameter v = shortParameter w := congrArg (fun M => M 0 1) hm
  have hb : longParameter v = longParameter w := congrArg (fun M => M 1 2) hm
  have hc : middleParameter v = middleParameter w := by
    have he := congrArg (fun M => M 1 3) hm
    change -star (middleParameter v) = -star (middleParameter w) at he
    exact star_injective (neg_injective he)
  have hd : highParameter v = highParameter w := by
    have he := congrArg (fun M => M 0 3) hm
    change -shortParameter v * star (middleParameter v) + highParameter v =
      -shortParameter w * star (middleParameter w) + highParameter w at he
    rw [ha, hc] at he
    exact add_left_cancel he
  funext i
  fin_cases i
  · exact congrArg QuadraticAlgebra.re ha
  · exact congrArg QuadraticAlgebra.im ha
  · exact congrArg QuadraticAlgebra.im hb
  · exact congrArg QuadraticAlgebra.re hc
  · exact congrArg QuadraticAlgebra.im hc
  · exact congrArg QuadraticAlgebra.im hd


private theorem trace_zero_real (t : K) (ht : star t + t = 0) : t.re = 0 := by
  have h : ∀ t : K, star t + t = 0 → t.re = 0 := by decide +kernel
  exact h t ht

private theorem upper_shape (g : CoordinateSU) (hg : g ∈ positiveGenerators) :
    g.val.val = !![1,g.val.val 0 1,g.val.val 0 2,g.val.val 0 3;
      0,1,g.val.val 1 2,g.val.val 1 3; 0,0,1,g.val.val 2 3; 0,0,0,1] := by
  obtain ⟨ht, hd⟩ := hg
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hd, ht _ _ (by decide : (0 : Fin 4) < 1),
      ht _ _ (by decide : (0 : Fin 4) < 2), ht _ _ (by decide : (0 : Fin 4) < 3),
      ht _ _ (by decide : (1 : Fin 4) < 2), ht _ _ (by decide : (1 : Fin 4) < 3),
      ht _ _ (by decide : (2 : Fin 4) < 3)]

/-- Every upper unitriangular special unitary matrix has the four root parameters. -/
private theorem upper_parameters (g : CoordinateSU) (hg : g ∈ positiveGenerators) :
    ∃ a b c d : K, star b + b = 0 ∧ star d + d = 0 ∧
      g.val.val = collectedMatrix a b c d := by
  let a := g.val.val 0 1
  let b := g.val.val 0 2
  let c := g.val.val 0 3
  let d := g.val.val 1 2
  let e := g.val.val 1 3
  let f := g.val.val 2 3
  have hshape : g.val.val = !![1,a,b,c; 0,1,d,e; 0,0,1,f; 0,0,0,1] := upper_shape g hg
  have hu := (coordinateForm.mem_specialSubgroup_iff g.val).mp g.property |>.1
  change coordinateForm.conjTranspose g.val.val * coordinateForm.form * g.val.val =
    coordinateForm.form at hu
  rw [hshape] at hu
  have h13 := congrArg (fun M : Mat => M 1 3) hu
  have h22 := congrArg (fun M : Mat => M 2 2) hu
  have h23 := congrArg (fun M : Mat => M 2 3) hu
  have h33 := congrArg (fun M : Mat => M 3 3) hu
  simp [HermitianForm.conjTranspose, coordinateForm, UnitaryFourFlag.form,
    UnitaryFourFlag.gram, UnitaryFourThree.conjugation, Matrix.mul_apply,
    Fin.sum_univ_succ, starRingEnd_apply] at h13 h22 h23 h33
  have hf : f = -star a := by linear_combination h13
  have hb : b = a*d-star e := by
    have ht := congrArg star h23
    simp only [star_add, star_mul, star_star, star_zero, hf, star_neg] at ht
    linear_combination ht
  have htrace : star (c-a*e) + (c-a*e) = 0 := by
    rw [hf] at h33
    simp only [star_neg, star_star] at h33
    simp only [star_sub, star_mul]
    linear_combination h33
  refine ⟨a, d, -star e, c-a*e, by simpa only [add_comm] using h22, htrace, ?_⟩
  rw [hshape]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [collectedMatrix, hf, hb]
  all_goals ring

/-- The six actual roots generate every matrix in the published generating set. -/
theorem positiveGenerator_normal_form (g : CoordinateSU) (hg : g ∈ positiveGenerators) :
    ∃ v : Parameters, rootProduct v = g := by
  obtain ⟨a,b,c,d,hb,hd,hm⟩ := upper_parameters g hg
  let v : Parameters := ![a.re,a.im,b.im,c.re,c.im,d.im]
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [rootProduct_matrix, hm]
  have hpa : shortParameter v = a := by
    apply QuadraticAlgebra.ext <;> rfl
  have hpb : longParameter v = b := by
    apply QuadraticAlgebra.ext
    · exact (trace_zero_real b hb).symm
    · rfl
  have hpc : middleParameter v = c := by
    apply QuadraticAlgebra.ext <;> rfl
  have hpd : highParameter v = d := by
    apply QuadraticAlgebra.ext
    · exact (trace_zero_real d hd).symm
    · rfl
  rw [hpa,hpb,hpc,hpd]

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.RootLifts
