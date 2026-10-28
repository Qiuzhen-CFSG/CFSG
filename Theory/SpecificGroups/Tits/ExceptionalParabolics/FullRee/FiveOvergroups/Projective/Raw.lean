module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Tactic

/-!
# Executable matrices for the max4 projective comparison

The field is the quadratic algebra F₅[z]/(z²-z-3). Four coefficients encode a
matrix; explicit multiplication and signed equality are proved sound for the
actual SL₂ and PSL₂ groups. This supports small kernel-checked Schreier
transfers on the literal native max4 cover without a presentation assumption.
The finite tables are witnesses; their source is the original ATLAS max4 SLP.
-/

@[expose] public section
namespace Tits.Max4Projective
instance fieldNoRoot : Fact (∀ r : ZMod 5, r^2 ≠ (3:ZMod 5)+1*r) := ⟨by decide +kernel⟩
abbrev F := QuadraticAlgebra (ZMod 5) 3 1
instance : Fintype F := Fintype.ofEquiv (ZMod 5 × ZMod 5) (QuadraticAlgebra.equivProd 3 1).symm
abbrev SL := Matrix.SpecialLinearGroup (Fin 2) F
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F
structure Raw where
  a : F
  b : F
  c : F
  d : F
  deriving DecidableEq
def Raw.matrix (x : Raw) : Matrix (Fin 2) (Fin 2) F := !![x.a,x.b;x.c,x.d]
def Raw.mul (x y : Raw) : Raw := ⟨x.a*y.a+x.b*y.c,x.a*y.b+x.b*y.d,x.c*y.a+x.d*y.c,x.c*y.b+x.d*y.d⟩
def Raw.neg (x : Raw) : Raw := ⟨-x.a,-x.b,-x.c,-x.d⟩
def Raw.det (x : Raw) : F := x.a*x.d-x.b*x.c
def Raw.one : Raw := ⟨1,0,0,1⟩
def Raw.inv (x : Raw) : Raw := ⟨x.d,-x.b,-x.c,x.a⟩
theorem Raw.matrix_mul (x y : Raw) : (x.mul y).matrix = x.matrix * y.matrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Raw.matrix,Raw.mul,Matrix.mul_apply,Fin.sum_univ_two]
theorem Raw.matrix_neg (x : Raw) : x.neg.matrix = -x.matrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl
theorem Raw.matrix_one : Raw.one.matrix = 1 := by decide +kernel
def Raw.sl (x : Raw) (h : x.det=1) : SL := ⟨x.matrix,by simpa [Raw.matrix,Raw.det] using h⟩
def pi : SL →* PSL := QuotientGroup.mk' (Subgroup.center SL)
theorem pi_neg_one : pi (-1)=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1,by simp,?_⟩
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg,Matrix.scalar_apply]
theorem projective_eq_of_matrix (x y : SL) (h : (x:Matrix (Fin 2) (Fin 2) F)=y ∨
    (x:Matrix (Fin 2) (Fin 2) F)=-(y:Matrix (Fin 2) (Fin 2) F)) : pi x=pi y := by
  rcases h with h | h
  · exact congrArg pi (Subtype.ext h)
  · have he : x=(-1)*y := by
      apply Subtype.ext
      simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one,Matrix.neg_mul,one_mul] using h
    rw [he,map_mul,pi_neg_one,one_mul]
def evalRaw {n : Nat} (gen : Fin n → Raw) : List (Fin n) → Raw
  | [] => Raw.one
  | i::w => (gen i).mul (evalRaw gen w)
theorem evalRaw_matrix {n : Nat} (gen : Fin n → Raw) (h : ∀i,(gen i).det=1)
    (w : List (Fin n)) : (evalRaw gen w).matrix =
      (Theory.GroupTheory.evalWord (fun i => (gen i).sl (h i)) w : SL) := by
  induction w with
  | nil => exact Raw.matrix_one
  | cons i w ih =>
    rw [evalRaw,Raw.matrix_mul,ih]
    rfl
theorem evalWord_pi {n : Nat} (gen : Fin n → SL) (w : List (Fin n)) :
    Theory.GroupTheory.evalWord (fun i => pi (gen i)) w = pi (Theory.GroupTheory.evalWord gen w) := by
  induction w with
  | nil => exact (map_one pi).symm
  | cons i w ih =>
    change pi (gen i) * Theory.GroupTheory.evalWord (fun i => pi (gen i)) w = _
    rw [ih,← map_mul]

theorem projective_transition {n : Nat} (g r s : Raw) (hg : g.det=1) (hr : r.det=1)
    (hs : s.det=1) (next : Fin n → Raw) (hn : ∀i,(next i).det=1) (w : List (Fin n))
    (h : g.mul r = s.mul (evalRaw next w) ∨ g.mul r = (s.mul (evalRaw next w)).neg) :
    pi (g.sl hg) * pi (r.sl hr) = pi (s.sl hs) *
      Theory.GroupTheory.evalWord (fun i => pi ((next i).sl (hn i))) w := by
  have he : pi (g.sl hg * r.sl hr) =
      pi (s.sl hs * Theory.GroupTheory.evalWord (fun i => (next i).sl (hn i)) w) := by
    apply projective_eq_of_matrix
    rcases h with h | h
    · left
      have hh := congrArg Raw.matrix h
      rw [Raw.matrix_mul,Raw.matrix_mul,evalRaw_matrix next hn] at hh
      exact hh
    · right
      have hh := congrArg Raw.matrix h
      rw [Raw.matrix_mul,Raw.matrix_neg,Raw.matrix_mul,evalRaw_matrix next hn] at hh
      exact hh
  simpa only [map_mul,← evalWord_pi] using he
end Tits.Max4Projective
