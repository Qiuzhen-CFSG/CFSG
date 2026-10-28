module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.Construction.StandardModel
public import Theory.LinearAlgebra.Hermitian.ProjectivePairTransport
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Concrete projective unitary generators for the Ree construction

Over `StandardField m`, write `bar` for q-Frobenius. In the antidiagonal
Hermitian form, the root matrices have rows `(1,bar a,b)`, `(0,1,a)`,
`(0,0,1)`, where `b + bar b = bar a * a`. The diagonal matrices
`diag(t,1,(bar t)⁻¹)` use every nonzero field element. Their determinant
is unrestricted, retaining the full projective unitary torus.

The matrices below are proved isometries. The existing field-and-form
transport gives an actual equivalence with the identity-Gram `StandardPGU`.
Matrix entries distinguish the identity in both proposed Bruhat forms:
the middle diagonal entry fixes the scalar in the small cell, and the
bottom-left entry excludes the identity in the big cell. Generation and
completeness of the rank-one relations are separate obligations.

These coordinates prepare Malle's projective unitary construction in
Section 2.5, manuscript pp.10–11, *The maximal subgroups of ²F₄(q²)*,
J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E.
Malle's q² is the coefficient cardinal `2^(2*m+1)` used here. His extra
cyclic group of order q²+1 is needed above the projective special subgroup.
-/

@[expose] public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction.StandardEmbedding

open Matrix BenderSuzuki.MatrixGroups
open scoped Matrix

abbrev E (m : ℕ) := StandardField m

def conjugation (m : ℕ) : E m ≃+* E m := (standardForm m).conj

@[simp] theorem conjugation_conjugation (m : ℕ) (a : E m) :
    conjugation m (conjugation m a) = a := (standardForm m).conj_involutive a

def gram (m : ℕ) : Matrix (Fin 3) (Fin 3) (E m) :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

def wittForm (m : ℕ) : HermitianForm 3 (E m) where
  conj := conjugation m
  conj_involutive := conjugation_conjugation m
  form := gram m
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [gram]
  form_nondegenerate := by simp [gram, Matrix.det_fin_three]

abbrev WittPGU (m : ℕ) := (wittForm m).unitarySubgroup.map ProjGenLinGroup.mk

theorem exists_wittProjectiveEquiv (m : ℕ) : Nonempty (WittPGU m ≃* StandardPGU m) := by
  obtain ⟨e, hu, _⟩ := HermitianForm.ProjectivePairTransport.exists_projective_pair_equiv_of_card
    (wittForm m) (standardForm m) (2 ^ (2 * m + 1))
    (standardField_card m) (standardForm_fixed_card m)
    (standardField_card m) (standardForm_fixed_card m)
  exact ⟨{
    toFun := fun x => ⟨e x, (hu x).mpr x.property⟩
    invFun := fun y => ⟨e.symm y, (hu (e.symm y)).mp (by simp only [e.apply_symm_apply]; exact y.property)⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
    map_mul' := fun x y => Subtype.ext (e.map_mul x y) }⟩

/-- The actual projective groups for the two Gram matrices are isomorphic. -/
def wittProjectiveEquiv (m : ℕ) : WittPGU m ≃* StandardPGU m :=
  (exists_wittProjectiveEquiv m).some

structure RootParameter (m : ℕ) where
  a : E m
  b : E m
  equation : b + conjugation m b = conjugation m a * a

def rootMatrix (m : ℕ) (a b : E m) : Matrix (Fin 3) (Fin 3) (E m) :=
  !![1, conjugation m a, b; 0, 1, a; 0, 0, 1]

def rootGL (m : ℕ) (a b : E m) : GL (Fin 3) (E m) :=
  GeneralLinearGroup.mkOfDetNeZero (rootMatrix m a b)
    (by simp [rootMatrix, Matrix.det_fin_three])

theorem rootGL_unitary (m : ℕ) (p : RootParameter m) :
    rootGL m p.a p.b ∈ (wittForm m).unitarySubgroup := by
  rw [HermitianForm.mem_unitarySubgroup_iff]
  change (Matrix.of fun i j => conjugation m (rootMatrix m p.a p.b j i)) * gram m *
    rootMatrix m p.a p.b = gram m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, gram, Matrix.mul_apply, Fin.sum_univ_three,
      CharTwo.add_self_eq_zero, conjugation_conjugation]
  have h := p.equation
  linear_combination (norm := ring_nf) h
  simp [CharTwo.two_eq_zero]

/-- The full projective unitary torus; no determinant-one constraint is imposed. -/
def torusMatrix (m : ℕ) (t : (E m)ˣ) : Matrix (Fin 3) (Fin 3) (E m) :=
  !![t, 0, 0; 0, 1, 0; 0, 0, (conjugation m (t : E m))⁻¹]

def torusGL (m : ℕ) (t : (E m)ˣ) : GL (Fin 3) (E m) :=
  GeneralLinearGroup.mkOfDetNeZero (torusMatrix m t)
    (by simp [torusMatrix, Matrix.det_fin_three, t.ne_zero])

theorem torusGL_unitary (m : ℕ) (t : (E m)ˣ) :
    torusGL m t ∈ (wittForm m).unitarySubgroup := by
  rw [HermitianForm.mem_unitarySubgroup_iff]
  change (Matrix.of fun i j => conjugation m (torusMatrix m t j i)) * gram m *
    torusMatrix m t = gram m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMatrix, gram, Matrix.mul_apply, Fin.sum_univ_three, t.ne_zero]

def weylGL (m : ℕ) : GL (Fin 3) (E m) :=
  GeneralLinearGroup.mkOfDetNeZero (gram m) (by simp [gram, Matrix.det_fin_three])

theorem weylGL_unitary (m : ℕ) : weylGL m ∈ (wittForm m).unitarySubgroup := by
  rw [HermitianForm.mem_unitarySubgroup_iff]
  change (Matrix.of fun i j => conjugation m (gram m j i)) * gram m * gram m = gram m
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, Matrix.mul_apply, Fin.sum_univ_three]

def root (m : ℕ) (p : RootParameter m) : WittPGU m :=
  ⟨ProjGenLinGroup.mk (rootGL m p.a p.b),
    Subgroup.mem_map.mpr ⟨_, rootGL_unitary m p, rfl⟩⟩

def torus (m : ℕ) (t : (E m)ˣ) : WittPGU m :=
  ⟨ProjGenLinGroup.mk (torusGL m t),
    Subgroup.mem_map.mpr ⟨_, torusGL_unitary m t, rfl⟩⟩

def weyl (m : ℕ) : WittPGU m :=
  ⟨ProjGenLinGroup.mk (weylGL m), Subgroup.mem_map.mpr ⟨_, weylGL_unitary m, rfl⟩⟩

def RootParameter.zero (m : ℕ) : RootParameter m := ⟨0, 0, by simp⟩

def RootParameter.mul {m : ℕ} (p q : RootParameter m) : RootParameter m where
  a := p.a + q.a
  b := p.b + q.b + conjugation m p.a * q.a
  equation := by
    simp only [map_add, map_mul, conjugation_conjugation]
    linear_combination p.equation + q.equation

def RootParameter.scale {m : ℕ} (t : (E m)ˣ) (p : RootParameter m) : RootParameter m where
  a := conjugation m (t : E m) * p.a
  b := (t : E m) * conjugation m (t : E m) * p.b
  equation := by
    simp only [map_mul, conjugation_conjugation]
    linear_combination (t : E m) * conjugation m (t : E m) * p.equation

def RootParameter.bruhatLeft {m : ℕ} (p : RootParameter m) (hb : p.b ≠ 0) :
    RootParameter m where
  a := p.a / p.b
  b := p.b⁻¹
  equation := by
    simp only [map_inv₀, map_div₀]
    have hcb : conjugation m p.b ≠ 0 := (map_ne_zero (conjugation m)).mpr hb
    field_simp
    linear_combination p.equation

def RootParameter.bruhatRight {m : ℕ} (p : RootParameter m) (hb : p.b ≠ 0) :
    RootParameter m where
  a := p.a / conjugation m p.b
  b := p.b⁻¹
  equation := by
    simp only [map_inv₀, map_div₀, conjugation_conjugation]
    have hcb : conjugation m p.b ≠ 0 := (map_ne_zero (conjugation m)).mpr hb
    field_simp
    linear_combination p.equation

/-- The diagonal parameter in the projective Bruhat relation. At the GL level
the corresponding right-hand product differs by the scalar `b / bar b`. -/
def bruhatTorus {m : ℕ} (p : RootParameter m) (hb : p.b ≠ 0) : (E m)ˣ :=
  Units.mk0 (p.b / conjugation m p.b ^ 2) (by simp [hb])

def conjugateInverse {m : ℕ} (t : (E m)ˣ) : (E m)ˣ :=
  (Units.map (conjugation m).toMonoidHom t)⁻¹

inductive Generator (m : ℕ) where
  | root (p : RootParameter m)
  | torus (t : (E m)ˣ)
  | weyl

abbrev Word (m : ℕ) := FreeGroup (Generator m)

def rootWord {m : ℕ} (p : RootParameter m) : Word m := FreeGroup.of (.root p)
def torusWord {m : ℕ} (t : (E m)ˣ) : Word m := FreeGroup.of (.torus t)
def weylWord (m : ℕ) : Word m := FreeGroup.of .weyl

def unitaryGenerator (m : ℕ) : Generator m → WittPGU m
  | .root p => root m p
  | .torus t => torus m t
  | .weyl => weyl m

def unitaryEval (m : ℕ) : Word m →* WittPGU m := FreeGroup.lift (unitaryGenerator m)

@[simp] theorem root_zero (m : ℕ) : root m (RootParameter.zero m) = 1 := by
  apply Subtype.ext
  change ProjGenLinGroup.mk (rootGL m 0 0) = 1
  have h : rootGL m 0 0 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rootGL, rootMatrix]
  rw [h, map_one]

@[simp] theorem torus_one (m : ℕ) : torus m 1 = 1 := by
  apply Subtype.ext
  change ProjGenLinGroup.mk (torusGL m 1) = 1
  have h : torusGL m 1 = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusGL, torusMatrix]
  rw [h, map_one]

theorem root_torus_eq_one {m : ℕ} (p : RootParameter m) (t : (E m)ˣ)
    (h : root m p * torus m t = 1) : p.a = 0 ∧ p.b = 0 ∧ t = 1 := by
  have hx := congrArg Subtype.val h
  change ProjGenLinGroup.mk (rootGL m p.a p.b) * ProjGenLinGroup.mk (torusGL m t) = 1 at hx
  rw [← map_mul, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hx
  obtain ⟨c, hc⟩ := hx
  have hc' := congrArg (fun A : GL (Fin 3) (E m) => (A : Matrix (Fin 3) (Fin 3) (E m))) hc
  have hmiddle := congrFun (congrFun hc' 1) 1
  have hc1 : (c : E m) = 1 := by
    simpa [rootGL, rootMatrix, torusGL, torusMatrix, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_three] using hmiddle
  have ht := congrFun (congrFun hc' 0) 0
  have ht1 : t = 1 := Units.ext (by
    simpa [rootGL, rootMatrix, torusGL, torusMatrix, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_three, hc1] using ht.symm)
  subst t
  have ha := congrFun (congrFun hc' 1) 2
  have hb := congrFun (congrFun hc' 0) 2
  refine ⟨?_, ?_, rfl⟩
  · simpa [rootGL, rootMatrix, torusGL, torusMatrix, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_three] using ha.symm
  · simpa [rootGL, rootMatrix, torusGL, torusMatrix, GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_three] using hb.symm

theorem bigCell_ne_one {m : ℕ} (p q : RootParameter m) (t : (E m)ˣ) :
    root m p * torus m t * weyl m * root m q ≠ 1 := by
  intro h
  have hx := congrArg Subtype.val h
  change ProjGenLinGroup.mk (rootGL m p.a p.b) * ProjGenLinGroup.mk (torusGL m t) *
    ProjGenLinGroup.mk (weylGL m) * ProjGenLinGroup.mk (rootGL m q.a q.b) = 1 at hx
  rw [← map_mul, ← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar] at hx
  obtain ⟨c, hc⟩ := hx
  have he := congrArg (fun A : GL (Fin 3) (E m) => A 2 0) hc
  have hzero : (conjugation m (t : E m))⁻¹ = 0 := by
    simpa [rootGL, rootMatrix, torusGL, torusMatrix, weylGL, gram,
      GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_three] using he.symm
  exact (inv_ne_zero ((map_ne_zero (conjugation m)).mpr t.ne_zero)) hzero

end ReeF4.MaximalSubgroups.SimpleNormal.Construction.StandardEmbedding
