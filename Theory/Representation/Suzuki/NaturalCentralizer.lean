module
public import Theory.Representation.Suzuki.NaturalMatrix

/-!
# The scalar commutant of the natural Suzuki module

The root-fixed line and its Weyl conjugate determine the first and last
coordinate maps of a commuting additive endomorphism. Central root matrices
determine the other two maps and force scalar multiplication by the same
field element. This holds on the literal binary natural module.

Consumer: the original central Hall action in Aschbacher--Smith 10.2.3.
Source: Huppert--Blackburn, Finite Groups III, XI.3.1; Aschbacher--Smith,
10.1.2(5) and 10.2.3, printed pp.742,745.
-/

public noncomputable section

open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII Subgroup
namespace Representation.SuzukiNatural
private def root (m : ℕ) (a b : F m) : SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m a b, subset_closure (Or.inl ⟨a,b,rfl⟩)⟩
private def weyl (m : ℕ) : SuzukiMatrixGroup m :=
  ⟨SuzukiWeylGL m, subset_closure (Or.inr (Or.inr rfl))⟩
private def axis (m : ℕ) (i : Fin 4) (a : F m) : W m := Pi.single i a
private theorem weyl_apply (m : ℕ) (v : W m) :
    natural m (weyl m) v = ![v 3,v 2,v 1,v 0] := by
  ext i
  fin_cases i <;> simp [natural_apply,weyl,SuzukiWeylGL,SuzukiWeylMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four]
private theorem root_apply (m : ℕ) (a b : F m) (v : W m) :
    natural m (root m a b) v =
      ![v 0 + a * v 1 + b * v 2 +
          (a ^ (2 + 2 ^ (m+1)) + a*b + b ^ (2 ^ (m+1))) * v 3,
        v 1 + a ^ (2 ^ (m+1)) * v 2 + (a ^ (1 + 2 ^ (m+1))+b) * v 3,
        v 2 + a * v 3, v 3] := by
  ext i
  fin_cases i <;> simp [natural_apply,root,SuzukiRootGL,SuzukiRootMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_four,add_assoc]
private theorem root_fixed_axis (m : ℕ) (x : F m) (a b : F m) :
    natural m (root m a b) (axis m 0 x) = axis m 0 x := by
  rw [root_apply]
  ext i
  fin_cases i <;> simp [axis]
private theorem fixed_axis (m : ℕ) (v : W m)
    (h : ∀ a b, natural m (root m a b) v = v) : v = axis m 0 (v 0) := by
  have h01 := h 0 1
  rw [root_apply] at h01
  have h3 : v 3 = 0 := by
    have hh := congrFun h01 1
    simpa using hh
  have h2 : v 2 = 0 := by
    have hh := congrFun h01 0
    simpa [h3] using hh
  have h1 : v 1 = 0 := by
    have hh := congrFun (h 1 0) 0
    rw [root_apply] at hh
    simpa [h2,h3] using hh
  ext i
  fin_cases i <;> simp [axis,h1,h2,h3]
private theorem weyl_axis (m : ℕ) (x : F m) (i : Fin 4) :
    natural m (weyl m) (axis m i x) = axis m (3-i) x := by
  rw [weyl_apply]
  ext j
  fin_cases i <;> fin_cases j <;> simp [axis]
private theorem root_last (m : ℕ) (x : F m) :
    natural m (root m 0 1) (axis m 3 x) =
      axis m 0 x + axis m 1 x + axis m 3 x := by
  rw [root_apply]
  ext i
  fin_cases i <;> simp [axis]
private theorem root_third (m : ℕ) (x b : F m) :
    natural m (root m 0 b) (axis m 2 x) = axis m 0 (b*x) + axis m 2 x := by
  rw [root_apply]
  ext i
  fin_cases i <;> simp [axis]

/-- Every additive endomorphism commuting with the natural Suzuki action is a scalar. -/
theorem commuting_addHom_eq_scalar (m : ℕ) (f : W m →+ W m)
    (hf : ∀ g v, f (natural m g v) = natural m g (f v)) :
    ∃ a : F m, ∀ v, f v = a • v := by
  let φ (x : F m) := f (axis m 0 x) 0
  have h0 (x : F m) : f (axis m 0 x) = axis m 0 (φ x) := by
    apply fixed_axis
    intro a b
    rw [←hf,root_fixed_axis]
  have h3 (x : F m) : f (axis m 3 x) = axis m 3 (φ x) := by
    have hh := hf (weyl m) (axis m 0 x)
    rw [weyl_axis,h0,weyl_axis] at hh
    exact hh
  have h1 (x : F m) : f (axis m 1 x) = axis m 1 (φ x) := by
    have hh := hf (root m 0 1) (axis m 3 x)
    rw [root_last,map_add,map_add,h0,h3,root_last] at hh
    exact add_left_cancel (add_right_cancel hh)
  have h2 (x : F m) : f (axis m 2 x) = axis m 2 (φ x) := by
    have hh := hf (weyl m) (axis m 1 x)
    rw [weyl_axis,h1,weyl_axis] at hh
    exact hh
  have hmul (x b : F m) : φ (b*x) = b * φ x := by
    have hh := hf (root m 0 b) (axis m 2 x)
    rw [root_third,map_add,h0,h2,root_third] at hh
    have hh' := congrFun hh 0
    simpa [axis] using hh'
  refine ⟨φ 1,?_⟩
  intro v
  have hv : v = axis m 0 (v 0) + axis m 1 (v 1) + axis m 2 (v 2) + axis m 3 (v 3) := by
    ext i
    fin_cases i <;> simp [axis]
  conv_lhs => rw [hv]
  rw [map_add,map_add,map_add,h0,h1,h2,h3]
  have he (x : F m) : φ x = x * φ 1 := by simpa using hmul 1 x
  rw [he (v 0),he (v 1),he (v 2),he (v 3)]
  ext i
  fin_cases i <;> simp [axis,mul_comm]
/-- The full root subgroup fixes precisely the first coordinate line. -/
theorem root_fixed_coordinates (m : ℕ) (v : W m)
    (hv : ∀ g ∈ SuzukiRootSubgroup m, natural m g v = v) :
    v = ![v 0,0,0,0] := by
  have hh := fixed_axis m v (fun a b => hv (root m a b)
    ((mem_suzukiRootSubgroup_iff m _).mpr ⟨a,b,rfl⟩))
  rw [hh]
  ext i
  fin_cases i <;> simp [axis]

end Representation.SuzukiNatural
