module
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# Coordinates for an alternating four-space with a two-dimensional radical

Split off the radical and choose bases of both two-dimensional summands.
The alternating form on the complementary plane is determined by one
nonzero value. Scaling one coordinate by this value gives the standard
rank-two form, without any restriction on the characteristic.

This is the elementary radical-complement normal form for alternating
bilinear forms. The ternary group application is
`Theory.ElementaryAbelian.TernaryAlternatingCoordinates`.
-/

@[expose] public section
open Module
namespace AlternatingForm
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem plane_formula {P : Type*} [AddCommGroup P] [Module K P]
    (B : LinearMap.BilinForm K P) (hB : B.IsAlt) (b : Module.Basis (Fin 2) K P)
    (v w : P) : B v w = B (b 0) (b 1) *
      (b.repr v 0 * b.repr w 1 - b.repr w 0 * b.repr v 1) := by
  have h10 : B (b 1) (b 0) = -B (b 0) (b 1) := (hB.neg_eq _ _).symm
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  simp only [Fin.sum_univ_two, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero, h10]
  ring

private def fourCoordinates (k : K) (hk : k ≠ 0) :
    ((Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] (Fin 4 → K) where
  toFun x := ![x.2 0,x.1 0,x.1 1,k*x.2 1]
  invFun x := (![x 1,x 2],![x 0,k⁻¹*x 3])
  left_inv x := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [hk]
  right_inv x := by ext i; fin_cases i <;> simp [hk]
  map_add' x y := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' a x := by ext i; fin_cases i <;> simp [mul_left_comm]

/-- Coordinates on a four-dimensional alternating space with radical of dimension two. -/
theorem exists_four_coordinates [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hdim : finrank K V = 4) (hrad : finrank K B.ker = 2) :
    ∃ e : V ≃ₗ[K] (Fin 4 → K),
      ∀ v w, B v w = e v 0 * e w 3 - e w 0 * e v 3 := by
  obtain ⟨P,hP⟩ := B.ker.exists_isCompl
  have hdP : finrank K P = 2 := by
    have hh := Submodule.finrank_add_eq_of_isCompl hP
    rw [hdim,hrad] at hh
    omega
  let b := Module.finBasisOfFinrankEq K P hdP
  let r := Module.finBasisOfFinrankEq K B.ker hrad
  let C := B.restrict P
  have hC : C.IsAlt := fun x => hB x
  have hpzero (x : B.ker) (y : V) : B x y = 0 := LinearMap.congr_fun x.property y
  have hz (x : V) (y : B.ker) : B x y = 0 := hB.eq_iff.mpr (hpzero y x)
  have hk : C (b 0) (b 1) ≠ 0 := by
    intro hk
    have hxker : (b 0 : V) ∈ B.ker := by
      apply LinearMap.mem_ker.mpr
      ext y
      obtain ⟨z,w,hz',hw,rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hP.codisjoint y
      change B (b 0) (z+w)=0
      rw [map_add,hz _ ⟨z,hz'⟩,zero_add]
      have hh := plane_formula C hC b (b 0) ⟨w,hw⟩
      rw [hk,zero_mul] at hh
      exact hh
    have hxzero : (b 0 : V)=0 := hP.disjoint.le_bot ⟨hxker,(b 0).property⟩
    exact b.ne_zero 0 (Subtype.ext hxzero)
  let split := (B.ker.prodEquivOfIsCompl P hP).symm
  let e := split.trans ((r.equivFun.prodCongr b.equivFun).trans
    (fourCoordinates (C (b 0) (b 1)) hk))
  refine ⟨e,?_⟩
  intro v w
  obtain ⟨v,rfl⟩ := split.symm.surjective v
  obtain ⟨w,rfl⟩ := split.symm.surjective w
  have hv : split.symm v = (v.1:V)+(v.2:V) := rfl
  have hw : split.symm w = (w.1:V)+(w.2:V) := rfl
  have he (v : B.ker × P) : e (split.symm v) =
      ![b.repr v.2 0,r.repr v.1 0,r.repr v.1 1,C (b 0) (b 1)*b.repr v.2 1] := by
    change fourCoordinates _ hk ((r.equivFun.prodCongr b.equivFun) (split (split.symm v)))=_
    rw [split.apply_symm_apply]
    rfl
  rw [he,he,hv,hw]
  simp only [map_add,LinearMap.add_apply,hpzero,hz,zero_add,add_zero]
  change C v.2 w.2 = _
  rw [plane_formula C hC b]
  dsimp
  ring
end AlternatingForm
