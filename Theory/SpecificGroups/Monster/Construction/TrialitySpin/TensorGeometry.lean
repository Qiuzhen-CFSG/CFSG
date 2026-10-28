module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.TensorKernel
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# The form and monomial basis on the triality tensor space

Tensor an orthonormal natural basis with the actual signed-orbit spin basis.
The source tensor form makes this basis orthonormal, hence is positive definite.
The natural and spin isometries preserve the form, and their signed basis
permutations make the tensor action monomial. These constructions take only
the natural-factor basis and action properties, independently of its geometric
halfspace realization.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.5(1), printed p. 147.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped TensorProduct
namespace Sporadic.Monster.Construction.TrialitySpin.TensorGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (F : LinearMap.BilinForm ℝ V)

/-- The source form is the tensor product of the two factor forms. -/
def form : LinearMap.BilinForm ℝ (V ⊗[ℝ] SpinSpace) := F.tmul bothAxesDomain.form

theorem form_tmul (v w : V) (s t : SpinSpace) :
    form F (v ⊗ₜ[ℝ] s) (w ⊗ₜ[ℝ] t) = F v w * bothAxesDomain.form s t := by
  change bothAxesDomain.form s t * F v w = _
  exact mul_comm _ _

variable {ι : Type*} (b : Module.Basis ι ℝ V)

/-- A transversal of the source signed vectors gives this tensor basis. -/
def basis : Module.Basis (ι × bothAxesDomain.signedOrbits.toPairing.Orbit) ℝ
    (V ⊗[ℝ] SpinSpace) := b.tensorProduct bothAxesDomain.basis

theorem basis_apply (i : ι × bothAxesDomain.signedOrbits.toPairing.Orbit) :
    basis b i = b i.1 ⊗ₜ[ℝ] bothAxesDomain.basis i.2 :=
  b.tensorProduct_apply' bothAxesDomain.basis i

variable (hb : ∀ i j, F (b i) (b j) = if i = j then 1 else 0)
include hb

theorem basis_orthonormal (i j : ι × bothAxesDomain.signedOrbits.toPairing.Orbit) :
    form F (basis b i) (basis b j) = if i = j then 1 else 0 := by
  classical
  rw [basis_apply, basis_apply, form_tmul, hb, bothAxesDomain.basis_orthonormal]
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [h₁, h₂, Prod.ext_iff]

variable [Fintype ι]
local instance : Fintype bothAxesDomain.signedOrbits.toPairing.Orbit := Fintype.ofFinite _

private theorem form_eq_sum (x y : V ⊗[ℝ] SpinSpace) :
    form F x y = ∑ i, (basis b).repr x i * (basis b).repr y i := by
  classical
  conv_lhs => rw [← (basis b).sum_repr x, ← (basis b).sum_repr y]
  simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.sum_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    basis_orthonormal F b hb]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem form_pos (x : V ⊗[ℝ] SpinSpace) (hx : x ≠ 0) : 0 < form F x x := by
  classical
  rw [form_eq_sum F b hb]
  apply (Finset.sum_pos_iff_of_nonneg (fun i _ => mul_self_nonneg ((basis b).repr x i))).2
  have hcoord : ∃ i, (basis b).repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply (basis b).repr.injective
    ext i
    exact h i
  obtain ⟨i,hi⟩ := hcoord
  exact ⟨i,Finset.mem_univ i,mul_self_pos.mpr hi⟩

omit hb
omit [Fintype ι]
variable (ρ : Representation ℝ N1 V)

/-- Factor isometries preserve the source tensor form. -/
theorem representation_isometry
    (hF : ∀ g v w, F (ρ g v) (ρ g w) = F v w)
    (g : N1) (x y : V ⊗[ℝ] SpinSpace) :
    form F (TensorKernel.representation ρ g x) (TensorKernel.representation ρ g y) =
      form F x y := by
  have he : (form F).comp (TensorKernel.representation ρ g)
      (TensorKernel.representation ρ g) = form F := by
    apply TensorProduct.ext'
    intro v s
    apply TensorProduct.ext'
    intro w t
    simp only [LinearMap.BilinForm.comp_apply,
      TensorKernel.representation, Representation.tprod_apply, TensorProduct.map_tmul,
      form_tmul, hF, SpinAction.representation_isometry]
  exact congrArg (fun H : LinearMap.BilinForm ℝ (V ⊗[ℝ] SpinSpace) => H x y) he

/-- Each tensor basis vector maps to a signed tensor basis vector. -/
theorem representation_monomial
    (hm : ∀ g i, ∃ j, ρ g (b i) = b j ∨ ρ g (b i) = -b j)
    (g : N1) (i : ι × bothAxesDomain.signedOrbits.toPairing.Orbit) :
    ∃ j, TensorKernel.representation ρ g (basis b i) = basis b j ∨
      TensorKernel.representation ρ g (basis b i) = -basis b j := by
  obtain ⟨j,hj⟩ := hm g i.1
  obtain ⟨t,ht⟩ := SpinAction.representation_monomial g i.2
  refine ⟨(j,t),?_⟩
  simp only [basis_apply, TensorKernel.representation, Representation.tprod_apply,
    TensorProduct.map_tmul]
  rcases hj with hj | hj <;> rcases ht with ht | ht <;>
    simp only [hj,ht,TensorProduct.neg_tmul,TensorProduct.tmul_neg,neg_neg] <;> tauto

end Sporadic.Monster.Construction.TrialitySpin.TensorGeometry
