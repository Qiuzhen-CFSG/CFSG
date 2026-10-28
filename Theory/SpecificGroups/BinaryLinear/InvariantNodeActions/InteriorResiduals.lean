module
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators

/-!
# Interior-node residuals are not of exponent six

For an interior node, roots entering and leaving its two-dimensional Levi
block belong to the literal two-residual. Their product has a nonidentity
sixth power, witnessed on the last basis vector. This uniform argument
retains the original basis and works in every dimension with an interior node.
It excludes products of A₃ blocks in the source parabolic application.

Source: Aschbacher--Smith 15.1.22(*), (3), printed pp.1098--1100.
-/
public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic OrderedResidualConjugators

/-- Every non-end node has a two-residual containing a nonidentity sixth power. -/
theorem interior_node_residual_not_exponent_six {m : ℕ} (b : Basis m) (i : Fin m)
    (hi : 0 < i.val) (hi' : i.val + 1 < m) :
    ∃ x ∈ pResidual 2 (minimalParabolic b i), x ^ 6 ≠ 1 := by
  let P := minimalParabolic b i
  let r : Fin (m+1) := ⟨0,by omega⟩
  let s := i.castSucc
  let u : Fin (m+1) := ⟨m,by omega⟩
  have hrs : r ≠ s := by intro he; have := congrArg Fin.val he; simp [r,s] at this; omega
  have hsu : s ≠ u := by intro he; have := congrArg Fin.val he; simp [s,u] at this; omega
  have hru : r ≠ u := by intro he; have := congrArg Fin.val he; simp [r,u] at this; omega
  let x := root b r s hrs
  let y := root b s u hsu
  have hx : x ∈ nodeResidual b i := incident_root_mem_nodeResidual b i r s hrs
    (Or.inl ⟨hi,Or.inl rfl⟩)
  have hy : y ∈ nodeResidual b i := incident_root_mem_nodeResidual b i s u hsu
    (Or.inr ⟨Or.inl rfl,hi'⟩)
  obtain ⟨g,hg,he⟩ := (nodeResidual b i).mul_mem hx hy
  change (g : LinearGroup (m+1)) = x*y at he
  refine ⟨g,hg,?_⟩
  intro h6
  have hv : ((x*y)^6) (b u) = b u := by
    have hh := congrArg (fun a : P => (a : LinearGroup (m+1)) (b u)) h6
    simpa only [coe_pow,coe_one,he,LinearEquiv.coe_one,id_eq] using hh
  have hv' : ((x*y)^6) (b u) = b u + b r := by
    simp [x,y,pow_succ,LinearEquiv.mul_apply,root_basis,hrs,hsu,hru,
      Ne.symm hsu,map_add]
    funext j
    simp only [Pi.add_apply]
    ring_nf
    simp only [show (6 : ZMod 2) = 0 from by decide,
      show (21 : ZMod 2) = 1 from by decide,mul_zero,add_zero,mul_one]
  rw [hv'] at hv
  exact b.ne_zero r (add_eq_left.mp hv)
end BinaryLinear.InvariantNodeActions
