module

public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# Inner and outer operators on the binary natural–dual pair

Inverse transpose is implemented by exchanging a vector with its dot-product
functional. The trivial invertible commutant makes every implementation
unique. Thus inner automorphisms preserve the two factors and outer
automorphisms exchange them, on the actual six-dimensional module.
Source: Aschbacher–Smith 15.3.58(3), printed p.1149.
-/

@[expose] public section
open Representation
namespace BinaryLinearThree.NaturalDual

noncomputable def graphSwap : Space ≃ₗ[ZMod 2] Space :=
  (LinearEquiv.prodComm _ _ _).trans
    (AutomorphismAction.graphNaturalDual.symm.toLinearEquiv.prodCongr
      AutomorphismAction.graphNaturalDual.toLinearEquiv)

theorem graphSwap_apply (x : Space) : graphSwap x =
    (AutomorphismAction.graphNaturalDual.symm x.2,
      AutomorphismAction.graphNaturalDual x.1) := rfl

theorem graphSwap_covariance (g : Group) (x : Space) :
    graphSwap (action g x) = action (AutomorphismAction.graph g) (graphSwap x) := by
  apply Prod.ext
  · change AutomorphismAction.graphNaturalDual.symm (W.dual g x.2) =
      W (AutomorphismAction.graph g) (AutomorphismAction.graphNaturalDual.symm x.2)
    exact LinearMap.congr_fun (AutomorphismAction.graphNaturalDual.symm.isIntertwining' g) x.2
  · change AutomorphismAction.graphNaturalDual (W g x.1) =
      W.dual (AutomorphismAction.graph g) (AutomorphismAction.graphNaturalDual x.1)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      AutomorphismAction.graph_graph, LinearMap.comp_apply, Equiv.coe_toLinearMap] using
      LinearMap.congr_fun (AutomorphismAction.graphNaturalDual.isIntertwining'
        (AutomorphismAction.graph g)) x.1

/-- A group automorphism has at most one implementing linear equivalence. -/
theorem implementing_unique (α : MulAut Group) (f h : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g x, f (action g x) = action (α g) (f x))
    (hh : ∀ g x, h (action g x) = action (α g) (h x)) : f = h := by
  have hc : ∀ g x, (f.trans h.symm) (action g x) =
      action g ((f.trans h.symm) x) := by
    intro g x
    change h.symm (f (action g x)) = action g (h.symm (f x))
    apply h.injective
    rw [h.apply_symm_apply, hf, hh, h.apply_symm_apply]
  have he := centralizer_eq_one (f.trans h.symm) hc
  ext x : 1
  have hx := congrArg (fun e : Space ≃ₗ[ZMod 2] Space => e x) he
  have hxx := congrArg h hx
  simpa only [LinearEquiv.trans_apply, h.apply_symm_apply, LinearEquiv.refl_apply] using hxx

noncomputable def innerOperator (g : Group) : Space ≃ₗ[ZMod 2] Space :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (action.asGroupHom g)

theorem innerOperator_covariance (g k : Group) (x : Space) :
    innerOperator g (action k x) = action ((MulAut.conj g) k) (innerOperator g x) := by
  change action g (action k x) = action (g * k * g⁻¹) (action g x)
  simp only [← Module.End.mul_apply, ← map_mul]
  simp [mul_assoc]

theorem inner_operator (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g x, f (action g x) = action (α g) (f x))
    (hα : α ∈ MulAut.innerSubgroup Group) : ∃ g : Group, f = innerOperator g := by
  obtain ⟨g, rfl⟩ := hα
  exact ⟨g, implementing_unique _ f (innerOperator g) hf (innerOperator_covariance g)⟩

theorem outer_operator (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g x, f (action g x) = action (α g) (f x))
    (hα : α ∉ MulAut.innerSubgroup Group) :
    ∃ g : Group, f = graphSwap.trans (innerOperator g) := by
  obtain ⟨g, hg⟩ := AutomorphismAction.outer_eq_inner_graph α hα
  refine ⟨g, implementing_unique α f (graphSwap.trans (innerOperator g)) hf ?_⟩
  intro k x
  change innerOperator g (graphSwap (action k x)) =
    action (α k) (innerOperator g (graphSwap x))
  rw [graphSwap_covariance, innerOperator_covariance, hg]
  rfl

theorem outer_swaps (α : MulAut Group) (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g x, f (action g x) = action (α g) (f x))
    (hα : α ∉ MulAut.innerSubgroup Group) :
    (∀ v : Vector, (f (v, 0)).1 = 0) ∧
      ∀ v : Module.Dual (ZMod 2) Vector, (f (0, v)).2 = 0 := by
  obtain ⟨g, rfl⟩ := outer_operator α f hf hα
  constructor
  · intro v
    change W g (AutomorphismAction.graphNaturalDual.symm.toLinearEquiv 0) = 0
    rw [LinearEquiv.map_zero, map_zero]
  · intro v
    change W.dual g (AutomorphismAction.graphNaturalDual.toLinearEquiv 0) = 0
    rw [LinearEquiv.map_zero, map_zero]

end BinaryLinearThree.NaturalDual
