module
public import Theory.SpecificGroups.PSL3Two.PairedOuterInputs
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates

/-!
# Cubic commutators of involutory automorphisms of SL₃(2)

Every nonidentity involutory automorphism has a commutator of order three.
For inner automorphisms, conjugacy reduces to a transvection; for outer
ones, the diagram cocycle calculation supplies an inner conjugator.
One explicit matrix in each case gives the cubic, and automorphism
transport preserves its exact order.

This supplies the group calculation for the mixed natural/Steinberg
exclusion in Aschbacher--Smith D.3.7--9, printed pp.197--200, used in
original3.2.6 and10.1.1. The representation consumer retains the actual
normal square and the full action kernel.
-/

public noncomputable section
open Matrix Subgroup
namespace Matrix.PSL3Two

private theorem cubic_commutator_transport (α β e : MulAut SL)
    (he : ∀ x, e (α x) = β (e x))
    (hβ : ∃ x, orderOf (β x * x⁻¹) = 3) :
    ∃ x, orderOf (α x * x⁻¹) = 3 := by
  obtain ⟨x,hx⟩ := hβ
  refine ⟨e.symm x, ?_⟩
  rw [← e.orderOf_eq, map_mul, map_inv, he, e.apply_symm_apply]
  exact hx

theorem involutory_automorphism_cubic_commutator (α : MulAut SL)
    (hα : α * α = 1) (hne : α ≠ 1) :
    ∃ x, orderOf (α x * x⁻¹) = 3 := by
  by_cases hin : ∃ g, α = MulAut.conj g
  · obtain ⟨g,rfl⟩ := hin
    have hg : g * g = 1 := MarkedAutomorphisms.conj_injective (by
      rw [map_mul,map_one]
      exact hα)
    have hg1 : g ≠ 1 := fun hh => hne (by rw [hh,map_one])
    obtain ⟨c,hc⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator
      g hg1 hg
    let z := BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution
    have hc' : g = c * z * c⁻¹ := by rw [←hc,mul_inv_cancel_right]
    apply cubic_commutator_transport (MulAut.conj g) (MulAut.conj z) (MulAut.conj c⁻¹)
    · intro x
      simp only [MulAut.conj_apply,hc']
      group
    · let x : SL := ⟨!![0,0,1;0,1,0;1,0,0],by decide⟩
      refine ⟨x,orderOf_eq_prime ?_ ?_⟩ <;> decide
  · have hout : ∀ g, α ≠ MulAut.conj g := by simpa only [not_exists] using hin
    obtain ⟨c,hc⟩ := PairedOuterInputs.exists_inner_conjugate_diagram α
      (fun x => DFunLike.congr_fun hα x) hout
    apply cubic_commutator_transport α MarkedAutomorphisms.diagram (MulAut.conj c)
    · intro x
      have hh := DFunLike.congr_fun hc (MulAut.conj c x)
      simpa only [MulAut.mul_apply,MulAut.inv_apply_self] using hh
    · let x : SL := ⟨!![0,0,1;1,0,0;0,1,0],by decide⟩
      refine ⟨x,orderOf_eq_prime ?_ ?_⟩ <;> decide

end Matrix.PSL3Two
