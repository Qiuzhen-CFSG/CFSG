module

public import Theory.Representation.FirstCohomologyDuality
public import Mathlib.Algebra.Field.ZMod

/-!
# Central kernel and commutator disjointness from dual H1

The dual of a central quotient is an inclusion with trivial quotient.
Vanishing dual H1 supplies a fixed complement to that inclusion. Its
fixed functionals annihilate the original commutator, proving that the
original central kernel and commutator intersect trivially.

Source: Aschbacher--Smith I.1.6 and 12.7.16, printed pp.408 and844.
-/

public noncomputable section
namespace Representation.OneCohomology
variable {D U Q : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup Q] [Module (ZMod 2) Q]
  {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) D Q}

private theorem range_H1 (i : σ.IntertwiningMap τ) (hi : Function.Injective i)
    [Subsingleton (H1 σ)] : Subsingleton (H1 i.range.toRepresentation) := by
  let l : U ≃ₗ[ZMod 2] i.range.toSubmodule := LinearEquiv.ofInjective i.toLinearMap hi
  have hl (g : D) (v : U) : l (σ g v) = i.range.toRepresentation g (l v) :=
    Subtype.ext (i.isIntertwining σ τ g v)
  exact (H1Congr σ i.range.toRepresentation (MulEquiv.refl D) l hl).symm.injective.subsingleton

private theorem range_fixed_supplement (i : σ.IntertwiningMap τ)
    (hi : Function.Injective i) (ht : HasTrivialQuotient i.range)
    [Subsingleton (H1 σ)] (v : Q) :
    ∃ u : U, ∃ z : Q, z ∈ τ.invariants ∧ i u + z = v := by
  let := range_H1 i hi
  have hv := (extensionClass_eq_zero_iff i.range ht v).mp (Subsingleton.elim _ _)
  obtain ⟨_, ⟨u,rfl⟩, z, hz, he⟩ := Submodule.mem_sup.mp hv
  exact ⟨u,z,hz,he⟩

theorem central_kernel_disjoint_commutator
    (p : σ.IntertwiningMap τ) (hs : Function.Surjective p)
    (hc : p.toLinearMap.ker ≤ σ.invariants) [Subsingleton (H1 τ.dual)] :
    Disjoint (Coinvariants.ker σ) p.toLinearMap.ker := by
  let i : τ.dual.IntertwiningMap σ.dual := dualIntertwining p
  have ht : HasTrivialQuotient i.range := by
    intro g f
    change σ.dual g f - f ∈ p.toLinearMap.dualMap.range
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro w hw
    change f (σ g⁻¹ w) - f w = 0
    rw [(hc hw) g⁻¹, sub_self]
  rw [Submodule.disjoint_def]
  intro x hx hk
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp
  intro f
  obtain ⟨b,z,hz,rfl⟩ := range_fixed_supplement (σ := τ.dual) (τ := σ.dual) i
    (LinearMap.dualMap_injective_of_surjective (f := p.toLinearMap) hs) ht f
  have hz' : z ∈ (Coinvariants.ker σ).dualAnnihilator := by
    rw [← σ.invariants_dual_eq_commutator_annihilator]
    exact hz
  change b (p x) + z x = 0
  have hzx : z x = 0 := by
    rw [Submodule.mem_dualAnnihilator] at hz'
    exact hz' x hx
  rw [show p x = 0 from hk, map_zero, hzx, add_zero]

end Representation.OneCohomology
