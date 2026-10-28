module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic

universe u v w

/-! Nilpotence lemmas for representations and finite-dimensional endomorphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} {Γ : Type v} {V : Type w}
  [Field k] [Group Γ] [AddCommGroup V] [Module k V]

/-- Unipotence of every group operator descends to an invariant quotient. -/
public lemma Representation.isNilpotent_quotient_sub_one
    (ρ : Representation k Γ V) (W : Submodule k V)
    (hW : ∀ g : Γ, W ≤ W.comap (ρ g))
    (hunipotent : ∀ g : Γ, IsNilpotent (ρ g - 1)) :
    ∀ g : Γ, IsNilpotent (ρ.quotient W hW g - 1) := by
  intro g
  obtain ⟨r, hr⟩ := hunipotent g
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ y =>
    have hp : ∀ j : ℕ,
        ((ρ.quotient W hW g - 1) ^ j) (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (((ρ g - 1) ^ j) y) := by
      intro j
      induction j with
      | zero => simp
      | succ j hj =>
          rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
          simp only [LinearMap.sub_apply, Module.End.one_apply, hj]
          simp [Representation.quotient]
    change ((ρ.quotient W hW g - 1) ^ r)
      (Submodule.Quotient.mk y) = 0
    rw [hp r, hr]
    simp

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The trace pairing on a finite-dimensional endomorphism algebra separates
points. -/
public lemma endomorphism_eq_zero_of_trace_mul_eq_zero
    (x : Module.End k V)
    (h : ∀ y : Module.End k V, LinearMap.trace k V (x * y) = 0) :
    x = 0 := by
  let b := Module.Free.chooseBasis k V
  apply (LinearMap.toMatrix b b).injective
  rw [map_zero]
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  let y : Module.End k V := Matrix.toLin b b Y
  have hy := h y
  simpa [LinearMap.trace_eq_matrix_trace k b, y,
    LinearMap.toMatrix_mul] using hy

/-- On a finite-dimensional vector space, pointwise local nilpotence has the
uniform exponent given by the dimension. -/
public lemma endomorphism_pow_finrank_eq_zero_of_locallyNilpotent
    (f : Module.End k V)
    (h : ∀ x : V, ∃ n : ℕ, (f^[n]) x = 0) :
    f ^ (Module.finrank k V) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨n, hn⟩ := h x
  have hx : x ∈ LinearMap.ker (f ^ n) := by
    rw [LinearMap.mem_ker]
    simpa only [Module.End.coe_pow] using hn
  have hx' : x ∈ LinearMap.ker (f ^ (Module.finrank k V)) :=
    (Module.End.ker_pow_le_ker_pow_finrank f n) hx
  exact hx'

/-- A group injected into a nilpotent group is nilpotent. -/
public lemma isNilpotent_of_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f)
    (hH : Group.IsNilpotent H) : Group.IsNilpotent G := by
  let : Group.IsNilpotent H := hH
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  let : Group.IsNilpotent f.range := Subgroup.isNilpotent f.range
  exact (Group.isNilpotent_congr e).mpr inferInstance

end Theory.AlgebraicGroup
