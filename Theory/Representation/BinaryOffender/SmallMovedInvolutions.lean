module
public import Theory.Representation.BinaryOffender.MovedFaithfulness
public import Theory.Representation.BinaryOffender.InvolutionRatio
/-!
# Involutions supported on a small moved space

A faithful binary action with trivial two-core remains faithful on the moved
space of the entire actor. More generally the same argument applies to a
subgroup with trivial two-core and its specified invariant moved space.
An involution's displacement then lies in a proper fixed subspace of that
moved space. A moved space of dimension at most three therefore bounds the
involution's displacement on the original module by two.

The source application is the SL₃(2) factor in Aschbacher–Smith B.5.13,
printed p.110. No splitting of the original module is needed.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
 [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- Faithfulness on the literal moved space of a subgroup with trivial two-core. -/
theorem faithful_on_moved_subrepresentation (σ : Representation (ZMod 2) G V)
    (hf : Function.Injective σ) (N : Subgroup G) (hc : pCore 2 N = ⊥)
    (U : Subrepresentation σ) (hU : U.toSubmodule = subspaceCommutator σ ⊤ N) :
    Function.Injective (U.toRepresentation.comp N.subtype) := by
  let τ := U.toRepresentation.comp N.subtype
  have hk : τ.ker = ⊥ := by
    apply normal_eq_bot_of_fixes_displacements (σ.comp N.subtype)
      (hf.comp N.subtype_injective) hc ⊤ τ.ker le_top
    intro n hn k hk v
    have hv : σ (k : G) v - v ∈ U.toSubmodule := by
      rw [hU]
      exact Submodule.subset_span ⟨k, k.property, v, Submodule.mem_top, rfl⟩
    have he := congrArg (fun f => (f : Module.End (ZMod 2) U.toSubmodule)
        ⟨σ (k : G) v - v,hv⟩) hn
    exact congrArg Subtype.val he
  intro a b hab
  have hh : a * b⁻¹ ∈ τ.ker := by
    change τ (a * b⁻¹) = 1
    rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
  exact mul_inv_eq_one.mp (hk.le hh)

/-- Every involution supported in a moved space of dimension at most three
displaces at most two dimensions of the full module. -/
theorem fixedCodim_involution_le_two_of_small_moved (σ : Representation (ZMod 2) G V)
    (hf : Function.Injective σ) (N : Subgroup G) (hc : pCore 2 N = ⊥)
    (U : Subrepresentation σ) (hU : U.toSubmodule = subspaceCommutator σ ⊤ N)
    (hdim : Module.finrank (ZMod 2) U.toSubmodule ≤ 3)
    (t : N) (ht : orderOf t = 2) : fixedCodim σ (zpowers (t : G)) ≤ 2 := by
  have hfaith := faithful_on_moved_subrepresentation σ hf N hc U hU
  have hn : ¬ U.toSubmodule ≤ fixedSpace σ (zpowers (t : G)) := by
    intro he
    have hact : (U.toRepresentation.comp N.subtype) t =
        (U.toRepresentation.comp N.subtype) 1 := by
      ext v
      change σ (t : G) (v : V) = σ 1 (v : V)
      rw [map_one]
      exact (mem_fixedSpace_zpowers_iff σ t v).mp (he v.property)
    have hte := hfaith hact
    simp only [hte, orderOf_one] at ht
    omega
  have hlt : U.toSubmodule ⊓ fixedSpace σ (zpowers (t : G)) < U.toSubmodule :=
    lt_of_le_of_ne inf_le_left (fun he => hn (he ▸ inf_le_right))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  have htG : orderOf (t : G) = 2 :=
    (orderOf_injective N.subtype N.subtype_injective t).trans ht
  have ht2 : (t : G) * (t : G) = 1 := by
    have hh := pow_orderOf_eq_one (t : G)
    rw [htG, pow_two] at hh
    exact hh
  have hr : LinearMap.range (σ (t : G) - LinearMap.id) ≤
      U.toSubmodule ⊓ fixedSpace σ (zpowers (t : G)) := by
    rintro _ ⟨v,rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hU]
      exact Submodule.subset_span ⟨t, t.property, v, Submodule.mem_top, rfl⟩
    · exact (mem_fixedSpace_zpowers_iff σ t _).mpr (involution_fixes_displacement σ ht2 v)
  have hle := Submodule.finrank_mono hr
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hle
  omega
end Representation.BinaryOffender
