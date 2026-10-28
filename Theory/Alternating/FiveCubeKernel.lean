module

public import Theory.SpecificGroups.GL2.CubeKernelInvolutions
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# A₅ in quotients with a cubic kernel

A₅ has two distinct involutions. A perfect subgroup of an odd-characteristic
GL₂ subgroup modulo a kernel of exponent three has at most one involution.
Thus no faithful perfect A₅ can occur in that quotient.

Source: the odd ternary rows of Aschbacher--Smith A.3.14, pp.49--50.
-/

open Subgroup Matrix Equiv.Perm
namespace AlternatingFive.CubeKernel

private def u : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [mem_alternatingGroup]; decide +kernel⟩
private def v : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [mem_alternatingGroup]; decide +kernel⟩
private theorem u_sq : u ^ 2 = 1 := by decide +kernel
private theorem v_sq : v ^ 2 = 1 := by decide +kernel
private theorem u_ne : u ≠ 1 := by decide +kernel
private theorem v_ne : v ≠ 1 := by decide +kernel
private theorem u_ne_v : u ≠ v := by decide +kernel

/-- There is no faithful perfect A₅ subgroup in such a cubic quotient. -/
public theorem no_perfect_alternating_five {G H K F : Type*} [Group G] [Group H] [Group K]
    [Group.IsPerfect K] [Field F]
    (hF : (2 : F) ≠ 0) (f : G →* H) (hf : Function.Surjective f)
    (hker : ∀ g ∈ f.ker, g ^ 3 = 1)
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (j : K →* H) (hj : Function.Injective j)
    (e : K ≃* alternatingGroup (Fin 5)) : False := by
  let a := e.symm
  have hu : a u ^ 2 = 1 := by rw [← map_pow, u_sq, map_one]
  have hv : a v ^ 2 = 1 := by rw [← map_pow, v_sq, map_one]
  have he := GeneralLinearGroup.CubeKernel.perfect_involutions_eq hF f hf hker ρ hρ j hj hu
    (fun h => u_ne (a.injective (h.trans a.map_one.symm))) hv
    (fun h => v_ne (a.injective (h.trans a.map_one.symm)))
  exact u_ne_v (a.injective he)

end AlternatingFive.CubeKernel
