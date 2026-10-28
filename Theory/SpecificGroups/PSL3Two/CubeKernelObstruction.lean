module

public import Theory.SpecificGroups.GL2.CubeKernelInvolutions
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# The binary PSL₃ obstruction in cubic quotients of GL₂ subgroups

Two distinct binary transvections give two distinct involutions in the actual
PSL₃(2), using the canonical SL₃(2) to PSL₃(2) isomorphism. Thus a perfect
subgroup isomorphic to PSL₃(2) cannot embed in a quotient of an
odd-characteristic degree-two linear group through a kernel of exponent three.

Source: the inner-involution exclusion in Aschbacher--Smith, proof of 15.3.38,
p.1137, using the degree-two centralizer blocks from A.3.21(a), p.55.
-/

open Subgroup Matrix
namespace Matrix.PSL3Two.CubeKernel

private def u : PSL3Two.SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def v : PSL3Two.SL := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
private theorem u_sq : u ^ 2 = 1 := by decide +kernel
private theorem v_sq : v ^ 2 = 1 := by decide +kernel
private theorem u_ne : u ≠ 1 := by decide +kernel
private theorem v_ne : v ≠ 1 := by decide +kernel
private theorem u_ne_v : u ≠ v := by decide +kernel

/-- There is no faithful perfect PSL₃(2) subgroup in such a cubic quotient. -/
public theorem no_perfect_psl3_two {G H K F : Type*} [Group G] [Group H] [Group K]
    [Group.IsPerfect K] [Field F]
    (hF : (2 : F) ≠ 0) (f : G →* H) (hf : Function.Surjective f)
    (hker : ∀ g ∈ f.ker, g ^ 3 = 1)
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (j : K →* H) (hj : Function.Injective j)
    (e : K ≃* PSL3Two.PSL) : False := by
  let a := PSL3Two.equiv.trans e.symm
  have hu : a u ^ 2 = 1 := by rw [← map_pow, u_sq, map_one]
  have hv : a v ^ 2 = 1 := by rw [← map_pow, v_sq, map_one]
  have he := GeneralLinearGroup.CubeKernel.perfect_involutions_eq hF f hf hker ρ hρ j hj hu
    (fun h => u_ne (a.injective (h.trans a.map_one.symm))) hv
    (fun h => v_ne (a.injective (h.trans a.map_one.symm)))
  exact u_ne_v (a.injective he)

end Matrix.PSL3Two.CubeKernel
