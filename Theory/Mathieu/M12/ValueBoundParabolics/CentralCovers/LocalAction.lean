module

public import Theory.Mathieu.M12.Properties.Sylow3
import all Theory.Mathieu.M12.Properties.Sylow3

/-!
# The inverting action on the marked M₁₂ Sylow three-subgroup

An explicit word in the ATLAS generators induces (i,j,k) ↦ (-i,-j,k)
on the existing order-27 Heisenberg subgroup. The permutation identities
are checked in the kernel, so this is an action on the actual M₁₂ carrier.

This is the local action used to exclude three-primary central kernels
in the M₁₂ case of Aschbacher–Smith E.4.3(1), printed pp.241–242.
It realizes the inverting element in the normalizer described in GLS3,
Table 5.3b (row 3A). No normalizer-order or multiplier assumption is used.
The generators and Heisenberg embedding are those of M12.Properties.Sylow3.
The internal import grants access to that module's checked permutation tables;
this implementation coupling is confined to the calculation proofs here.
-/

public section

open Subgroup
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers

set_option maxRecDepth 100000

@[expose] def heisenbergInversion : MulAut M12Heisenberg where
  toFun a := ⟨-a.i, -a.j, a.k⟩
  invFun a := ⟨-a.i, -a.j, a.k⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp
  map_mul' a b := by
    apply M12Heisenberg.ext
    · change -(a.i + b.i) = -a.i + -b.i
      exact neg_add a.i b.i
    · change -(a.j + b.j) = -a.j + -b.j
      exact neg_add a.j b.j
    · change a.k + b.k - a.j * b.i = a.k + b.k - (-a.j) * (-b.i)
      ring

@[expose] noncomputable def sylowThreeInverter : M12 :=
  let a : M12 := ⟨m12GeneratorA, m12GeneratorA_mem⟩
  let b : M12 := ⟨m12GeneratorB, m12GeneratorB_mem⟩
  a * b * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b * a * b * a * b * a * b⁻¹ * a * b * a * b⁻¹ * a * b * a * b * a

private def sylowThreeInverterPerm : Equiv.Perm (Fin 12) where
  toFun := ![11, 9, 2, 4, 3, 5, 7, 6, 8, 1, 10, 0]
  invFun := ![11, 9, 2, 4, 3, 5, 7, 6, 8, 1, 10, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem sylowThreeInverter_perm :
    (sylowThreeInverter : Equiv.Perm (Fin 12)) = sylowThreeInverterPerm := by
  decide +kernel

theorem sylowThreeInverter_sq : sylowThreeInverter ^ 2 = 1 := by
  apply Subtype.ext
  change (sylowThreeInverter : Equiv.Perm (Fin 12)) ^ 2 = 1
  rw [sylowThreeInverter_perm]
  decide +kernel

theorem sylowThreeInverter_conj (a : M12Heisenberg) :
    sylowThreeInverter * m12HeisenbergHom a * sylowThreeInverter⁻¹ =
      m12HeisenbergHom (heisenbergInversion a) := by
  apply Subtype.ext
  change (sylowThreeInverter : Equiv.Perm (Fin 12)) *
    (m12HeisenbergEval a : Equiv.Perm (Fin 12)) *
    (sylowThreeInverter : Equiv.Perm (Fin 12))⁻¹ =
      (m12HeisenbergEval (heisenbergInversion a) : Equiv.Perm (Fin 12))
  rw [sylowThreeInverter_perm, m12HeisenbergEval_perm, m12HeisenbergEval_perm]
  rcases a with ⟨i,j,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

/-- The inverse of the marked Sylow equivalence is the concrete embedding. -/
theorem heisenbergEquiv_symm_apply (a : M12Heisenberg) :
    (m12Sylow3Subgroup_mulEquiv_heisenberg.symm a : M12) = m12HeisenbergHom a := by rfl

theorem sylowThreeInverter_mem_normalizer :
    sylowThreeInverter ∈ normalizer (m12Sylow3Subgroup : Set M12) := by
  apply mem_normalizer_iff.mpr
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨heisenbergInversion b, (sylowThreeInverter_conj b).symm⟩
  · intro ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨heisenbergInversion.symm b, ?_⟩
    have hc := sylowThreeInverter_conj (heisenbergInversion.symm b)
    rw [heisenbergInversion.apply_symm_apply, hb] at hc
    exact mul_left_cancel (mul_right_cancel hc)

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics.CentralCovers
