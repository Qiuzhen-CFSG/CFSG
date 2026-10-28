module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Borels

/-!
# Transporting residual displacements to a standard Sylow subgroup

An actual conjugation carrying the standard Borel into the source residual
carries its embedded three-residual there. Applying the source fixer and
transporting the displacement back gives membership in the standard Sylow.
No invariant torus or quotient-action formula is an input.

Source: Aschbacher–Smith 13.8.20, printed p.954.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
variable {D : Type*} [Group D]

/-- Functoriality of the actual embedded residual, without a quotient convention. -/
theorem map_residualIn_le (p : ℕ) (f : D →* D) (B C : Subgroup D)
    (h : B.map f ≤ C) : (residualIn p B).map f ≤ residualIn p C := by
  let g : B →* C := (f.comp B.subtype).codRestrict C
    (fun b => h (mem_map_of_mem f b.property))
  rintro _ ⟨_,⟨b,hb,rfl⟩,rfl⟩
  exact ⟨g b, map_pResidual_le p g (mem_map_of_mem g hb), rfl⟩

/-- Residual fixation transports actual displacements along a Sylow alignment. -/
theorem aligned_actor_displacement (e : D ≃* D) (U B : Subgroup D) (S : Sylow 2 D)
    (hUS : U.map e.toMonoidHom = S)
    (hB : B.map e.toMonoidHom ≤ intrinsicResidual S)
    (hcore : (intrinsicResidual S).pCoreIn 2 = S)
    (α : MulAut D) (hfix : FixesResidualTorus (intrinsicResidual S) α)
    {x : D} (hx : x ∈ residualIn 3 B) :
    ((MulAut.congr e.symm) α) x * x⁻¹ ∈ U := by
  have he : e x ∈ residualIn 3 (intrinsicResidual S) :=
    map_residualIn_le 3 e.toMonoidHom B (intrinsicResidual S) hB (mem_map_of_mem _ hx)
  have hd := hfix (e x) (mem_sup_left he)
  rw [hcore, ← hUS] at hd
  obtain ⟨u,hu,heq⟩ := hd
  have hh := congrArg e.symm heq
  have hh' : u = ((MulAut.congr e.symm) α) x * x⁻¹ := by
    change u = e.symm (α (e x)) * x⁻¹
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, e.symm_apply_apply] using hh
  exact hh' ▸ hu


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
