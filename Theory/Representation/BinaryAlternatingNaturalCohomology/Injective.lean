module
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.HigmanRelativeTrace.Injective
-- Internal companion to the projectivity proof: reuse its checked trace
-- seed without exposing the private matrix calculation in the public API.
import all Theory.Representation.BinaryAlternatingNaturalCohomology.Projective

/-!
# Injectivity of the binary deleted A₅ module

The same relative-trace identity that proves projectivity proves injectivity.
Consequently copies embedded in an arbitrary module split off, including in
characteristic two. This supplies the splitting needed in the whole-layer
argument of Aschbacher--Smith 5.1.14(4) and 5.1.19, printed pp.638,643--644.
-/

public noncomputable section

namespace BinaryPermutation

theorem alternatingFive_core_injective :
    Module.Injective (MonoidAlgebra (ZMod 2) (alternatingGroup (Fin 5)))
      (alternatingCoreRepresentation (Fin 5)).asModule := by
  let ρ := alternatingCoreRepresentation (Fin 5)
  let a := ρ.asModuleEquiv.symm.conj traceSeed
  apply ModularBlock.HigmanRelativeTrace.injective_of_relative_trace_id a
  apply LinearMap.ext
  intro v
  apply ρ.asModuleEquiv.injective
  simp only [LinearMap.sum_apply, LinearMap.id_apply, map_sum,
    LinearMap.conjugate_apply, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul]
  simp only [a, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single, one_smul]
  exact traceSeed_sum _

end BinaryPermutation
