module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Native120
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree120.Norm
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Reduction
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Theory.Representation.FactorDegreeFiltration.FiniteDual

/-!
# Maps from native Mathieu code constituents

For a small irreducible FF target, the code and cocode have no nonzero maps
by their actual no-FF theorems. The two exterior squares have only the
11-dimensional quotient and a 44-dimensional simple kernel; their duals
give the corresponding obstruction for the cocode. The native trace kernel
is the proved simple module of dimension 120.

Source: Aschbacher–Smith, H.14–H.16 and K.4; the native Golay constructions
implement the degree-44 and degree-120 constituents used here.
-/

open Representation
namespace Representation.Mathieu.M24SmallFF
@[expose] public noncomputable section
variable {G k U W V : Type*} [Group G] [Field k]
  [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
  [AddCommGroup V] [Module k V]
  {τ : Representation k G U} {σ : Representation k G W} {ρ : Representation k G V}

def descend (q : τ.IntertwiningMap σ) (hq : Function.Surjective q)
    (f : τ.IntertwiningMap ρ) (hk : q.toLinearMap.ker ≤ f.toLinearMap.ker) :
    σ.IntertwiningMap ρ := by
  let d : W →ₗ[k] V := (q.toLinearMap.ker.liftQ f.toLinearMap hk).comp
    (q.toLinearMap.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hd (u : U) : d (q u) = f u := by
    change (q.toLinearMap.ker.liftQ f.toLinearMap hk)
      ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap u)) = f u
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨d, ?_⟩
  intro g
  apply LinearMap.ext
  intro w
  obtain ⟨u,rfl⟩ := hq w
  change d (σ g (q u)) = ρ g (d (q u))
  rw [← q.isIntertwining, hd, hd]
  exact LinearMap.congr_fun (f.isIntertwining' g) u

lemma descend_apply (q : τ.IntertwiningMap σ) (hq : Function.Surjective q)
    (f : τ.IntertwiningMap ρ) (hk : q.toLinearMap.ker ≤ f.toLinearMap.ker) (u : U) :
    descend q hq f hk (q u) = f u := by
  change (q.toLinearMap.ker.liftQ f.toLinearMap hk)
    ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap u)) = f u
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

lemma map_eq_zero_of_ker (q : τ.IntertwiningMap σ) (hq : Function.Surjective q)
    (hσ : ∀ f : σ.IntertwiningMap ρ, f = 0)
    (f : τ.IntertwiningMap ρ) (hk : q.toLinearMap.ker ≤ f.toLinearMap.ker) : f = 0 := by
  ext u
  have h := congrArg (fun e : σ.IntertwiningMap ρ => e (q u)) (hσ (descend q hq f hk))
  change f u = 0
  simpa only [descend_apply, IntertwiningMap.coe_zero, Pi.zero_apply] using h

lemma map_eq_zero_of_simple_dim [FiniteDimensional k U] [FiniteDimensional k V]
    [τ.IsIrreducible] [ρ.IsIrreducible]
    (hd : Module.finrank k V < Module.finrank k U) (f : τ.IntertwiningMap ρ) : f = 0 := by
  rcases IsIrreducible.bijective_or_eq_zero f with hf | hz
  · have h := (f.ofBijective hf).toLinearEquiv.finrank_eq
    omega
  · exact hz

end
open Sporadic.Mathieu MathieuCode Representation.BinaryOffender
open Representation.MathieuM24Degree44.FiveSpace
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
public section Native
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M24 V) [ρ.IsIrreducible]
    (hff : IsFFModule ρ) (hd : Module.finrank (ZMod 2) V ≤ 24)

omit [FiniteDimensional (ZMod 2) V] in
include hff in
lemma code_map_zero (f : codeRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : codeRepresentation.IsIrreducible := code_isIrreducible
  by_contra hf
  let E := (f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)).symm
  exact QuadraticActors.code_not_isFFModule (hff.map_equivariant ρ codeRepresentation
    (MonoidHom.id _) Function.injective_id E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))
omit [FiniteDimensional (ZMod 2) V] in
include hff in
lemma cocode_map_zero (f : cocodeRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : cocodeRepresentation.IsIrreducible := cocode_isIrreducible
  by_contra hf
  let E := (f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)).symm
  exact QuadraticActors.cocode_not_isFFModule (hff.map_equivariant ρ cocodeRepresentation
    (MonoidHom.id _) Function.injective_id E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v))
include hd in
lemma kernel44_map_zero (f : kernelRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : kernelRepresentation.IsAbsolutelyIrreducible := kernel_isAbsolutelyIrreducible
  let : kernelRepresentation.IsIrreducible :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  exact map_eq_zero_of_simple_dim (by rw [finrank_kernel]; omega) f
include hd in
lemma dualKernel44_map_zero (f : dualKernelRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : kernelRepresentation.IsAbsolutelyIrreducible := kernel_isAbsolutelyIrreducible
  let : kernelRepresentation.IsIrreducible :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  let : dualKernelRepresentation.IsIrreducible := isIrreducible_dual
  exact map_eq_zero_of_simple_dim (by rw [finrank_dualKernel]; omega) f
include hff hd in
lemma codeExterior_map_zero (f : codeExterior.IntertwiningMap ρ) : f = 0 := by
  apply map_eq_zero_of_ker contraction contraction_surjective (cocode_map_zero ρ hff) f
  let i : kernelRepresentation.IntertwiningMap codeExterior := ⟨kernel.toSubmodule.subtype, fun _ => rfl⟩
  have hi := kernel44_map_zero ρ hd (f.comp i)
  intro v hv
  exact congrArg (fun e : kernelRepresentation.IntertwiningMap ρ => e ⟨v,hv⟩) hi
include hff hd in
lemma dualCodeExterior_map_zero (f : codeExterior.dual.IntertwiningMap ρ) : f = 0 := by
  let i : cocodeRepresentation.dual.IntertwiningMap codeExterior.dual :=
    ⟨contraction.toLinearMap.dualMap, by
      intro g
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro v
      exact congrArg φ (LinearMap.congr_fun (contraction.isIntertwining' g⁻¹) v).symm⟩
  let q : codeExterior.dual.IntertwiningMap dualKernelRepresentation :=
    ⟨kernel.toSubmodule.dualRestrict, fun _ => rfl⟩
  apply map_eq_zero_of_ker q (Subspace.dualRestrict_surjective (W := kernel.toSubmodule))
    (dualKernel44_map_zero ρ hd) f
  intro φ hφ
  have hr : φ ∈ LinearMap.range contraction.toLinearMap.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact hφ
  obtain ⟨ψ, rfl⟩ := hr
  have hh := code_map_zero ρ hff ((f.comp i).comp codeDuality.toIntertwiningMap)
  obtain ⟨u, hu⟩ := codeDuality.toLinearEquiv.surjective ψ
  have hv := congrArg (fun e : codeRepresentation.IntertwiningMap ρ => e u) hh
  change f (i (codeDuality u)) = 0 at hv
  change codeDuality u = ψ at hu
  rw [hu] at hv
  exact hv
include hff hd in
lemma cocodeExterior_map_zero (f : cocodeExterior.IntertwiningMap ρ) : f = 0 := by
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Subspace.dual_finrank_eq, finrank_cocodeExterior, finrank_codeExterior])).mpr
      exteriorPairingLinear_surjective
  let e := exteriorPairing.ofBijective ⟨hinj, exteriorPairingLinear_surjective⟩
  have hh := dualCodeExterior_map_zero ρ hff hd (f.comp e.symm.toIntertwiningMap)
  ext v
  have he := congrArg (fun q : codeExterior.dual.IntertwiningMap ρ => q (e v)) hh
  change f (e.symm (e v)) = 0 at he
  rw [e.symm_apply_apply] at he
  exact he

include hd in
lemma traceZero_map_zero (f : Native120.nativeTraceZeroRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : native120Realization.representation.IsAbsolutelyIrreducible :=
    native120Realization.absolute120_of_norm MatrixDensity.Degree120.norm_mem
  let : native120Realization.representation.IsIrreducible :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible _
  let E : Native120.nativeTraceZeroRepresentation.Equiv native120Realization.representation :=
    Representation.Equiv.mk native120Equiv (by
      intro g
      apply LinearMap.ext
      intro v
      exact native120Equiv_equivariant g v)
  have hdim : Module.finrank (ZMod 2) V < Module.finrank (ZMod 2) (Fin 120 → ZMod 2) := by
    rw [Module.finrank_fin_fun]
    omega
  let f' : native120Realization.representation.IntertwiningMap ρ :=
    f.comp E.symm.toIntertwiningMap
  have hh : f' = 0 := map_eq_zero_of_simple_dim hdim f'
  ext v
  have hv := congrArg (fun q : native120Realization.representation.IntertwiningMap ρ => q (E v)) hh
  change f (E.symm (E v)) = 0 at hv
  rw [E.symm_apply_apply] at hv
  exact hv
end Native
end Representation.Mathieu.M24SmallFF
