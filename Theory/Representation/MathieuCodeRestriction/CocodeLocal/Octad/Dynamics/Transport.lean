module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Moments
/-!
# Transporting the native moment coordinates

The seed parity-and-moment coordinates are carried to any octad by an actual
M24 conjugator. The map, kernel, parity, translation parameters, and fixed
exterior pairs all intertwine the literal actions. This coordinate model is
constructed from the native seed calculation, with no fixed-space premise.

Source: Aschbacher--Smith, H.15.2, printed pp.398--399.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
open Representation.BinaryOffender
namespace MathieuCode.CocodeOctad.Dynamics
open SmallKernelFixed
noncomputable section

lemma action_inv (g : M24) (v : Cocode) :
    cocodeRepresentation g⁻¹ (cocodeRepresentation g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
lemma action_inv' (g : M24) (v : Cocode) :
    cocodeRepresentation g (cocodeRepresentation g⁻¹ v) = v := by
  simpa only [inv_inv] using action_inv g⁻¹ v

def actionEquiv (g : M24) : Cocode ≃ₗ[ZMod 2] Cocode :=
  { cocodeRepresentation g with
    invFun := cocodeRepresentation g⁻¹
    left_inv := action_inv g
    right_inv := action_inv' g }

lemma parity_transport (O P : Octad) (g : M24) (hg : g • O.val = P.val) (v : Cocode) :
    octadParity P (cocodeRepresentation g v) = octadParity O v := by
  obtain ⟨w, rfl⟩ := codeInCore.mkQ_surjective v
  rw [cocodeRepresentation_mk, octadParity_mk, octadParity_mk]
  have hw : fullRepresentation g (wordOfSet O.val) = wordOfSet P.val := by
    change BinaryPermutation.representation (Fin 24) g.val _ = _
    rw [permute_wordOfSet]
    exact congrArg wordOfSet hg
  exact hw ▸ dotForm_invariant g (wordOfSet O.val) w.val

lemma supported_transport (B : Finset (Fin 24)) (g : M24)
    {v : Cocode} (hv : v ∈ supportedPairSpace B) :
    cocodeRepresentation g v ∈ supportedPairSpace (g • B) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨P, hP, rfl⟩ := hv
    rw [pairVector_equivariant]
    exact pairVector_mem_supportedPairSpace _ (Finset.smul_finset_subset_smul_finset hP)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv

/-- Native coordinates, including the translation action and actual fixed pair classes. -/
structure CoordinateModel (O : Octad) where
  map : Cocode →ₗ[ZMod 2] (ZMod 2 × E)
  surjective : Function.Surjective map
  ker : map.ker = supportedPairSpace O.val
  parity : ∀ v, (map v).1 = octadParity O v
  actor : Fin 16 ≃ octadPointwiseKernel O
  actor_zero : (actor 0).val = 1
  vector : Fin 16 → Cocode
  vector_map : ∀ n, map (vector n) = (0, decode n)
  vector_fixed : ∀ n, cocodeRepresentation (actor n).val (vector n) = vector n
  action : ∀ n v, map (cocodeRepresentation (actor n).val v) =
    ((map v).1, (map v).2 + (map v).1 • decode n)

def seedActor : Fin 16 ≃ octadPointwiseKernel seedOctad := Equiv.ofBijective
  (fun n => ⟨translation n, translation_mem n⟩)
  ⟨fun _ _ h => translation_injective (congrArg (fun a : octadPointwiseKernel seedOctad => a.val) h), fun g => by
    obtain ⟨n, hn⟩ := translation_surjective g.val g.property
    exact ⟨n, Subtype.ext hn⟩⟩

def seedModel : CoordinateModel seedOctad where
  map := coordinates
  surjective := coordinates_surjective
  ker := coordinates_ker
  parity := fun _ => rfl
  actor := seedActor
  actor_zero := translation_zero
  vector := direction
  vector_map := coordinates_direction
  vector_fixed := direction_fixed
  action := coordinates_action

def kernelTransport (O P : Octad) (g : M24) (hg : g • O.val = P.val) :
    octadPointwiseKernel O ≃* octadPointwiseKernel P :=
  ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr (octad_kernel_map O P g hg))

lemma kernelTransport_apply (O P : Octad) (g : M24) (hg : g • O.val = P.val)
    (a : octadPointwiseKernel O) : (kernelTransport O P g hg a).val = g * a.val * g⁻¹ := rfl

lemma conjugate_action (g a : M24) (v : Cocode) :
    cocodeRepresentation g⁻¹ (cocodeRepresentation (g * a * g⁻¹) v) =
      cocodeRepresentation a (cocodeRepresentation g⁻¹ v) := by
  rw [map_mul, map_mul]
  simp only [Module.End.mul_apply, action_inv]

/-- Transport uses a literal M24 octad conjugator and the native cocode action. -/
def CoordinateModel.transport {O P : Octad} (C : CoordinateModel O)
    (g : M24) (hg : g • O.val = P.val) : CoordinateModel P where
  map := C.map.comp (cocodeRepresentation g⁻¹)
  surjective := C.surjective.comp (actionEquiv g⁻¹).surjective
  ker := by
    ext v
    change C.map (cocodeRepresentation g⁻¹ v) = 0 ↔ v ∈ supportedPairSpace P.val
    rw [← LinearMap.mem_ker, C.ker]
    constructor
    · intro hv
      have h := supported_transport O.val g hv
      rwa [action_inv', hg] at h
    · intro hv
      have h := supported_transport P.val g⁻¹ hv
      rwa [← hg, inv_smul_smul] at h
  parity := fun v => by
    change (C.map (cocodeRepresentation g⁻¹ v)).1 = _
    rw [C.parity]
    exact (parity_transport O P g hg (cocodeRepresentation g⁻¹ v)).symm.trans
      (congrArg (octadParity P) (action_inv' g v))
  actor := C.actor.trans (kernelTransport O P g hg).toEquiv
  actor_zero := by
    change g * (C.actor 0).val * g⁻¹ = 1
    rw [C.actor_zero, mul_one, mul_inv_cancel]
  vector := fun n => cocodeRepresentation g (C.vector n)
  vector_map := fun n => by
    change C.map (cocodeRepresentation g⁻¹ (cocodeRepresentation g (C.vector n))) = _
    rw [action_inv, C.vector_map]
  vector_fixed := fun n => by
    change cocodeRepresentation (g * (C.actor n).val * g⁻¹)
      (cocodeRepresentation g (C.vector n)) = _
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, action_inv, C.vector_fixed]
  action := fun n v => by
    change C.map (cocodeRepresentation g⁻¹
      (cocodeRepresentation (g * (C.actor n).val * g⁻¹) v)) = _
    rw [conjugate_action, C.action]
    rfl

def model (O : Octad) : CoordinateModel O :=
  seedModel.transport (Classical.choose (exists_smul_octad_eq seedOctad O))
    (Classical.choose_spec (exists_smul_octad_eq seedOctad O))

end
end MathieuCode.CocodeOctad.Dynamics
