module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Basic
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Dynamics.Transport
/-!
# Full native octad transvections and conjugation equivariance

The moment quotient identifies the kernel's native displacements bijectively
with the geometric axis. Composition of the actual quotient actions proves
that this bijection is a group isomorphism to the additive axis. Conjugating
the action and evaluating on a parity-one vector proves stabilizer
equivariance. The image is exactly all transvections with this parity and
axis, and the kernel acts trivially on the axis.

Source: Aschbacher--Smith, H.15.2(6), printed p.399.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.CocodeOctad.Dynamics
open SmallKernelFixed
noncomputable section

abbrev Axis (O : Octad) : Submodule (ZMod 2) (Cocode ⧸ octadPairSpace O) :=
  (octadHyperplane O).map (octadPairSpace O).mkQ

def pairSubrepresentation (O : Octad) : Subrepresentation (cocodeRepresentation.comp (octadStabilizer O).subtype) where
  toSubmodule := octadPairSpace O
  apply_mem_toSubmodule g _ hv := supportedPairSpace_invariant O.val g.val g.property hv

abbrev quotientRepresentation (O : Octad) :
    Representation (ZMod 2) (octadStabilizer O) (Cocode ⧸ octadPairSpace O) :=
  (pairSubrepresentation O).quotientRepresentation

lemma quotientRepresentation_mk (O : Octad) (g : octadStabilizer O) (v : Cocode) :
    quotientRepresentation O g ((octadPairSpace O).mkQ v) =
      (octadPairSpace O).mkQ (cocodeRepresentation g.val v) := rfl

lemma kernel_le_stabilizer (O : Octad) : octadPointwiseKernel O ≤ octadStabilizer O := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

lemma kernel_normalizes (O : Octad) :
    octadStabilizer O ≤ Subgroup.normalizer (octadPointwiseKernel O : Set M24) := by
  have h := (LinearFourCore.action O).ker.le_normalizer_map (octadStabilizer O).subtype
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

def kernelConjugate (O : Octad) (g : octadStabilizer O) (a : octadPointwiseKernel O) :
    octadPointwiseKernel O :=
  ⟨g.val * a.val * g.val⁻¹, (Subgroup.mem_normalizer_iff.mp (kernel_normalizes O g.property) a.val).mp a.property⟩

namespace CoordinateModel
variable {O : Octad} (C : CoordinateModel O)
include C

def quotientCoordinates : (Cocode ⧸ octadPairSpace O) ≃ₗ[ZMod 2] (ZMod 2 × E) :=
  (Submodule.quotEquivOfEq _ _ C.ker.symm).trans (C.map.quotKerEquivOfSurjective C.surjective)

lemma quotientCoordinates_mk (v : Cocode) :
    C.quotientCoordinates ((octadPairSpace O).mkQ v) = C.map v := rfl

lemma vector_parity (n : Fin 16) : C.vector n ∈ octadHyperplane O := by
  change octadParity O (C.vector n) = 0
  rw [← C.parity, C.vector_map]

def axisDirection (a : octadPointwiseKernel O) : Axis O :=
  ⟨(octadPairSpace O).mkQ (C.vector (C.actor.symm a)),
    ⟨C.vector (C.actor.symm a), C.vector_parity _, rfl⟩⟩

lemma axisDirection_coordinates (a : octadPointwiseKernel O) :
    C.quotientCoordinates (C.axisDirection a).val = (0, decode (C.actor.symm a)) := by
  exact C.vector_map _

lemma axisDirection_injective : Function.Injective C.axisDirection := by
  intro a b h
  have he := congrArg (fun x : Axis O => C.quotientCoordinates x.val) h
  rw [C.axisDirection_coordinates, C.axisDirection_coordinates] at he
  exact C.actor.symm.injective (decode_bijective.1 (congrArg Prod.snd he))

lemma axisDirection_surjective : Function.Surjective C.axisDirection := by
  intro x
  obtain ⟨v, hv, hx⟩ := x.property
  obtain ⟨n, hn⟩ := decode_bijective.2 (C.map v).2
  refine ⟨C.actor n, ?_⟩
  apply Subtype.ext
  apply C.quotientCoordinates.injective
  rw [C.axisDirection_coordinates, Equiv.symm_apply_apply, ← hx, C.quotientCoordinates_mk]
  apply Prod.ext
  · exact ((C.parity v).trans hv).symm
  · exact hn

lemma action_mk (a : octadPointwiseKernel O) (v : Cocode) :
    (octadPairSpace O).mkQ (cocodeRepresentation a.val v) =
      (octadPairSpace O).mkQ v + octadParity O v • (C.axisDirection a).val := by
  apply C.quotientCoordinates.injective
  rw [map_add, map_smul, C.quotientCoordinates_mk, C.quotientCoordinates_mk,
    C.axisDirection_coordinates]
  obtain ⟨n, rfl⟩ := C.actor.surjective a
  rw [C.action, Equiv.symm_apply_apply]
  apply Prod.ext
  · change (C.map v).1 = (C.map v).1 + octadParity O v * 0
    rw [mul_zero, add_zero]
  · change (C.map v).2 + (C.map v).1 • decode n =
      (C.map v).2 + octadParity O v • decode n
    rw [C.parity]

lemma axisDirection_mul (a b : octadPointwiseKernel O) :
    C.axisDirection (a * b) = C.axisDirection a + C.axisDirection b := by
  obtain ⟨v, hv⟩ := octadParity_surjective O 1
  apply Subtype.ext
  have h : (octadPairSpace O).mkQ v + (C.axisDirection (a * b)).val =
      (octadPairSpace O).mkQ v + ((C.axisDirection a).val + (C.axisDirection b).val) := by
    calc
      _ = (octadPairSpace O).mkQ (cocodeRepresentation (a * b).val v) := by
        rw [C.action_mk, hv, one_smul]
      _ = (octadPairSpace O).mkQ (cocodeRepresentation a.val (cocodeRepresentation b.val v)) := by
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      _ = _ := by
        rw [C.action_mk, C.action_mk,
          octadParity_invariant O ⟨b.val, kernel_le_stabilizer O b.property⟩ v, hv, one_smul]
        simp only [one_smul]
        abel
  exact add_left_cancel h

def transvectionHom : octadPointwiseKernel O →* Multiplicative (Axis O) where
  toFun a := Multiplicative.ofAdd (C.axisDirection a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change C.axisDirection 1 = 0
    have h := C.axisDirection_mul 1 1
    rw [one_mul] at h
    exact (add_eq_left.mp h.symm)
  map_mul' a b := congrArg Multiplicative.ofAdd (C.axisDirection_mul a b)

def transvectionEquiv : octadPointwiseKernel O ≃* Multiplicative (Axis O) :=
  MulEquiv.ofBijective C.transvectionHom
    ⟨fun _ _ h => C.axisDirection_injective (Multiplicative.ofAdd.injective h),
      fun x => by
        obtain ⟨a, ha⟩ := C.axisDirection_surjective x.toAdd
        exact ⟨a, congrArg Multiplicative.ofAdd ha⟩⟩

lemma transvectionEquiv_action (a : octadPointwiseKernel O) (v : Cocode) :
    (octadPairSpace O).mkQ (cocodeRepresentation a.val v) =
      (octadPairSpace O).mkQ v + octadParity O v • (C.transvectionEquiv a).toAdd.val :=
  C.action_mk a v

lemma transvectionEquiv_conjugation (g : octadStabilizer O) (a : octadPointwiseKernel O) :
    (C.transvectionEquiv (kernelConjugate O g a)).toAdd.val =
      quotientRepresentation O g (C.transvectionEquiv a).toAdd.val := by
  obtain ⟨v, hv⟩ := octadParity_surjective O 1
  have hi : octadParity O (cocodeRepresentation g.val⁻¹ v) = 1 :=
    (octadParity_invariant O g⁻¹ v).trans hv
  have h : (octadPairSpace O).mkQ v + (C.axisDirection (kernelConjugate O g a)).val =
      (octadPairSpace O).mkQ v + quotientRepresentation O g (C.axisDirection a).val := by
    calc
      _ = (octadPairSpace O).mkQ (cocodeRepresentation (kernelConjugate O g a).val v) := by
        rw [C.action_mk, hv, one_smul]
      _ = quotientRepresentation O g
          ((octadPairSpace O).mkQ (cocodeRepresentation a.val (cocodeRepresentation g.val⁻¹ v))) := by
        rw [quotientRepresentation_mk]
        change (octadPairSpace O).mkQ (cocodeRepresentation (g.val * a.val * g.val⁻¹) v) = _
        rw [map_mul, map_mul]
        rfl
      _ = _ := by
        rw [C.action_mk, map_add, map_smul, quotientRepresentation_mk, action_inv', hi, one_smul]
  exact add_left_cancel h

lemma full_transvection_image :
    Set.range (fun a : octadPointwiseKernel O =>
      quotientRepresentation O ⟨a.val, kernel_le_stabilizer O a.property⟩) =
    Set.range (fun x : Axis O => quotientTransvection O x.val) := by
  have he (a : octadPointwiseKernel O) :
      quotientRepresentation O ⟨a.val, kernel_le_stabilizer O a.property⟩ =
        quotientTransvection O (C.axisDirection a).val := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (octadPairSpace O).mkQ_surjective x
    exact C.action_mk a v
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨C.axisDirection a, (he a).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := C.axisDirection_surjective x
    exact ⟨a, he a⟩

end CoordinateModel

def octadTransvectionEquiv (O : Octad) : octadPointwiseKernel O ≃* Multiplicative (Axis O) :=
  (model O).transvectionEquiv

lemma octadTransvectionEquiv_action (O : Octad) (a : octadPointwiseKernel O) (v : Cocode) :
    (octadPairSpace O).mkQ (cocodeRepresentation a.val v) =
      (octadPairSpace O).mkQ v + octadParity O v • (octadTransvectionEquiv O a).toAdd.val :=
  (model O).transvectionEquiv_action a v

lemma octadTransvectionEquiv_conjugation (O : Octad) (g : octadStabilizer O)
    (a : octadPointwiseKernel O) :
    (octadTransvectionEquiv O (kernelConjugate O g a)).toAdd.val =
      quotientRepresentation O g (octadTransvectionEquiv O a).toAdd.val :=
  (model O).transvectionEquiv_conjugation g a

lemma octad_full_transvection_image (O : Octad) :
    Set.range (fun a : octadPointwiseKernel O =>
      quotientRepresentation O ⟨a.val, kernel_le_stabilizer O a.property⟩) =
    Set.range (fun x : Axis O => quotientTransvection O x.val) :=
  (model O).full_transvection_image


lemma octadTransvectionEquiv_action_quotient (O : Octad) (a : octadPointwiseKernel O)
    (x : Cocode ⧸ octadPairSpace O) :
    quotientRepresentation O ⟨a.val, kernel_le_stabilizer O a.property⟩ x =
      x + quotientOctadParity O x • (octadTransvectionEquiv O a).toAdd.val := by
  obtain ⟨v, rfl⟩ := (octadPairSpace O).mkQ_surjective x
  exact octadTransvectionEquiv_action O a v

lemma quotientParity_axis (O : Octad) (x : Axis O) : quotientOctadParity O x.val = 0 := by
  obtain ⟨v, hv, he⟩ := x.property
  rw [← he, quotientOctadParity_mkQ]
  exact hv

lemma kernel_fixes_axis (O : Octad) (a : octadPointwiseKernel O) (x : Axis O) :
    quotientRepresentation O ⟨a.val, kernel_le_stabilizer O a.property⟩ x.val = x.val := by
  rw [octadTransvectionEquiv_action_quotient, quotientParity_axis, zero_smul, add_zero]

/-- The axis has the actual induced octad-stabilizer action. -/
def axisRepresentation (O : Octad) : Representation (ZMod 2) (octadStabilizer O) (Axis O) where
  toFun g := (quotientRepresentation O g).restrict (fun x hx => by
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨cocodeRepresentation g.val v, octadHyperplane_invariant O g hv, rfl⟩)
  map_one' := by
    ext x
    exact LinearMap.congr_fun (map_one (quotientRepresentation O)) x.val
  map_mul' g h := by
    ext x
    exact LinearMap.congr_fun (map_mul (quotientRepresentation O) g h) x.val

lemma octadTransvectionEquiv_equivariant (O : Octad) (g : octadStabilizer O)
    (a : octadPointwiseKernel O) :
    (octadTransvectionEquiv O (kernelConjugate O g a)).toAdd =
      axisRepresentation O g (octadTransvectionEquiv O a).toAdd := by
  apply Subtype.ext
  exact octadTransvectionEquiv_conjugation O g a

end
end MathieuCode.CocodeOctad.Dynamics
