module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.DiagonalModel
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.E6Model.Coordinates

/-!
# Transporting the explicit SL3 block action to the E6 end chain

The block representation is an actual homomorphism on the full matrix SL3.
This module transports it through the specified integral coordinate matrix,
proves that its elementary markings force its image into the literal E6
carrier, and applies the existing diagonal action to the complement.

Two explicit obligations remain: bijectivity of the specified coordinates in
odd characteristic and the four signed Geck curve comparisons. These are not
assumed as instances, and this conditional construction does not assert the
unconditional `e6Model`. Final assembly must discharge both obligations.
The entire matrix block is retained, so this route also treats characteristic
three. Source: GLS3 §2.6.2; Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
open WordDescent Matrix
attribute [local instance] Classical.decEq

variable (F : Type*) [Field F]

namespace E6Model

/-- The standard correspondence with linear automorphisms uses the original E6 basis. -/
def ambientEquiv : Ambient F ≃* (Space F ≃ₗ[F] Space F) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Space F))

@[simp] theorem ambientEquiv_apply (g : Ambient F) (v : Space F) :
    ambientEquiv F g v = g.val *ᵥ v := rfl

variable (hc : Function.Bijective (coordinates F))

/-- The explicitly specified coordinate map, once its bijectivity is established. -/
def coordinateEquiv : Space F ≃ₗ[F] BlockSpace F := LinearEquiv.ofBijective (coordinates F) hc

@[simp] theorem coordinateEquiv_apply (v : Space F) :
    coordinateEquiv F hc v = coordinates F v := rfl

/-- Conjugate the genuine block action into the original E6 coordinate space. -/
def linearAction : Model F →* (Space F ≃ₗ[F] Space F) where
  toFun g := (coordinateEquiv F hc).trans ((blockAction F g).trans (coordinateEquiv F hc).symm)
  map_one' := by
    ext v
    simp only [map_one, LinearEquiv.trans_apply, LinearEquiv.coe_one, id_eq,
      LinearEquiv.symm_apply_apply]
  map_mul' g h := by
    ext v
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]

/-- The transported matrices are units before any range assertion is made. -/
def ambientAction : Model F →* Ambient F :=
  (ambientEquiv F).symm.toMonoidHom.comp (linearAction F hc)

variable (hcurve : ∀ (s k : Bool) (t : F) (v : Space F),
  coordinates F ((simpleRoot F s (leftNode k) t).val.val *ᵥ v) =
    blockAction F (modelGenerator F s k t) (coordinates F v))

include hcurve in
/-- The literal signed curve comparison identifies all four transported generators. -/
theorem ambientAction_generator (s k : Bool) (t : F) :
    ambientAction F hc (modelGenerator F s k t) = (simpleRoot F s (leftNode k) t).val := by
  apply (ambientEquiv F).injective
  change ambientEquiv F ((ambientEquiv F).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply LinearEquiv.ext
  intro v
  apply (coordinateEquiv F hc).injective
  change coordinateEquiv F hc ((coordinateEquiv F hc).symm
      (blockAction F (modelGenerator F s k t) (coordinateEquiv F hc v))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (hcurve s k t v).symm

include hcurve in
/-- Elementary generation supplies range containment in the original E6 group. -/
theorem ambientAction_mem (g : Model F) : ambientAction F hc g ∈ splitCarrier F := by
  have htop : (splitCarrier F).comap (ambientAction F hc) = ⊤ := by
    apply model_generates F
    intro s k t
    change ambientAction F hc (modelGenerator F s k t) ∈ splitCarrier F
    rw [ambientAction_generator F hc hcurve]
    exact (simpleRoot F s (leftNode k) t).property
  have hg : g ∈ (splitCarrier F).comap (ambientAction F hc) := by rw [htop]; trivial
  exact hg

end E6Model

/-- Conditional assembly from the fixed coordinate map and its signed comparison. -/
def e6ModelOfCoordinates
    (hc : Function.Bijective (E6Model.coordinates F))
    (hcurve : ∀ (s k : Bool) (t : F) (v : Space F),
      E6Model.coordinates F ((simpleRoot F s (leftNode k) t).val.val *ᵥ v) =
        E6Model.blockAction F (modelGenerator F s k t) (E6Model.coordinates F v)) :
    Model F →* splitCarrier F :=
  (E6Model.ambientAction F hc).codRestrict (splitCarrier F)
    (E6Model.ambientAction_mem F hc hcurve)

@[simp] theorem e6ModelOfCoordinates_generator
    (hc : Function.Bijective (E6Model.coordinates F))
    (hcurve : ∀ (s k : Bool) (t : F) (v : Space F),
      E6Model.coordinates F ((simpleRoot F s (leftNode k) t).val.val *ᵥ v) =
        E6Model.blockAction F (modelGenerator F s k t) (E6Model.coordinates F v))
    (s k : Bool) (t : F) :
    e6ModelOfCoordinates F hc hcurve (modelGenerator F s k t) =
      simpleRoot F s (leftNode k) t := by
  apply Subtype.ext
  exact E6Model.ambientAction_generator F hc hcurve s k t

/-- Apply the actual diagonal E6 action to this representation of the first chain. -/
def e6ComplementActionOfCoordinates
    (hc : Function.Bijective (E6Model.coordinates F))
    (hcurve : ∀ (s k : Bool) (t : F) (v : Space F),
      E6Model.coordinates F ((simpleRoot F s (leftNode k) t).val.val *ᵥ v) =
        E6Model.blockAction F (modelGenerator F s k t) (E6Model.coordinates F v)) :
    Model F →* (complementSpace F ≃ₗ[F] complementSpace F) :=
  modelComplementAction F (e6ModelOfCoordinates F hc hcurve)
    (e6ModelOfCoordinates_generator F hc hcurve)

@[simp] theorem e6ComplementActionOfCoordinates_generator
    (hc : Function.Bijective (E6Model.coordinates F))
    (hcurve : ∀ (s k : Bool) (t : F) (v : Space F),
      E6Model.coordinates F ((simpleRoot F s (leftNode k) t).val.val *ᵥ v) =
        E6Model.blockAction F (modelGenerator F s k t) (E6Model.coordinates F v))
    (s k : Bool) (t : F) :
    e6ComplementActionOfCoordinates F hc hcurve (modelGenerator F s k t) =
      eigenspaceAction F (-1) (f4Simple F s (pairNode 2 3 k) t) :=
  modelComplementAction_generator F _ _ s k t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
