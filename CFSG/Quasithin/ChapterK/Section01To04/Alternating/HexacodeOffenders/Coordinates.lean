module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Contracts

/-!
# Actual field coordinates for the recognized triple-six action

The quadratic-algebra field used by the hexacode is identified with the
Galois field used in the corrected B.4.2 contract. Applying that ring
equivalence in each coordinate gives binary coordinates compatible with
all four scalars. The recognition intertwiner then supplies the same
coordinates and field-linearity on the original module. The center and
central quotient are transported through the actual actor equivalence.

These are the structural assertions of K.1.3, Aschbacher–Smith, combined
manuscript of 1 March 2004, printed p.453 (PDF p.464). The offender
calculation is separate; none is assumed in these constructions.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
open ChapterB.QuasisimpleSource

/-- The existing field isomorphism has precisely the carrier required by B.4.2. -/
noncomputable def fieldEquiv : Hexacode.F ≃+* BinaryField.four.Carrier :=
  SL2FourNatural.fieldEquiv

/-- The field isomorphism respects the given binary scalar structures. -/
noncomputable def fieldBinaryEquiv : Hexacode.F ≃ₗ[ZMod 2] BinaryField.four.Carrier where
  toAddEquiv := fieldEquiv.toAddEquiv
  map_smul' c v := by
    fin_cases c
    · change fieldEquiv ((0 : ZMod 2) • v) = (0 : ZMod 2) • fieldEquiv v
      simp
    · change fieldEquiv ((1 : ZMod 2) • v) = (1 : ZMod 2) • fieldEquiv v
      simp

/-- Coefficientwise transport from the quadratic field to the contract field. -/
noncomputable def vectorEquiv :
    (Fin 3 → Hexacode.F) ≃ₗ[ZMod 2] (Fin 3 → BinaryField.four.Carrier) :=
  LinearEquiv.piCongrRight fun _ => fieldBinaryEquiv

/-- Scalar compatibility is with the ring isomorphism, not just cardinalities. -/
theorem vectorEquiv_smul (c : Hexacode.F) (v : Fin 3 → Hexacode.F) :
    vectorEquiv (c • v) = fieldEquiv c • vectorEquiv v := by
  funext i
  exact fieldEquiv.map_mul c (v i)

/-- The model's coordinates in the literal field used by the source contract. -/
noncomputable def modelCoordinates :
    hexacode ≃ₗ[ZMod 2] (Fin 3 → BinaryField.four.Carrier) :=
  Hexacode.binaryCoordinates.trans vectorEquiv

/-- The model coordinate map transports the genuine four-element scalar action. -/
theorem modelCoordinates_smul (c : Hexacode.F) (v : hexacode) :
    modelCoordinates (c • v) = fieldEquiv c • modelCoordinates v := by
  change vectorEquiv (Hexacode.fieldCoordinates (c • v)) = _
  rw [Hexacode.fieldCoordinates.map_smul, vectorEquiv_smul]
  rfl

/-- Even operators are linear in the contract's field coordinates. -/
theorem modelCoordinates_scalar_linear (g : HexEvenAutomorphisms)
    (c : BinaryField.four.Carrier) (v : hexacode) :
    modelCoordinates (Hexacode.evenAction g
      (modelCoordinates.symm (c • modelCoordinates v))) =
      c • modelCoordinates (Hexacode.evenAction g v) := by
  have hs : modelCoordinates.symm (c • modelCoordinates v) = fieldEquiv.symm c • v := by
    apply modelCoordinates.injective
    rw [modelCoordinates.apply_symm_apply, modelCoordinates_smul,
      fieldEquiv.apply_symm_apply]
  rw [hs]
  change modelCoordinates (Hexacode.action g.val (fieldEquiv.symm c • v)) = _
  rw [Hexacode.action_even_smul g.val g.property, modelCoordinates_smul,
    fieldEquiv.apply_symm_apply]
  rfl

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Coordinates on the original recognized module, retaining its binary intertwiner. -/
noncomputable def coordinates (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction) :
    V ≃ₗ[ZMod 2] (Fin 3 → BinaryField.four.Carrier) :=
  e.linearEquiv.trans modelCoordinates

/-- Recognition gives binary dimension six without a separate dimension assumption. -/
theorem dimension (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction) :
    Module.finrank (ZMod 2) V = 6 :=
  e.linearEquiv.finrank_eq.trans hexacode_finrank

/-- The transported coordinates make the literal component action field-linear. -/
theorem coordinates_scalar_linear
    (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction)
    (g : L) (c : BinaryField.four.Carrier) (v : V) :
    coordinates e (ρ g ( (coordinates e).symm (c • coordinates e v))) =
      c • coordinates e (ρ g v) := by
  change modelCoordinates (e.linearEquiv (ρ g
      (e.linearEquiv.symm (modelCoordinates.symm (c • modelCoordinates (e.linearEquiv v)))))) = _
  rw [show ∀ w, e.linearEquiv (ρ g w) =
    Hexacode.evenAction (e.groupEquiv g) (e.linearEquiv w) from e.intertwines g]
  rw [e.linearEquiv.apply_symm_apply, modelCoordinates_scalar_linear]
  rw [← e.intertwines g v]
  rfl

/-- The center is the actual cubic center of the recognized actor. -/
noncomputable def centerEquiv
    (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction) :
    center L ≃* Multiplicative (ZMod 3) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (centerCongr e.groupEquiv).trans
    (mulEquivOfPrimeCardEq Hexacode.even_center_card (by simp))

/-- The equivalence is on the quotient by the literal center of L. -/
noncomputable def quotientEquiv
    (e : ActionEquiv (ρ.comp L.subtype) Hexacode.evenAction) :
    (L ⧸ center L) ≃* alternatingGroup (Fin 6) := by
  refine (QuotientGroup.congr _ _ e.groupEquiv ?_).trans
    Hexacode.even_quotient_center_equiv
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr e.groupEquiv ⟨a, ha⟩).property
  · intro hb
    exact ⟨e.groupEquiv.symm b, (centerCongr e.groupEquiv.symm ⟨b, hb⟩).property,
      e.groupEquiv.apply_symm_apply b⟩

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
