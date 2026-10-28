/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetMarkings
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetTrio
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetTransitivity

/-!
# HexacodeSextetPackage

The proved sextet affine equivalence, split extension, recovery maps, marking
compatibility, and trio compatibility are collected into one interface. Every field is
discharged by the concrete coordinate constructions imported here.

Source: `Atlas/Mathieu/HexacodeSextetPackage.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The complete concrete Job 5 construction, with no assumed group orders or fullness. -/
structure HexacodeSextetPackage : Prop where
  hexacode_group : HexacodeAutomorphismPackage
  sextet_geometry : SextetGeometryPackage
  full_stabilizer : ∀ g : Mathieu24CodeModel,
    g ∈ sextetStabilizer ↔ PreservesTetradPartition g.val
  affine_criterion : ∀ (t : HexWord) (g : Monomial HexIndex),
    CodePreserving (affinePermutation t g) ↔ t ∈ hexacode ∧ g ∈ Monomial.stabilizer hexacode
  affine_isomorphism : Function.Bijective sextetAffineHom
  coordinates : ∀ (x : SextetAffineGroup) (i : HexIndex) (k : Fin 4),
    (sextetAffineEquiv x).val.val (i,k) =
      (x.right.val.perm i,rowLabel.symm
        (x.right.val.localMap (x.right.val.perm i) (rowLabel k) +
          x.left.toAdd.val (x.right.val.perm i)))
  inverse_parameters : ∀ s : SextetStabilizer,
    ((sextetAffineEquiv.symm s).left.toAdd.val,(sextetAffineEquiv.symm s).right.val) =
      (partitionTranslation s.val.val ((sextetStabilizer_mem_iff s.val).mp s.prop),
        partitionMonomial s.val.val ((sextetStabilizer_mem_iff s.val).mp s.prop))
  order : Nat.card SextetStabilizer = 138240
  translation_injective : Function.Injective sextetTranslation
  quotient_surjective : Function.Surjective sextetQuotient
  split : sextetQuotient.comp sextetSection = MonoidHom.id _
  translation_kernel : sextetQuotient.ker = sextetTranslation.range
  translation_kernel_order : Nat.card sextetQuotient.ker = 64
  column_kernel_isomorphism : Nonempty (SextetColumnKernelAffine ≃* sextetCoordinateHom.ker)
  column_kernel_order : Nat.card sextetCoordinateHom.ker = 192
  conjugation : ∀ (g : HexAutomorphisms) (t : Multiplicative hexacode),
    sextetSection g * sextetTranslation t * (sextetSection g)⁻¹ =
      sextetTranslation (hexAffineAction g t)
  preserves_C0 : ∀ (s : SextetStabilizer) (w : C0),
    coordinatePermutation s.val.val w.val ∈ C0
  recovery_equivariant : ∀ (s : SextetStabilizer) (w : C0),
    recoverHex (sextetC0Action s w) = hexAction (sextetQuotient s) (recoverHex w)
  preserves_R0 : ∀ (s : SextetStabilizer) (w : C0),
    (sextetC0Action s w).val ∈ R0 ↔ w.val ∈ R0
  translations_trivial_quotient : ∀ (t : Multiplicative hexacode) (w : C0),
    recoverHex (sextetC0Action (sextetTranslation t) w) = recoverHex w
  markings : ∀ (x : SextetAffineGroup) (m : KleinianMarking) (i : HexIndex),
    ∃ e : Equiv.Perm (Fin 2), ∀ s,
      permuteBlock (sextetAffineEquiv x).val.val (markedPair m (i,s)) =
        markedPair (transformedMarking x.right.val m) (x.right.val.perm i,e s)
  trio : ∀ s : SextetStabilizer,
    distinguishedUnorderedTrio.image (permuteBlock s.val.val) = distinguishedUnorderedTrio ↔
      columnPairing.image (fun U => U.image (hexCoordinateHom (sextetQuotient s))) = columnPairing
  stabilizer_transitive : ∀ x y : Omega, ∃ s : SextetStabilizer, s.val.val x = y
  code_group_transitive : ∀ x y : Omega, ∃ g : Mathieu24CodeModel, g.val x = y

theorem hexacode_sextet_package : HexacodeSextetPackage where
  hexacode_group := hexacode_automorphism_package
  sextet_geometry := sextet_geometry_package
  full_stabilizer := sextetStabilizer_mem_iff
  affine_criterion := affine_code_preservation_iff
  affine_isomorphism := sextetAffineHom_bijective
  coordinates := sextetAffineEquiv_coordinates
  inverse_parameters := sextetAffineEquiv_inverse_parameters
  order := sextetStabilizer_card
  translation_injective := sextetTranslation_injective
  quotient_surjective := sextetQuotient_surjective
  split := sextet_section_splits
  translation_kernel := sextetQuotient_kernel
  translation_kernel_order := sextetQuotient_kernel_card
  column_kernel_isomorphism := ⟨sextetColumnKernelEquiv⟩
  column_kernel_order := sextetCoordinate_kernel_card
  conjugation := sextet_translation_conjugation
  preserves_C0 := sextet_preserves_C0
  recovery_equivariant := recoverHex_equivariant
  preserves_R0 := sextet_preserves_R0
  translations_trivial_quotient := sextet_translation_trivial_recovery
  markings := sextet_marking_compatibility
  trio := sextet_trio_iff_pairing
  stabilizer_transitive := sextet_coordinate_transitive
  code_group_transitive := golay_coordinate_transitive

end Atlas.Codes
