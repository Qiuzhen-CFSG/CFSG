/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/HigmanSimsLattice.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsSimplicity
public import Theory.AtlasPort.OtherSporadic.Conway.LeechPlaneComplement
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2

/-!
Lattice representations and Conway embeddings of Higman–Sims.
The marked triangle defines a faithful rank-22 integral representation and compatible injections into Conway stabilizers.

Source: Gerald Höhn, `Atlas/Sporadic/HigmanSimsLattice.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway

def vector : leech := Conway3.vector.val

theorem triangle_gram : integerDot vector.val vector.val = 48 ∧
    integerDot endpoint.val endpoint.val = 32 ∧ integerDot vector.val endpoint.val = 16 :=
  ⟨normSixVector_norm _,hs_endpoint_norm,hs_normSix_endpoint_dot⟩

theorem finite : Finite Model := inferInstance

def toConway3 : Model →* Conway3.Model := (MulAction.stabilizer Conway3.Model endpoint).subtype

theorem toConway3_injective : Function.Injective toConway3 := Subtype.val_injective

def embedding : Model →* LeechIsometryGroup := Conway3.embedding.comp toConway3

theorem embedding_injective : Function.Injective embedding :=
  Conway3.embedding_injective.comp toConway3_injective

def toConway1 : Model →* LeechCentralQuotient := Conway3.toConway1.comp toConway3

theorem toConway1_injective : Function.Injective toConway1 :=
  Conway3.toConway1_injective.comp toConway3_injective

abbrev Complement := leechPlaneComplement vector endpoint

theorem plane_gram_determinant : leechPlaneGramDet vector endpoint = 1280 := by
  unfold leechPlaneGramDet
  rw [triangle_gram.1,triangle_gram.2.1,triangle_gram.2.2]
  norm_num

theorem complement_rank : Module.finrank ℤ Complement = 22 :=
  leechPlaneComplement_rank vector endpoint (by rw [triangle_gram.1]; decide)
    (by rw [plane_gram_determinant]; decide)

theorem complement_free : Module.Free ℤ Complement := inferInstance

theorem complement_finite : Module.Finite ℤ Complement := inferInstance

def integralRepresentation : Model →* (Complement ≃ₗ[ℤ] Complement) :=
  leechPlaneRepresentation vector endpoint

theorem integralRepresentation_injective : Function.Injective integralRepresentation :=
  leechPlaneRepresentation_injective vector endpoint (by rw [plane_gram_determinant]; decide)

theorem integralRepresentation_preserves (g : Model) (z t : Complement) :
    integerDot (integralRepresentation g z).val.val (integralRepresentation g t).val.val =
      integerDot z.val.val t.val.val := leechPlaneRepresentation_preserves vector endpoint g z t

theorem normFourTransporter_exists : ∃ t : LeechIsometryGroup, t.val endpoint = Conway2.vector.val := by
  let := full_minimum_pretransitive
  obtain ⟨t,ht⟩ := MulAction.exists_smul_eq LeechIsometryGroup
    (show LeechShell 4 from ⟨endpoint,triangle_gram.2.1⟩) Conway2.vector
  exact ⟨t,congrArg Subtype.val ht⟩

def normFourTransporter : LeechIsometryGroup := Classical.choose normFourTransporter_exists

theorem normFourTransporter_spec : normFourTransporter.val endpoint = Conway2.vector.val :=
  Classical.choose_spec normFourTransporter_exists

def toNormFourStabilizer : Model →* fullVectorStabilizer endpoint where
  toFun g := ⟨g.val.val,g.prop⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def normFourStabilizerEquiv : fullVectorStabilizer endpoint ≃* Conway2.Model :=
  MulAction.stabilizerEquivStabilizer (show Conway2.vector.val = normFourTransporter • endpoint from
    normFourTransporter_spec.symm)

def toConway2 : Model →* Conway2.Model := normFourStabilizerEquiv.toMonoidHom.comp toNormFourStabilizer

theorem toConway2_injective : Function.Injective toConway2 := by
  apply normFourStabilizerEquiv.injective.comp
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun k : fullVectorStabilizer endpoint => (k : LeechIsometryGroup)) he

theorem toConway2_compatible (g : Model) : Conway2.embedding (toConway2 g) =
    normFourTransporter*embedding g*normFourTransporter⁻¹ := by
  exact MulAction.stabilizerEquivStabilizer_apply normFourTransporter_spec.symm (toNormFourStabilizer g)

theorem toConway3_compatible (g : Model) : Conway3.embedding (toConway3 g) = embedding g := rfl

theorem toConway1_via_conway3 (g : Model) : Conway3.toConway1 (toConway3 g) = toConway1 g := rfl

theorem toConway1_via_conway2 (g : Model) : Conway2.toConway1 (toConway2 g) =
    leechCentralProjection normFourTransporter*toConway1 g*(leechCentralProjection normFourTransporter)⁻¹ := by
  change leechCentralProjection (Conway2.embedding (toConway2 g)) =
    leechCentralProjection normFourTransporter*leechCentralProjection (embedding g)*
      (leechCentralProjection normFourTransporter)⁻¹
  have he := congrArg leechCentralProjection (toConway2_compatible g)
  simpa only [map_mul,map_inv] using he

theorem co2_index_product : 953856*Nat.card Model = Nat.card Conway2.Model := by
  rw [card,Conway2.card]
  rfl

theorem co3_index_product : 11178*Nat.card Model = Nat.card Conway3.Model := conway3_order_identity

theorem mathieu22Embedding_range : mathieu22Embedding.range = PointStabilizer := by
  ext g
  constructor
  · rintro ⟨p,rfl⟩
    exact (pointStabilizerEquiv p).prop
  · intro hg
    obtain ⟨p,hp⟩ := pointStabilizerEquiv.surjective ⟨g,hg⟩
    exact ⟨p,congrArg Subtype.val hp⟩

theorem pointStabilizerEquiv_compatible (g : MathieuModel) :
    (pointStabilizerEquiv g).val = mathieu22Embedding g := rfl

end Atlas.Sporadic.HigmanSims
