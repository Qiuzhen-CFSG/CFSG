module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.CoordinateTransport.Coordinates

/-!
# Transport of the sextet part action and affine translations

Given compatible point coordinates and a group equivalence, the actual action
on native tetrads is conjugate to the ATLAS column action. Its surjectivity and
kernel order 192 follow from the concrete hexacode calculation. Transporting the
affine inclusion gives a normal subgroup of order 64, with its full conjugation
action equal to the hexacode action through the affine quotient.

The marking and compatible group equivalence are explicit inputs here. The
unconditional coordinate construction and automorphism comparison remain the
responsibility of `CoordinateTransport`; none of these conditional transport
lemmas asserts either existence. No intrinsic prime-core identification is made.

Source: Aschbacher–Smith H.15.3(1), printed p.400. The ATLAS affine construction
is by Gerald Höhn and ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917, under the ATLAS Research and Attribution
License 1.0; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.SextetLayers.CoordinateTransport
noncomputable section

variable {S : Sextet} (m : Marking S)
  (e : Atlas.Codes.SextetStabilizer ≃* sextetStabilizer S)
  (he : ∀ s p, (e s).val.val (m.pointEquiv p) = m.pointEquiv (s.val.val p))

include he in
lemma partPerm_apply (s : Atlas.Codes.SextetStabilizer) (i : Atlas.Codes.HexIndex) :
    sextetPartPerm S (e s) (m.partEquiv i) =
      m.partEquiv (Atlas.Codes.hexCoordinateHom (Atlas.Codes.sextetQuotient s) i) := by
  apply sextetPart_eq_of_mem S _ _ (i := m.pointEquiv (s.val.val (i,0)))
  · rw [sextetPartPerm_apply, ← he s (i,0)]
    exact Finset.smul_mem_smul_finset ((m.mem_part (i,0) i).mpr rfl)
  · apply (m.mem_part _ _).mpr
    exact Atlas.Codes.sextet_coordinate_compatibility s i 0

include he in
lemma partPerm_eq (s : Atlas.Codes.SextetStabilizer) :
    sextetPartPerm S (e s) = m.partEquiv.permCongr
      (Atlas.Codes.hexCoordinateHom (Atlas.Codes.sextetQuotient s)) := by
  apply Equiv.ext
  intro B
  obtain ⟨i,rfl⟩ := m.partEquiv.surjective B
  simpa using partPerm_apply m e he s i

include he in
lemma partPerm_surjective : Function.Surjective (sextetPartPerm S) := by
  intro σ
  obtain ⟨h,hh⟩ := Atlas.Codes.hexCoordinateHom_surjective (m.partEquiv.symm.permCongr σ)
  obtain ⟨s,hs⟩ := Atlas.Codes.sextetQuotient_surjective h
  refine ⟨e s, ?_⟩
  rw [partPerm_eq m e he, hs, hh]
  exact m.partEquiv.permCongr.apply_symm_apply σ

include he in
lemma partPerm_kernel_comap :
    (sextetPartPerm S).ker.comap e.toMonoidHom = Atlas.Codes.sextetCoordinateHom.ker := by
  ext s
  change sextetPartPerm S (e s) = 1 ↔ Atlas.Codes.sextetCoordinateHom s = 1
  rw [partPerm_eq m e he]
  change m.partEquiv.permCongrHom _ = 1 ↔
    Atlas.Codes.hexCoordinateSixHom (Atlas.Codes.sextetQuotient s) = 1
  rw [m.partEquiv.permCongrHom.map_eq_one_iff, Atlas.Codes.hexSix_eq_one]

include he in
lemma partPerm_kernel_map : (sextetPartPerm S).ker =
    Atlas.Codes.sextetCoordinateHom.ker.map e.toMonoidHom := by
  rw [← partPerm_kernel_comap m e he]
  exact (Subgroup.map_comap_eq_self_of_surjective e.surjective _).symm

include he in
lemma partPerm_kernel_card : Nat.card (sextetPartPerm S).ker = 192 := by
  rw [partPerm_kernel_map m e he, Subgroup.card_map_of_injective e.injective,
    Atlas.Codes.sextetCoordinate_kernel_card]

/-- The transported affine translations, in the actual native stabilizer. -/
def translation : Multiplicative Atlas.Codes.hexacode →* sextetStabilizer S :=
  e.toMonoidHom.comp Atlas.Codes.sextetTranslation

lemma translation_injective : Function.Injective (translation e) :=
  e.injective.comp Atlas.Codes.sextetTranslation_injective

/-- The affine quotient, with no identification with a prime core asserted. -/
def quotient : sextetStabilizer S →* Atlas.Codes.HexAutomorphisms :=
  Atlas.Codes.sextetQuotient.comp e.symm.toMonoidHom

lemma quotient_translation (t : Multiplicative Atlas.Codes.hexacode) :
    quotient e (translation e t) = 1 := by
  change Atlas.Codes.sextetQuotient (e.symm (e (Atlas.Codes.sextetTranslation t))) = 1
  rw [e.symm_apply_apply, Atlas.Codes.sextetQuotient_translation]

lemma quotient_surjective : Function.Surjective (quotient e) :=
  Atlas.Codes.sextetQuotient_surjective.comp e.symm.surjective

lemma quotient_kernel : (quotient e).ker = (translation e).range := by
  ext g
  constructor
  · intro hg
    have hx : e.symm g ∈ Atlas.Codes.sextetTranslation.range := by
      rw [← Atlas.Codes.sextetQuotient_kernel]
      exact hg
    obtain ⟨t,ht⟩ := hx
    exact ⟨t, (congrArg e ht).trans (e.apply_symm_apply g)⟩
  · rintro ⟨t,rfl⟩
    exact quotient_translation e t

lemma translation_normal : (translation e).range.Normal := by
  rw [← quotient_kernel e]
  infer_instance

lemma translation_card : Nat.card (translation e).range = 64 := by
  rw [translation, MonoidHom.range_comp, Subgroup.card_map_of_injective e.injective,
    ← Atlas.Codes.sextetQuotient_kernel, Atlas.Codes.sextetQuotient_kernel_card]

private lemma atlas_conjugation (s : Atlas.Codes.SextetStabilizer)
    (t : Multiplicative Atlas.Codes.hexacode) :
    s * Atlas.Codes.sextetTranslation t * s⁻¹ =
      Atlas.Codes.sextetTranslation (Atlas.Codes.hexAffineAction (Atlas.Codes.sextetQuotient s) t) := by
  obtain ⟨x,rfl⟩ := Atlas.Codes.sextetAffineEquiv.surjective s
  rw [Atlas.Codes.sextetQuotient_affine]
  change Atlas.Codes.sextetAffineEquiv x *
    Atlas.Codes.sextetAffineEquiv (SemidirectProduct.inl t) *
      (Atlas.Codes.sextetAffineEquiv x)⁻¹ =
    Atlas.Codes.sextetAffineEquiv (SemidirectProduct.inl (Atlas.Codes.hexAffineAction x.right t))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply SemidirectProduct.ext
  · simp [mul_comm, mul_assoc]
  · simp

/-- The full native conjugation action is the ATLAS hexacode action. -/
lemma translation_conjugation (g : sextetStabilizer S) (t : Multiplicative Atlas.Codes.hexacode) :
    g * translation e t * g⁻¹ =
      translation e (Multiplicative.ofAdd (Atlas.Codes.hexAction (quotient e g) t.toAdd)) := by
  obtain ⟨s,rfl⟩ := e.surjective g
  have h := congrArg e (atlas_conjugation s t)
  simp only [map_mul, map_inv] at h
  change e s * e (Atlas.Codes.sextetTranslation t) * (e s)⁻¹ =
    e (Atlas.Codes.sextetTranslation (Atlas.Codes.hexAffineAction
      (Atlas.Codes.sextetQuotient (e.symm (e s))) t))
  rw [e.symm_apply_apply]
  exact h

include he in
lemma cocode_equivariant (s : Atlas.Codes.SextetStabilizer) (v : AtlasCocode) :
    m.cocodeEquiv (atlasCocodeRepresentation s v) =
      cocodeRepresentation (e s).val (m.cocodeEquiv v) :=
  m.cocodeEquiv_equivariant s (e s).val (he s) v

end
end MathieuCode.SextetLayers.CoordinateTransport
