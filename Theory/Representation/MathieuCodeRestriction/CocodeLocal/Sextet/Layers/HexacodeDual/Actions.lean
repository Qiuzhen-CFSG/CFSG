/-
The Golay and affine sextet constructions used here are by Gerald Höhn and
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Their source modules record revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Layers.AtlasModel
public import Theory.Representation.HexacodeAction
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# The actual affine actions on the middle sextet cocode layers

Affine row permutations preserve zero column parity. Differences of whole
columns are even repetitions in Golay, so their cocode classes agree and the
sextet stabilizer fixes the tetrad line pointwise. These facts construct the
literal subrepresentations and the action on the pair space modulo its line.
The semidirect product also identifies the hexacode action with conjugation on
the actual, injectively embedded translation subgroup, for every stabilizer
element.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400; the licensed ATLAS Golay and affine hexacode constructions.
The dual equivalence and irreducibility are separate proof obligations.
-/

@[expose] public section

open scoped BigOperators
open Atlas.Codes
namespace MathieuCode.SextetLayers
noncomputable section

/-- Column parity transforms by the literal permutation of the six columns. -/
lemma atlasColumnParity_equivariant (s : SextetStabilizer) (v : BinaryWord) (i : HexIndex) :
    atlasColumnParity (atlasFullRepresentation s v) i =
      atlasColumnParity v ((hexCoordinateHom (sextetQuotient s)).symm i) := by
  obtain ⟨x, rfl⟩ := sextetAffineEquiv.surjective s
  rw [sextetQuotient_affine]
  let e : Fin 4 ≃ Fin 4 :=
    (((rowLabel.trans (Equiv.subRight (x.left.toAdd.val i))).trans
      (x.right.val.localMap i).symm.toEquiv).trans rowLabel.symm)
  change (∑ k, v (x.right.val.perm.symm i, e k)) = _
  exact Equiv.sum_comp e (fun k => v (x.right.val.perm.symm i, k))

/-- The image of the zero-column-parity space is invariant in the cocode. -/
lemma atlasPairSpace_invariant (g : SextetStabilizer) {v : AtlasCocode}
    (hv : v ∈ atlasPairSpace) : atlasCocodeRepresentation g v ∈ atlasPairSpace := by
  obtain ⟨w, hw, rfl⟩ := hv
  refine ⟨atlasCoreRepresentation g w, ?_, rfl⟩
  change atlasColumnParity (atlasFullRepresentation g w.val) = 0
  ext i
  rw [atlasColumnParity_equivariant]
  exact congrFun hw _

/-- The core action sends a whole column to the corresponding whole column. -/
lemma atlasCoreRepresentation_tetrad (g : SextetStabilizer) (i : HexIndex) :
    atlasCoreRepresentation g (atlasTetradCore i) =
      atlasTetradCore (hexCoordinateHom (sextetQuotient g) i) := by
  obtain ⟨x, rfl⟩ := sextetAffineEquiv.surjective g
  rw [sextetQuotient_affine]
  apply Subtype.ext
  funext p
  change (if x.right.val.perm.symm p.1 = i then (1 : Bit) else 0) =
    if p.1 = x.right.val.perm i then 1 else 0
  simp only [Equiv.symm_apply_eq]

/-- Even repetitions are encoder words with zero hexacode and twist entries. -/
lemma atlasRepetition_le_golay : R0 ≤ golay := by
  rintro v ⟨r, hr, rfl⟩
  exact ⟨(0, ⟨r, hr⟩, 0), by simp [golayEncoder, c0Encoder]⟩

/-- The published core tetrad is the ATLAS repetition of a single coordinate. -/
lemma atlasTetradCore_coe_eq_rho (i : HexIndex) :
    (atlasTetradCore i).val = rho (Pi.single (hexIndexEquiv i) 1) := by
  funext p
  simp [atlasTetradCore, rho, Pi.single_apply, eq_comm]

/-- Any two entire columns differ by a Golay word. -/
lemma atlasTetradClass_eq (i j : HexIndex) :
    atlasCodeInCore.mkQ (atlasTetradCore i) = atlasCodeInCore.mkQ (atlasTetradCore j) := by
  apply (Submodule.Quotient.eq atlasCodeInCore).mpr
  change (atlasTetradCore i).val - (atlasTetradCore j).val ∈ golay
  rw [atlasTetradCore_coe_eq_rho, atlasTetradCore_coe_eq_rho, ← map_sub]
  apply atlasRepetition_le_golay
  refine ⟨_, ?_, rfl⟩
  apply (parityCode_mem 5 _).mpr
  simp [Finset.sum_sub_distrib]

/-- The common tetrad class is fixed by the entire sextet stabilizer. -/
lemma atlasTetradClass_fixed (g : SextetStabilizer) :
    atlasCocodeRepresentation g (atlasCodeInCore.mkQ (atlasTetradCore (0,0))) =
      atlasCodeInCore.mkQ (atlasTetradCore (0,0)) := by
  rw [atlasCocodeRepresentation_mk, atlasCoreRepresentation_tetrad]
  exact atlasTetradClass_eq _ _

/-- The specified tetrad line is fixed pointwise. -/
lemma atlasTetradLine_fixed (g : SextetStabilizer) {v : AtlasCocode}
    (hv : v ∈ atlasTetradLine) : atlasCocodeRepresentation g v = v := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, atlasTetradClass_fixed]

/-- The hexacode action is exactly conjugation on the actual translation subgroup. -/
lemma atlasHexacodeAction_translation_conjugation (s : SextetStabilizer) (t : Multiplicative hexacode) :
    s * sextetTranslation t * s⁻¹ =
      sextetTranslation (Multiplicative.ofAdd
        ((Representation.Hexacode.action.comp sextetQuotient) s t.toAdd)) := by
  obtain ⟨x, rfl⟩ := sextetAffineEquiv.surjective s
  have he : x * SemidirectProduct.inl t * x⁻¹ =
      SemidirectProduct.inl (hexAffineAction x.right t) := by
    apply SemidirectProduct.ext
    · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, mul_comm]
    · simp
  change _ = sextetTranslation
    (Multiplicative.ofAdd (hexAction (sextetQuotient (sextetAffineEquiv x)) t.toAdd))
  rw [sextetQuotient_affine]
  change sextetAffineEquiv x * sextetAffineEquiv (SemidirectProduct.inl t) *
      (sextetAffineEquiv x)⁻¹ =
    sextetAffineEquiv (SemidirectProduct.inl (hexAffineAction x.right t))
  rw [← map_inv, ← map_mul, ← map_mul, he]

/-- The actual pair space as a subrepresentation of the cocode. -/
def atlasPairSubrepresentation : Subrepresentation atlasCocodeRepresentation where
  toSubmodule := atlasPairSpace
  apply_mem_toSubmodule := atlasPairSpace_invariant

/-- The actual tetrad line as a subrepresentation of the cocode. -/
def atlasTetradSubrepresentation : Subrepresentation atlasCocodeRepresentation where
  toSubmodule := atlasTetradLine
  apply_mem_toSubmodule g _ hv := (atlasTetradLine_fixed g hv).symm ▸ hv

/-- Restriction of the cocode action to the specified pair space. -/
abbrev atlasPairRepresentation := atlasPairSubrepresentation.toRepresentation

/-- The pullback of the tetrad line inside the pair representation. -/
def atlasLineInPairSubrepresentation : Subrepresentation atlasPairRepresentation where
  toSubmodule := atlasLineInPair
  apply_mem_toSubmodule g v hv := by
    change atlasCocodeRepresentation g v.val ∈ atlasTetradLine
    have hv' : v.val ∈ atlasTetradLine := hv
    rw [atlasTetradLine_fixed g hv']
    exact hv'

/-- The exact middle quotient, with the published pullback denominator. -/
abbrev AtlasMiddle := atlasPairSpace ⧸ atlasLineInPair

/-- The induced action on the literal middle quotient. -/
def atlasMiddleRepresentation : Representation Bit SextetStabilizer AtlasMiddle :=
  atlasPairRepresentation.quotient atlasLineInPair
    atlasLineInPairSubrepresentation.apply_mem_toSubmodule

/-- The quotient action on a representative from the pair space. -/
lemma atlasMiddleRepresentation_mk (g : SextetStabilizer) (v : atlasPairSpace) :
    atlasMiddleRepresentation g (atlasLineInPair.mkQ v) =
      atlasLineInPair.mkQ (atlasPairRepresentation g v) := rfl

end
end MathieuCode.SextetLayers
