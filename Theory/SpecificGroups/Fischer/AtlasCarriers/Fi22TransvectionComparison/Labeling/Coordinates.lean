module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Certificates
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Geometry

/-!
# Verified bijection from the Fi22 fixed points to isotropic coordinates

The finite checks validate the coordinates of every actual fixed point and the
reverse lookup on every normalized isotropic vector. A checked inverse to the
base-four encoding covers all vectors; finite-field uniqueness and projective
normalization then identify precisely the identity-form model of U₆(2).
No action comparison or centralizer generation is assumed in the bijection.

Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
open KernelCertificate

theorem vector_surjective : Function.Surjective (fun n : Fin 4096 => vector n.val) := by
  apply ((Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩).2
  · intro n m h
    apply Fin.ext
    simpa only [encode_vector] using congrArg encodeVector h
  · simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      show Fintype.card Four = 4 by decide +kernel]
    rfl

theorem decode_spec (v : NormalPoint) :
    fastA (decodeLabel (encodeVector v.val)) = decodeLabel (encodeVector v.val) ∧
      representative (decodeLabel (encodeVector v.val)) = v.val := by
  obtain ⟨n, hn⟩ := vector_surjective v.val
  change vector n.val = v.val at hn
  rw [← hn, encode_vector]
  exact normalizedCode_spec n (by rw [hn]; exact v.property)

/-- Every original fixed point has the displayed normalized isotropic vector. -/
def toNormal (i : FixedPointsA) : NormalPoint :=
  ⟨representative i.val,
    (representative_spec i.val (by rw [← generatorA_apply_eq_fastA]; exact i.property)).1,
    (representative_spec i.val (by rw [← generatorA_apply_eq_fastA]; exact i.property)).2.1⟩

/-- Reverse lookup retains the literal ambient ATLAS label. -/
def ofNormal (v : NormalPoint) : FixedPointsA :=
  ⟨decodeLabel (encodeVector v.val), by
    change generatorA _ = _
    rw [generatorA_apply_eq_fastA]
    exact (decode_spec v).1⟩

theorem ofNormal_toNormal (i : FixedPointsA) : ofNormal (toNormal i) = i := by
  apply Subtype.ext
  exact (representative_spec i.val (by rw [← generatorA_apply_eq_fastA]; exact i.property)).2.2

theorem toNormal_ofNormal (v : NormalPoint) : toNormal (ofNormal v) = v :=
  Subtype.ext (decode_spec v).2

/-- The checked finite coordinate bijection before taking projective classes. -/
def coordinateEquiv : FixedPointsA ≃ NormalPoint where
  toFun := toNormal
  invFun := ofNormal
  left_inv := ofNormal_toNormal
  right_inv := toNormal_ofNormal

/-- A bijective labeling in the actual unitary projective model, including its singleton. -/
noncomputable def labelingEquiv : FixedPointsA ≃ Theory.SpecificGroups.U6Two.PointWithSingleton :=
  coordinateEquiv.trans normalPointEquiv

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
