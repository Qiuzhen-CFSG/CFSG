module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.BinaryNorm
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyProducts
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.FrameGeometry
public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.CanonicalEight.CayleyFlip

/-!
# A canonical elementary eight above every ternary G₂ four-group

The intrinsic norm-line stabilizer is normalized by the whole normalizer of
the four-group. The canonical Cayley frame proves that the selected lines
span the octonions, so their pointwise stabilizer is elementary abelian of
order dividing eight. The actual first-generator sign automorphism fixes
these lines and moves a vector fixed by the four-group. Thus the stabilizer
strictly contains the four-group and has order eight.

The exported extension theorem discharges both geometric premises and retains
containment of the whole ambient normalizer. It supplies the four-group branch
of the ternary maximal-two-local cover without a conjugacy or coverage assumption.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4, and Volume II Theorem 0.1.1(4), pp.481–482.
The recognition hypotheses on p.417 are not used to infer this extension.
The octonion model is the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight

/-- Every elementary four-group in the actual ternary G₂ model lies in an
elementary eight normalized by its whole ambient normalizer. -/
public theorem exists_elementary_eight_extension (E : Subgroup G)
    (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4) :
    ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
      E ≤ F ∧ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (F : Set G) := by
  let := hE
  obtain ⟨a, b, c, ha, hlin, horth, hsel, hexhaust⟩ :=
    exists_canonical_cayley_frame E hcard
  obtain ⟨g, hg⟩ := exists_cayley_frame_flip a b c hlin
    (fun i => selected_norm_ne_zero E (hsel i)) horth
  exact extension_of_cayley_frame_flip E hcard a b c ha hlin hsel hexhaust g hg

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
