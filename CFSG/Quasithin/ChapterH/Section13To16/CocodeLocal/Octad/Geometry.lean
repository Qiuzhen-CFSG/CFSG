module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Defs
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Hyperplane
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Kernel

/-!
# The geometric octad space in H.15.2

The actual span of pair classes inside an octad has dimension six and is
identified, equivariantly for its native stabilizer, with the natural
section of the binary permutation module on that octad. If the octad
contains the point fixed by the native M23, avoiding the M23 weight-two
orbit bounds a subspace's dimension by four. The intrinsic two-core is
identified with pointwise octad fixation and has order sixteen. When the
octad contains point zero, its M23 preimage maps onto the full kernel, so
both fixed spaces and fixed-space spans agree under literal restriction.
The octad-parity hyperplane is constructed independently of its remaining
identification with the fixed-space span.

The equality with the intrinsic two-core fixed space, the orthogonal
action and M24 orbit bound, the fixed-space span and transvection action,
and the involution/pointwise-centralizer calculations remain separate
obligations before full source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.15.2(2–6), printed pp.398–399.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode

/-- The source geometric octad space has dimension six. -/
theorem finrank_octadPairSpace (O : Octad) :
    Module.finrank (ZMod 2) (octadPairSpace O) = 6 :=
  CocodeOctad.finrank_supportedPairSpace O

/-- The explicit linear model, with action compatibility exported by
`MathieuCode.CocodeOctad.naturalEquiv_equivariant`. -/
def octadPairSpaceEquiv (O : Octad) :
    BinaryPermutation.natural O.val ≃ₗ[ZMod 2] octadPairSpace O :=
  CocodeOctad.naturalEquiv O

/-- H.15.2(3), M23: the literal source orbit on an octad through the fixed point. -/
theorem m23_octadPairSpace_avoiding_finrank_le (O : Octad)
    (hO : (0 : Fin 24) ∈ O.val) (I : Submodule (ZMod 2) Cocode)
    (hI : I ≤ octadPairSpace O) (ha : Disjoint (I : Set Cocode) m23WeightTwoOrbit) :
    Module.finrank (ZMod 2) I ≤ 4 :=
  CocodeOctad.m23_avoiding_finrank_le O hO I hI ha

open Representation.BinaryOffender

lemma mem_octadKernel_iff (O : Octad) (g : M24) :
    g ∈ octadKernel O ↔ ∀ i ∈ O.val, g • i = i := by
  change g ∈ (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype ↔ _
  rw [CocodeOctad.core_eq_coordinateKernel]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (CocodeOctad.mem_coordinateAction_ker O u).mp hu
  · intro hg
    have hs : g ∈ octadStabilizer O := by
      apply MulAction.mem_stabilizer_finset'.mpr
      intro i hi
      rwa [hg i hi]
    exact ⟨⟨g, hs⟩, (CocodeOctad.mem_coordinateAction_ker O _).mpr hg, rfl⟩

lemma octadPairSpace_le_fixedSpace (O : Octad) :
    octadPairSpace O ≤ fixedSpace cocodeRepresentation (octadKernel O) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P, hP, rfl⟩ g
  apply (pairVector_fixed_iff g.val P).mpr
  rw [Finset.smul_finset_def]
  calc
    _ = P.val.image id := Finset.image_congr fun i hi =>
      (mem_octadKernel_iff O g.val).mp g.property i (hP hi)
    _ = P.val := Finset.image_id

lemma m23OctadKernel_map (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    (m23OctadKernel O).map pointEmbedding = octadKernel O := by
  change ((octadKernel O).comap pointEmbedding).map pointEmbedding = _
  rw [Subgroup.map_comap_eq, inf_eq_right]
  intro g hg
  rw [pointEmbedding_range]
  exact (mem_octadKernel_iff O g).mp hg 0 hO

lemma m23_octad_fixedSpace_eq (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    fixedSpace m23CocodeRepresentation (m23OctadKernel O) =
      fixedSpace cocodeRepresentation (octadKernel O) := by
  rw [← m23OctadKernel_map O hO]
  ext v
  constructor
  · intro hv g
    obtain ⟨h, hh, he⟩ := g.property
    have hhfix := hv ⟨h, hh⟩
    change cocodeRepresentation (pointEmbedding h) v = v at hhfix
    rw [he] at hhfix
    exact hhfix
  · intro hv h
    exact hv ⟨pointEmbedding h.val, Subgroup.mem_map_of_mem _ h.property⟩

lemma card_octadKernel (O : Octad) : Nat.card (octadKernel O) = 16 := by
  change Nat.card ((pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype) = _
  rw [CocodeOctad.core_eq_coordinateKernel]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (octadStabilizer O).subtype_injective).toEquiv).symm.trans
    (CocodeOctad.card_coordinateKernel O)

lemma octadKernel_elementary (O : Octad) : IsElementaryAbelian 2 (octadKernel O) := by
  have : IsElementaryAbelian 2 (pCore 2 (octadStabilizer O)) :=
    (LinearFourCore.octad_core_structure O).2
  exact IsElementaryAbelian.map (octadStabilizer O).subtype

lemma m23_octad_fixedSpaceSpan_eq (O : Octad) (hO : (0 : Fin 24) ∈ O.val) :
    fixedSpaceSpan m23CocodeRepresentation (m23OctadKernel O) =
      fixedSpaceSpan cocodeRepresentation (octadKernel O) := by
  have h := fixedSpaceSpan_map_equivariant m23CocodeRepresentation cocodeRepresentation
    pointEmbedding pointEmbedding_injective (LinearEquiv.refl (ZMod 2) Cocode)
    (fun _ _ => rfl) (m23OctadKernel O)
  simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id,
    m23OctadKernel_map O hO] using h

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
