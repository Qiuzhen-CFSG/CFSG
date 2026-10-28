module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Defs
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry

/-!
# The geometric line and invariant pair space for H.15.3

The common tetrad class gives a nonzero line fixed by the entire native sextet
stabilizer. Its containment in the intrinsic two-core fixed space follows from
the two-core inclusion, and its containment in the pair space follows by
splitting a tetrad into two pairs. Equivariance of pair classes makes the pair
space invariant. The resulting subrepresentations specify the literal local
sections without assuming their dimensions or irreducibility.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3,
printed p.400. These are geometric prerequisites, not the four completed
clauses of that lemma.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode Representation.BinaryOffender
open scoped Pointwise

lemma sextetKernel_le_stabilizer (S : Sextet) : sextetKernel S ≤ sextetStabilizer S := by
  rintro g ⟨k, hk, rfl⟩
  exact k.property

lemma sextetTetradLine_le_fixedSpace (S : Sextet) :
    sextetTetradLine S ≤ sextetFixedSpace S := by
  intro v hv g
  exact sextetTetradLine_le_fixed S hv ⟨g.val, sextetKernel_le_stabilizer S g.property⟩

lemma sextetTetradLine_le_pairSpace (S : Sextet) :
    sextetTetradLine S ≤ sextetPairSpace S := by
  obtain ⟨B, hB⟩ := sextet_parts_nonempty S
  rw [sextetTetradLine_eq S hB]
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff]
  have hle : supportedPairSpace B ≤ sextetPairSpace S :=
    le_iSup_of_le B (le_iSup_of_le hB le_rfl)
  exact hle (tetradVector_mem_supportedPairSpace (S.tetrad B hB))

lemma sextetTetradLine_ne_bot (S : Sextet) : sextetTetradLine S ≠ ⊥ := by
  intro h
  have hm : sextetVector S ∈ sextetTetradLine S := Submodule.mem_span_singleton_self _
  rw [h, Submodule.mem_bot] at hm
  exact sextetVector_ne_zero S hm

lemma sextetFixedSpace_ne_bot (S : Sextet) : sextetFixedSpace S ≠ ⊥ := by
  intro h
  apply sextetTetradLine_ne_bot S
  exact bot_unique (h ▸ sextetTetradLine_le_fixedSpace S)

lemma sextetPairSpace_ne_bot (S : Sextet) : sextetPairSpace S ≠ ⊥ := by
  intro h
  apply sextetTetradLine_ne_bot S
  exact bot_unique (h ▸ sextetTetradLine_le_pairSpace S)

lemma sextetPairSpace_invariant (S : Sextet) (g : sextetStabilizer S)
    {v : Cocode} (hv : v ∈ sextetPairSpace S) :
    cocodeRepresentation g.val v ∈ sextetPairSpace S := by
  have hg : g.val • S.parts = S.parts := g.property
  suffices sextetPairSpace S ≤ (sextetPairSpace S).comap (cocodeRepresentation g.val) from
    this hv
  refine iSup_le fun B => iSup_le fun hB => ?_
  rw [← Submodule.map_le_iff_le_comap]
  have hBg : g.val • B ∈ S.parts := hg ▸ Finset.smul_mem_smul_finset hB
  exact (supportedPairSpace_map_le g.val B).trans
    (le_iSup_of_le (g.val • B) (le_iSup_of_le hBg le_rfl))

/-- The native sextet stabilizer acting on the eleven-dimensional cocode. -/
def sextetRepresentation (S : Sextet) : Representation (ZMod 2) (sextetStabilizer S) Cocode :=
  cocodeRepresentation.comp (sextetStabilizer S).subtype

/-- The common tetrad line as an actual subrepresentation of the local action. -/
def sextetLineSubrepresentation (S : Sextet) : Subrepresentation (sextetRepresentation S) where
  toSubmodule := sextetTetradLine S
  apply_mem_toSubmodule g v hv := by
    have he := sextetTetradLine_le_fixed S hv g
    change cocodeRepresentation g.val v = v at he
    change cocodeRepresentation g.val v ∈ sextetTetradLine S
    rw [he]
    exact hv

/-- The span of pairs in individual tetrads as an actual local subrepresentation. -/
def sextetPairSubrepresentation (S : Sextet) : Subrepresentation (sextetRepresentation S) where
  toSubmodule := sextetPairSpace S
  apply_mem_toSubmodule g _ hv := sextetPairSpace_invariant S g hv

/-- The tetrad line inside the seven-dimensional candidate, before its rank is known. -/
def sextetLineInPair (S : Sextet) :
    Subrepresentation (sextetPairSubrepresentation S).toRepresentation where
  toSubmodule := (sextetTetradLine S).comap (sextetPairSpace S).subtype
  apply_mem_toSubmodule g v hv := by
    have he := sextetTetradLine_le_fixed S hv g
    change cocodeRepresentation g.val v.val = v.val at he
    change cocodeRepresentation g.val v.val ∈ sextetTetradLine S
    rw [he]
    exact hv

/-- Weight-two vectors make the geometric containment strict. -/
lemma sextetTetradLine_lt_pairSpace (S : Sextet) :
    sextetTetradLine S < sextetPairSpace S := by
  refine lt_of_le_of_ne (sextetTetradLine_le_pairSpace S) ?_
  intro he
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  obtain ⟨P,hPB,hP⟩ := Finset.exists_subset_card_eq
    (show 2 ≤ B.card by rw [S.tetrad B hB]; decide)
  have hle : supportedPairSpace B ≤ sextetPairSpace S :=
    le_iSup_of_le B (le_iSup_of_le hB le_rfl)
  have hp := hle (pairVector_mem_supportedPairSpace ⟨P,hP⟩ hPB)
  rw [← he] at hp
  exact pairVector_not_mem_sextetTetradLine S ⟨P,hP⟩ hp

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
