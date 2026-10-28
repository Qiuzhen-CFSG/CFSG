module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad
public import Theory.Representation.MathieuCodeRestriction.Orthogonality

/-!
# The octad-parity hyperplane of the native cocode

Self-orthogonality of the Golay code makes intersection parity with an octad
well-defined on the cocode. A pair with one point in the octad makes this
linear functional surjective. Its kernel is therefore a hyperplane of
dimension ten, contains the supported octad pair space, and is invariant
under the native octad stabilizer. It is exactly the image of the octad's
orthogonal space intersected with the even core.

This constructs the geometric candidate for the source fixed-space span;
its equality with that span remains a separate action calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of H.15.2(4–6), printed p.399.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad
noncomputable section

/-- Intersection parity with an octad, descended to the actual cocode. -/
def octadParity (O : Octad) : Cocode →ₗ[ZMod 2] ZMod 2 :=
  codeInCore.liftQ ((dotForm (wordOfSet O.val)).comp Core.subtype) (by
    intro v hv
    exact golay_le_orthogonal hv _ (octad_word_mem O))

@[simp] lemma octadParity_mk (O : Octad) (v : Core) :
    octadParity O (codeInCore.mkQ v) = dotForm (wordOfSet O.val) v.val := rfl

lemma dotForm_wordOfSet (B C : Finset (Fin 24)) :
    dotForm (wordOfSet B) (wordOfSet C) = ((B ∩ C).card : ZMod 2) := by
  change (∑ i, wordOfSet B i * wordOfSet C i) = _
  simp only [wordOfSet, ite_mul, one_mul, zero_mul]
  have h (i : Fin 24) : (if i ∈ B then if i ∈ C then (1 : ZMod 2) else 0 else 0) =
      if i ∈ B ∩ C then 1 else 0 := by
    by_cases hi : i ∈ B <;> by_cases hj : i ∈ C <;> simp [hi, hj]
  simp only [h, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

lemma octadParity_pairVector (O : Octad) (P : PointPair) :
    octadParity O (pairVector P) = ((O.val ∩ P.val).card : ZMod 2) :=
  dotForm_wordOfSet _ _

lemma octadParity_surjective (O : Octad) : Function.Surjective (octadParity O) := by
  have hO : O.val.card = 8 := m24Blocks_card _ O.property
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < O.val.card by omega)
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show O.val.card < (Finset.univ : Finset (Fin 24)).card by simp [hO])
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  let P : PointPair := ⟨{a, b}, by simp [hab]⟩
  have hp : octadParity O (pairVector P) = 1 := by
    rw [octadParity_pairVector]
    have he : O.val ∩ P.val = {a} := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, P]
      aesop
    rw [he]
    simp
  intro c
  refine ⟨c • pairVector P, ?_⟩
  rw [map_smul, hp, smul_eq_mul, mul_one]

/-- The source geometric hyperplane: classes meeting the octad evenly. -/
def octadHyperplane (O : Octad) : Submodule (ZMod 2) Cocode := (octadParity O).ker

lemma finrank_octadHyperplane (O : Octad) :
    Module.finrank (ZMod 2) (octadHyperplane O) = 10 := by
  have h := (octadParity O).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (octadParity_surjective O),
    finrank_top, Module.finrank_self, finrank_cocode] at h
  change Module.finrank (ZMod 2) (octadParity O).ker = 10
  omega

lemma finrank_quotient_octadHyperplane (O : Octad) :
    Module.finrank (ZMod 2) (Cocode ⧸ octadHyperplane O) = 1 := by
  have h := (octadHyperplane O).finrank_quotient_add_finrank
  rw [finrank_octadHyperplane, finrank_cocode] at h
  omega

lemma supportedPairSpace_le_octadHyperplane (O : Octad) :
    supportedPairSpace O.val ≤ octadHyperplane O := by
  apply Submodule.span_le.mpr
  rintro _ ⟨P, hP, rfl⟩
  change octadParity O (pairVector P) = 0
  rw [octadParity_pairVector, Finset.inter_eq_right.mpr hP, P.property]
  decide

/-- The kernel definition is the literal image of the octad orthogonal space
intersected with the even core, as in the printed proof. -/
lemma octadHyperplane_eq_orthogonal_image (O : Octad) :
    octadHyperplane O =
      ((dotForm.orthogonal (Submodule.span (ZMod 2) {wordOfSet O.val})).comap
        Core.subtype).map codeInCore.mkQ := by
  ext v
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective codeInCore v
  constructor
  · intro hv
    refine ⟨w, ?_, rfl⟩
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    change octadParity O (codeInCore.mkQ w) = 0 at hv
    rw [octadParity_mk] at hv
    simp [hv]
  · rintro ⟨u, hu, he⟩
    change octadParity O (codeInCore.mkQ w) = 0
    rw [← he, octadParity_mk]
    exact hu _ (Submodule.subset_span (Set.mem_singleton _))

lemma octadParity_invariant (O : Octad) (g : octadStabilizer O) (v : Cocode) :
    octadParity O (cocodeRepresentation g.val v) = octadParity O v := by
  obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective codeInCore v
  rw [cocodeRepresentation_mk, octadParity_mk, octadParity_mk]
  have hO : fullRepresentation g.val (wordOfSet O.val) = wordOfSet O.val := by
    change BinaryPermutation.representation (Fin 24) g.val.val _ = _
    rw [permute_wordOfSet]
    exact congrArg wordOfSet g.property
  have h := dotForm_invariant g.val (wordOfSet O.val) w.val
  rw [hO] at h
  exact h

lemma octadHyperplane_invariant (O : Octad) (g : octadStabilizer O)
    {v : Cocode} (hv : v ∈ octadHyperplane O) :
    cocodeRepresentation g.val v ∈ octadHyperplane O := by
  change octadParity O (cocodeRepresentation g.val v) = 0
  rw [octadParity_invariant]
  exact hv

end
end MathieuCode.CocodeOctad
