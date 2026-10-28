module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.Spaces

/-!
# Recovering the native quintet from its code subspace

The coordinate pairing identifies membership in `V4` with constancy of a
Golay representative on each of the six compatible tetrads. This criterion
holds for every representative of the code class: it is obtained through
both literal cocode quotients and the quotient of Golay by the constant line.

The five octads formed by adjoining another tetrad to `{0,2,9,14}` give
vectors in `V4`. Their coordinate values distinguish the six tetrads. Hence
a permutation preserving `V4` sends each tetrad into a tetrad; their equal
sizes make these containments equalities. This proves the native setwise
stabilizer equality without fixed-space dimensions or irreducibility.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
the setwise stabilizer step in the proof of H.16.3(4), printed p.403.
The compatible sextet and its octads are certified in `M22.LocalStructure`.
-/

public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped BigOperators Pointwise
namespace MathieuCode.M22Quintet

private theorem dot_pair (w : Full) (x y : Fin 24) (hxy : x ≠ y) :
    dotForm w (wordOfSet {x,y}) = w x + w y := by
  change (∑ z, w z * (if z ∈ ({x,y} : Finset (Fin 24)) then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hxy]

private theorem pairing_pair (w : golay) (hw : w.val 0 + w.val 9 = 0)
    (P : PointPair) :
    m22CodeCocodeDuality ⟨codeLine.mkQ w, hw⟩ (m22PairLine.mkQ (pairVector P)) =
      dotForm w.val (wordOfSet P.val) :=
  m22CodeCocodeDuality_apply_mk w hw ⟨wordOfSet P.val, wordOfSet_mem_core P⟩

/-- A code class belongs to the geometric annihilator precisely when its
Golay representative is constant on each compatible tetrad. -/
theorem V4_mk_iff_constant (w : golay) (hw : w.val 0 + w.val 9 = 0) :
    (⟨codeLine.mkQ w, hw⟩ : M22Code) ∈ V4 ↔
      ∀ B ∈ m22SourceSextet.parts, ∀ x ∈ B, ∀ y ∈ B, w.val x = w.val y := by
  change (⟨codeLine.mkQ w, hw⟩ : M22Code) ∈ annihilator V6 ↔ _
  rw [mem_annihilator]
  constructor
  · intro hv B hB x hx y hy
    by_cases hxy : x = y
    · exact congrArg w.val hxy
    have hp : pairVector ⟨{x,y}, by simp [hxy]⟩ ∈ U7 := by
      apply (le_iSup_of_le B (le_iSup_of_le hB le_rfl) : supportedPairSpace B ≤ U7)
      apply pairVector_mem_supportedPairSpace
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact Finset.mem_singleton.mp hz ▸ hy
    have h := hv _ (Submodule.mem_map_of_mem hp)
    rw [pairing_pair] at h
    simpa only [dot_pair _ _ _ hxy, CharTwo.add_eq_zero] using h
  · intro hc u hu
    obtain ⟨v, hv, rfl⟩ := hu
    let f : Cocode →ₗ[ZMod 2] ZMod 2 :=
      (m22CodeCocodeDuality ⟨codeLine.mkQ w, hw⟩).comp m22PairLine.mkQ
    have hle : U7 ≤ f.ker := by
      refine iSup_le fun B => iSup_le fun hB => ?_
      apply Submodule.span_le.mpr
      rintro v ⟨P, hP, rfl⟩
      change m22CodeCocodeDuality ⟨codeLine.mkQ w, hw⟩
        (m22PairLine.mkQ (pairVector P)) = 0
      rw [pairing_pair]
      obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp P.property
      rw [he, dot_pair _ _ _ hxy]
      rw [hc B hB x (hP (by simp [he])) y (hP (by simp [he]))]
      exact CharTwo.add_self_eq_zero _
    exact hle hv

private def separatingWord (j : Fin 5) : golay :=
  ⟨wordOfSet (m22SourceTetrad 0 ∪ m22SourceTetrad j.succ), by
    rw [golay_eq_span_octads]
    exact Submodule.subset_span ⟨_,
      m22SourceTetrad_union_octad 0 j.succ (Fin.succ_ne_zero j).symm, rfl⟩⟩

private theorem separatingWord_pair (j : Fin 5) :
    (separatingWord j).val 0 + (separatingWord j).val 9 = 0 := by
  revert j
  decide +kernel

private def separatingVector (j : Fin 5) : M22Code :=
  ⟨codeLine.mkQ (separatingWord j), separatingWord_pair j⟩

private theorem separatingVector_mem (j : Fin 5) : separatingVector j ∈ V4 := by
  apply (V4_mk_iff_constant _ _).mpr
  intro B hB
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hB
  revert j i
  decide +kernel

private theorem separatingWord_separates (x y : Fin 24)
    (h : ∀ j : Fin 5, (separatingWord j).val x = (separatingWord j).val y) :
    ∀ i : Fin 6, x ∈ m22SourceTetrad i ↔ y ∈ m22SourceTetrad i := by
  revert x y
  decide +kernel

private theorem image_same_tetrad (g : m22PairStabilizer)
    (hg : g ∈ subspaceStabilizer m22OuterCodeRepresentation V4)
    (B : Finset (Fin 24)) (hB : B ∈ m22SourceSextet.parts)
    (x y : Fin 24) (hx : x ∈ B) (hy : y ∈ B) :
    ∀ i : Fin 6, g.val.val x ∈ m22SourceTetrad i ↔
      g.val.val y ∈ m22SourceTetrad i := by
  apply separatingWord_separates
  intro j
  have hmem := ((subspaceStabilizer m22OuterCodeRepresentation V4).inv_mem hg
    (separatingVector j)).mpr (separatingVector_mem j)
  let w := golayRepresentation g.val⁻¹ (separatingWord j)
  have hw : w.val 0 + w.val 9 = 0 :=
    (m22OuterCodeRepresentation g⁻¹ (separatingVector j)).property
  have hc := (V4_mk_iff_constant w hw).mp hmem B hB x hx y hy
  exact hc

/-- The geometric annihilator recovers the actual compatible sextet stabilizer,
unconditionally, in the native setwise pair group. -/
theorem V4_stabilizer_eq_native :
    subspaceStabilizer m22OuterCodeRepresentation V4 = Q := by
  apply le_antisymm
  · intro g hg
    change g.val ∈ MulAction.stabilizer M24 m22SourceSextet.parts
    apply MulAction.mem_stabilizer_finset'.mpr
    intro B hB
    have hn : B.Nonempty := Finset.card_pos.mp (by
      rw [m22SourceSextet.tetrad B hB]
      decide)
    obtain ⟨x, hx⟩ := hn
    have hc : g.val.val x ∈ m22SourceSextet.parts.biUnion id := by
      rw [m22SourceSextet.cover]
      exact Finset.mem_univ _
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hc
    have hsub : g.val • B ⊆ C := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact (image_same_tetrad g hg B hB x y hx hy i).mp hxC
    have he : g.val • B = C := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_smul_finset, m22SourceSextet.tetrad B hB,
        m22SourceSextet.tetrad C hC])
    rwa [he]
  · exact le_subspaceStabilizer _ _ (fun g hg v hv => V4_invariant ⟨g, hg⟩ v hv)

end MathieuCode.M22Quintet
