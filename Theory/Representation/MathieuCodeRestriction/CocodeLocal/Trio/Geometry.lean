module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Representation.MathieuCodeRestriction.Orthogonality
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Trio

/-!
# The pair space of a native Golay trio

Pairs in a common octad span a 21-dimensional subspace of the even core.
Its orthogonal complement consists of the functions constant on each of the
three octads. Those three independent octad words lie in the self-dual Golay
code. Consequently the pair space contains Golay, and its image in the actual
cocode has dimension nine. Equivalently, its preimage consists of the words
whose coordinate sum on each octad is zero. The native trio stabilizer preserves
this geometric space.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.6(1),
printed p.401. This establishes the geometric middle term and its dimension;
its identification with the two commutator spaces is a separate calculation.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped BigOperators Pointwise
namespace MathieuCode.TrioCalculation
noncomputable section

variable (T : Trio)

/-- The pair-generated subspace before taking the Golay quotient. -/
def pairCore : Submodule (ZMod 2) Core :=
  Submodule.span (ZMod 2) {v | ∃ B ∈ T.parts, ∃ P : PointPair,
    P.val ⊆ B ∧ (⟨wordOfSet P.val, wordOfSet_mem_core P⟩ : Core) = v}

def pairFull : Submodule (ZMod 2) Full := (pairCore T).map Core.subtype

def constantMap : (T.parts → ZMod 2) →ₗ[ZMod 2] Full :=
  Fintype.linearCombination (ZMod 2) (fun B : T.parts => wordOfSet B.val)

private lemma part_nonempty (B : T.parts) : B.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [T.part_card B.property]
  decide

private lemma part_point (x : Fin 24) : ∃ B : T.parts, x ∈ B.val := by
  have hx : x ∈ T.parts.biUnion id := by rw [T.cover]; exact Finset.mem_univ _
  obtain ⟨B, hB, hx⟩ := Finset.mem_biUnion.mp hx
  exact ⟨⟨B, hB⟩, hx⟩

lemma constantMap_apply (c : T.parts → ZMod 2) (B : T.parts)
    {x : Fin 24} (hx : x ∈ B.val) : constantMap T c x = c B := by
  classical
  change (∑ A : T.parts, c A • wordOfSet A.val) x = c B
  rw [Finset.sum_apply, Finset.sum_eq_single B]
  · simp [wordOfSet, hx]
  · intro A _ hAB
    have hn : x ∉ A.val := by
      intro ha
      exact Finset.disjoint_left.mp
        (T.disjoint A.val A.property B.val B.property (fun h => hAB (Subtype.ext h))) ha hx
    simp [wordOfSet, hn]
  · simp

lemma constantMap_injective : Function.Injective (constantMap T) := by
  intro c d h
  funext B
  obtain ⟨x, hx⟩ := part_nonempty T B
  simpa only [constantMap_apply T _ B hx] using congrFun h x

lemma finrank_constantMap_range :
    Module.finrank (ZMod 2) (constantMap T).range = 3 := by
  rw [LinearMap.finrank_range_of_inj (constantMap_injective T)]
  simp [T.card]

lemma constantMap_range_le_golay : (constantMap T).range ≤ golay := by
  rintro _ ⟨c, rfl⟩
  apply golay.sum_mem
  intro B _
  apply golay.smul_mem
  rw [golay_eq_span_octads]
  exact Submodule.subset_span ⟨B.val, T.octad B.val B.property, rfl⟩

private lemma dot_word (B : Finset (Fin 24)) (v : Full) :
    dotForm (wordOfSet B) v = ∑ x ∈ B, v x := by
  simp [dotForm, dotProductBilin, dotProduct, wordOfSet]

private lemma pair_word_mem {B : Finset (Fin 24)} (hB : B ∈ T.parts)
    (P : PointPair) (hP : P.val ⊆ B) : wordOfSet P.val ∈ pairFull T :=
  ⟨⟨wordOfSet P.val, wordOfSet_mem_core P⟩,
    Submodule.subset_span ⟨B, hB, P, hP, rfl⟩, rfl⟩

lemma pairFull_orthogonal : dotForm.orthogonal (pairFull T) = (constantMap T).range := by
  classical
  apply le_antisymm
  · intro v hv
    have hc (B : T.parts) {x y : Fin 24} (hx : x ∈ B.val) (hy : y ∈ B.val) :
        v x = v y := by
      by_cases hxy : x = y
      · rw [hxy]
      · have hz := hv (wordOfSet {x,y})
          (pair_word_mem T B.property ⟨{x,y}, by simp [hxy]⟩
            (by
              intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact hx
              · simpa using (Finset.mem_singleton.mp hz ▸ hy)))
        rw [dot_word] at hz
        simpa [hxy, CharTwo.add_eq_zero] using hz
    let c : T.parts → ZMod 2 := fun B => v (part_nonempty T B).choose
    refine ⟨c, ?_⟩
    funext x
    obtain ⟨B, hx⟩ := part_point T x
    rw [constantMap_apply T c B hx]
    exact hc B (part_nonempty T B).choose_spec hx
  · rintro _ ⟨c, rfl⟩ u ⟨v, hv, rfl⟩
    change dotForm v.val (constantMap T c) = 0
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨B, hB, P, hP, rfl⟩ := hv
      obtain ⟨x, y, hxy, hPxy⟩ := Finset.card_eq_two.mp P.property
      have hx : x ∈ B := hP (by simp [hPxy])
      have hy : y ∈ B := hP (by simp [hPxy])
      rw [dot_word, hPxy]
      simp only [Finset.sum_pair hxy, constantMap_apply T c ⟨B,hB⟩ hx,
        constantMap_apply T c ⟨B,hB⟩ hy, CharTwo.add_self_eq_zero]
    | zero => simp
    | add v w _ _ hv hw => simpa using congrArg₂ (· + ·) hv hw
    | smul a v _ hv => simpa using congrArg (a • ·) hv

lemma pairFull_eq_orthogonal : pairFull T = dotForm.orthogonal (constantMap T).range := by
  rw [← pairFull_orthogonal, LinearMap.BilinForm.orthogonal_orthogonal
    dotForm_nondegenerate dotForm_symmetric.isRefl]

lemma golay_le_pairFull : golay ≤ pairFull T := by
  rw [pairFull_eq_orthogonal, ← golay_orthogonal_eq]
  exact LinearMap.BilinForm.orthogonal_le (constantMap_range_le_golay T)

lemma finrank_pairFull : Module.finrank (ZMod 2) (pairFull T) = 21 := by
  rw [pairFull_eq_orthogonal,
    LinearMap.BilinForm.finrank_orthogonal dotForm_nondegenerate,
    finrank_constantMap_range, BinaryPermutation.finrank_full]
  rfl

lemma finrank_pairCore : Module.finrank (ZMod 2) (pairCore T) = 21 := by
  exact (Submodule.equivMapOfInjective Core.subtype Core.injective_subtype
    (pairCore T)).finrank_eq.trans (finrank_pairFull T)

lemma codeInCore_le_pairCore : codeInCore ≤ pairCore T := by
  intro v hv
  obtain ⟨w, hw, he⟩ := golay_le_pairFull T hv
  have he' : w = v := Subtype.ext he
  rwa [← he']

lemma pairCore_quotient_image :
    (pairCore T).map codeInCore.mkQ = ⨆ B ∈ T.parts, supportedPairSpace B := by
  apply le_antisymm
  · rw [pairCore, Submodule.map_span_le]
    rintro _ ⟨B,hB,P,hP,rfl⟩
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB
      (pairVector_mem_supportedPairSpace P hP))
  · refine iSup_le fun B => iSup_le fun hB => Submodule.span_le.mpr ?_
    rintro _ ⟨P,hP,rfl⟩
    exact ⟨⟨wordOfSet P.val, wordOfSet_mem_core P⟩,
      Submodule.subset_span ⟨B,hB,P,hP,rfl⟩, rfl⟩

lemma finrank_pairCore_quotient_image :
    Module.finrank (ZMod 2) ((pairCore T).map codeInCore.mkQ) = 9 := by
  let f := codeInCore.mkQ.comp (pairCore T).subtype
  have hr : f.range = (pairCore T).map codeInCore.mkQ := by
    simp [f, LinearMap.range_comp]
  have hk : f.ker = codeInCore.comap (pairCore T).subtype := by
    simp [f, LinearMap.ker_comp]
  have hkd : Module.finrank (ZMod 2) f.ker = 12 := by
    rw [hk]
    exact (Submodule.comapSubtypeEquivOfLe (codeInCore_le_pairCore T)).finrank_eq.trans
      finrank_codeInCore
  have h := f.finrank_range_add_finrank_ker
  rw [hr, hkd, finrank_pairCore] at h
  omega

/-- The prequotient space consists exactly of words even on each octad. -/
lemma mem_pairCore_iff (v : Core) :
    v ∈ pairCore T ↔ ∀ B ∈ T.parts, ∑ x ∈ B, v.val x = 0 := by
  have hm : v ∈ pairCore T ↔ v.val ∈ pairFull T := by
    constructor
    · intro hv; exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, he⟩
      have he' : w = v := Subtype.ext he
      rwa [← he']
  rw [hm, pairFull_eq_orthogonal]
  constructor
  · intro hv B hB
    have hb : wordOfSet B ∈ (constantMap T).range := by
      refine ⟨Pi.single ⟨B,hB⟩ 1, ?_⟩
      simp [constantMap, Fintype.linearCombination_apply, Pi.single_apply]
    exact (dot_word B v.val) ▸ hv _ hb
  · intro hv u hu
    obtain ⟨c,rfl⟩ := hu
    change dotForm (∑ B : T.parts, c B • wordOfSet B.val) v.val = 0
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      dot_word]
    apply Finset.sum_eq_zero
    intro B _
    rw [hv B.val B.property, smul_zero]

/-- The image in the actual even-core/Golay quotient is nine-dimensional. -/
lemma finrank_pairSpace :
    Module.finrank (ZMod 2)
      (⨆ B ∈ T.parts, supportedPairSpace B : Submodule (ZMod 2) Cocode) = 9 := by
  rw [← pairCore_quotient_image]
  exact finrank_pairCore_quotient_image T

/-- Every native trio stabilizer element preserves the geometric pair space. -/
lemma pairSpace_invariant (g : M24) (hg : g ∈ trioStabilizer T)
    {v : Cocode} (hv : v ∈ ⨆ B ∈ T.parts, supportedPairSpace B) :
    cocodeRepresentation g v ∈ ⨆ B ∈ T.parts, supportedPairSpace B := by
  have hle : (⨆ B ∈ T.parts, supportedPairSpace B) ≤
      (⨆ B ∈ T.parts, supportedPairSpace B).comap (cocodeRepresentation g) := by
    refine iSup_le fun B => iSup_le fun hB => Submodule.span_le.mpr ?_
    rintro _ ⟨P,hP,rfl⟩
    change cocodeRepresentation g (pairVector P) ∈
      (⨆ B ∈ T.parts, supportedPairSpace B : Submodule (ZMod 2) Cocode)
    rw [pairVector_equivariant]
    exact Submodule.mem_iSup_of_mem (g • B) (Submodule.mem_iSup_of_mem
      ((mem_trioStabilizer_iff T g).mp hg B hB)
      (pairVector_mem_supportedPairSpace (mapPair g P) (Finset.smul_finset_subset_smul_finset hP)))
  exact hle hv

end
end MathieuCode.TrioCalculation
