module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules
public import Theory.Representation.MathieuCodeRestriction.M22.HexadGeometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Kernel

/-!
# Pair classes detect the genuine hexad kernel

Golay minimum distance separates pairs disjoint from the removed pair even in
its cocode quotient. Fixing all such pair classes on a hexad fixes its six
points. The native alternating octad action then excludes a permutation
exchanging just the distinguished two points. Thus the quotient pair classes
detect the actual pointwise octad kernel, also in the setwise pair stabilizer.

This supplies the geometric rigidity needed to exclude shears in the M22
centralizer transfer. It uses the literal coordinate pair {0,9} and the two
actual cocode quotient maps.

Source: Aschbacher--Smith, H.15.2(5) and its proof, printed pp.398--399,
combined manuscript of 1 March 2004.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
namespace MathieuCode.Hexad.CocodeAction
noncomputable section

/-- Minimum distance separates pairs away from the removed pair, even after
passing to the ten-dimensional quotient. -/
theorem quotient_pair_injective (B C : PointPair)
    (hB : Disjoint B.val m22Pair) (hC : Disjoint C.val m22Pair)
    (he : m22PairLine.mkQ (pairVector B) = m22PairLine.mkQ (pairVector C)) : B = C := by
  have hm : pairVector B - pairVector C ∈ m22PairLine :=
    (Submodule.Quotient.mk_eq_zero m22PairLine).mp (by
      change m22PairLine.mkQ (pairVector B - pairVector C) = 0
      rw [map_sub, he, sub_self])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  let w : Full := wordOfSet B.val - wordOfSet C.val - c • m22PairWord
  have hw : w ∈ golay := by
    change (⟨wordOfSet B.val, wordOfSet_mem_core B⟩ -
      ⟨wordOfSet C.val, wordOfSet_mem_core C⟩ - c •
      ⟨m22PairWord, m22PairWord_mem_core⟩ : Core) ∈ codeInCore
    apply (Submodule.Quotient.mk_eq_zero codeInCore).mp
    change codeInCore.mkQ (⟨wordOfSet B.val, wordOfSet_mem_core B⟩ -
      ⟨wordOfSet C.val, wordOfSet_mem_core C⟩ - c •
      ⟨m22PairWord, m22PairWord_mem_core⟩) = 0
    simp only [map_sub, map_smul]
    exact sub_eq_zero.mpr hc.symm
  have hwc : hammingNorm w ≤ 6 := by
    have hs : (Finset.univ.filter (fun i => w i ≠ 0)) ⊆ B.val ∪ C.val ∪ m22Pair := by
      intro i hi
      by_contra hn
      have hh : i ∉ B.val ∧ i ∉ C.val ∧ i ∉ m22Pair := by simpa using hn
      have hz : w i = 0 := by
        simp [w, wordOfSet, m22PairWord_eq_wordOfSet, hh]
      exact (Finset.mem_filter.mp hi).2 hz
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le (B.val ∪ C.val) m22Pair
    have h3 := Finset.card_union_le B.val C.val
    have hp : m22Pair.card = 2 := by decide
    change (Finset.univ.filter (fun i => w i ≠ 0)).card ≤ 6
    rw [B.property, C.property] at h3
    omega
  have hw0 : w = 0 := by
    by_contra hn
    have := native_golay_minimum hw hn
    omega
  apply Subtype.ext
  apply wordOfSet_injective
  ext i
  by_cases hi : i ∈ m22Pair
  · have hb : i ∉ B.val := fun hb => Finset.disjoint_left.mp hB hb hi
    have hc : i ∉ C.val := fun hc => Finset.disjoint_left.mp hC hc hi
    simp [wordOfSet, hb, hc]
  · have h := congrFun hw0 i
    simpa [w, m22PairWord_eq_wordOfSet, wordOfSet, hi, sub_eq_zero] using h

/-- Fixing every unordered pair in a set of at least three points fixes that set
pointwise; no setwise stabilizer hypothesis is needed. -/
private theorem fixes_points_of_fixes_pairs (B : Finset (Fin 24)) (hB : 3 ≤ B.card)
    (g : M24) (hg : ∀ P : PointPair, P.val ⊆ B → g • P.val = P.val) :
    ∀ i ∈ B, g • i = i := by
  intro i hi
  have hiB : 2 ≤ (B.erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by omega : 1 < (B.erase i).card)
  have hji := (Finset.mem_erase.mp hj).1
  have hki := (Finset.mem_erase.mp hk).1
  have hjB := (Finset.mem_erase.mp hj).2
  have hkB := (Finset.mem_erase.mp hk).2
  have h1 : g • ({i, j} : Finset (Fin 24)) = {i, j} :=
    hg ⟨{i, j}, by simp [hji.symm]⟩ (Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hjB⟩)
  have h2 : g • ({i, k} : Finset (Fin 24)) = {i, k} :=
    hg ⟨{i, k}, by simp [hki.symm]⟩ (Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hkB⟩)
  have hgi1 : g • i ∈ ({i, j} : Finset (Fin 24)) := by
    rw [← h1]
    exact Finset.smul_mem_smul_finset (by simp)
  have hgi2 : g • i ∈ ({i, k} : Finset (Fin 24)) := by
    rw [← h2]
    exact Finset.smul_mem_smul_finset (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hgi1 hgi2
  rcases hgi1 with h | h
  · exact h
  · exact hgi2.resolve_right (fun hk => hjk (h.symm.trans hk))

/-- An even octad permutation cannot move only the distinguished two points. -/
private theorem octad_fixer_of_hexad_fixer (O : Octad) (hO : m22Pair ⊆ O.val)
    (g : m22PairStabilizer) (hg : ∀ i ∈ O.val \ m22Pair, g.val • i = i) :
    g.val ∈ octadPointwiseKernel O := by
  have hgO : g.val ∈ octadStabilizer O := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    by_cases hip : i ∈ m22Pair
    · apply hO
      exact (MulAction.mem_stabilizer_finset.mp g.property i).mpr hip
    · rw [hg i (Finset.mem_sdiff.mpr ⟨hi, hip⟩)]
      exact hi
  let p := CocodeOctad.coordinateAction O ⟨g.val, hgO⟩
  have hp : p ∈ alternatingGroup O.val := by
    rw [← CocodeOctad.coordinateAction_range]
    exact MonoidHom.mem_range.mpr ⟨⟨g.val, hgO⟩, rfl⟩
  have hzero : (0 : Fin 24) ∈ O.val := hO (by decide)
  have hnine : (9 : Fin 24) ∈ O.val := hO (by decide)
  have hs : p.support ⊆ {⟨0, hzero⟩, ⟨9, hnine⟩} := by
    intro i hi
    by_contra hn
    have hiP : i.val ∉ m22Pair := by
      simpa [m22Pair, Subtype.ext_iff] using hn
    exact (Equiv.Perm.mem_support.mp hi) (Subtype.ext (hg i.val
      (Finset.mem_sdiff.mpr ⟨i.property, hiP⟩)))
  have hc : p.support.card ≤ 2 := (Finset.card_le_card hs).trans Finset.card_le_two
  have hp1 : p = 1 := by
    by_contra hn
    have h2 := Equiv.Perm.two_le_card_support_of_ne_one hn
    have ht := Equiv.Perm.card_support_eq_two.mp (show p.support.card = 2 by omega)
    have hh := ht.sign_eq
    rw [Equiv.Perm.mem_alternatingGroup.mp hp] at hh
    exact (by decide : (1 : ℤˣ) ≠ -1) hh
  rw [mem_octadPointwiseKernel]
  intro i hi
  exact congrArg Subtype.val (Equiv.congr_fun hp1 ⟨i, hi⟩)

/-- The quotient classes of pairs on the hexad detect its full pointwise
kernel, including in the literal setwise pair group. -/
theorem octad_kernel_of_quotient_pairs_fixed (O : Octad) (hO : m22Pair ⊆ O.val)
    (g : m22PairStabilizer)
    (hg : ∀ P : PointPair, P.val ⊆ O.val \ m22Pair →
      m22OuterCocodeRepresentation g (m22PairLine.mkQ (pairVector P)) =
        m22PairLine.mkQ (pairVector P)) :
    g.val ∈ octadPointwiseKernel O := by
  apply octad_fixer_of_hexad_fixer O hO g
  apply fixes_points_of_fixes_pairs (O.val \ m22Pair)
  · rw [Finset.card_sdiff_of_subset hO, m24Blocks_card _ O.property]
    decide
  intro P hP
  have hp : Disjoint P.val m22Pair := Finset.disjoint_left.mpr
    (fun i hi => (Finset.mem_sdiff.mp (hP hi)).2)
  have hgp : Disjoint (mapPair g.val P).val m22Pair := by
    apply Finset.disjoint_left.mpr
    intro i hi hip
    obtain ⟨j, hj, rfl⟩ := Finset.mem_smul_finset.mp hi
    exact Finset.disjoint_left.mp hp hj
      ((MulAction.mem_stabilizer_finset.mp g.property j).mp hip)
  change (mapPair g.val P).val = P.val
  apply congrArg Subtype.val
  apply quotient_pair_injective (mapPair g.val P) P hgp hp
  simpa only [m22OuterCocodeRepresentation_mk, pairVector_equivariant] using hg P hP


end
end MathieuCode.Hexad.CocodeAction
