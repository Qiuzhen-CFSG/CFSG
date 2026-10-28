module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.WordTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.BridgeCertificates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NativeFBranch

/-!
# Whole-subgroup F placement of the twenty-five nonline rows

Seven checked native words generate an elementary subgroup of a fixed
conjugate of F. Actual max2 words move this subgroup to containers of each
of the ten literal sixteen rows. Each nonline eight is contained in one
of those sixteen rows, so the same conjugator places that whole eight.
All point coordinates are the shared `FiniteConfigurations.Data` ones.

This establishes subgroup placement and a native F subgroup in the full
centralizer of every nonline row. It does not assert whole-normalizer
containment: F is not yet shown canonical under these pure normalizers.
In particular the two sixteen containers of an eight must not be confused
with a single F container of their canonical hull.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open FiniteConfigurations
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
attribute [local irreducible] modelGroup matrixA matrixB
set_option Elab.async false
private def seedMask : Fin 7 → Fin 8192 := ![1,68,270,532,1048,2208,4100]
/-- The 128 literal kernel words in the seed F occurrence. -/
@[expose] def seedCoordinate : Fin 128 → Fin 8192 := ![0,1,68,69,270,271,331,330,532,533,593,592,794,795,862,863,1048,1049,1117,1116,1303,1302,1363,1362,1549,1548,1609,1608,1794,1795,1863,1862,2208,2209,2277,2276,2479,2478,2539,2538,2741,2740,2801,2800,3002,3003,3071,3070,3257,3256,3325,3324,3511,3510,3570,3571,3757,3756,3816,3817,4003,4002,4071,4070,4100,4101,4161,4160,4362,4363,4430,4431,4624,4625,4692,4693,4894,4895,4955,4954,5149,5148,5209,5208,5394,5395,5463,5462,5640,5641,5709,5708,5895,5894,5955,5954,6308,6309,6368,6369,6571,6570,6638,6639,6833,6832,6900,6901,7102,7103,7162,7163,7356,7357,7417,7416,7602,7603,7670,7671,7848,7849,7916,7917,8102,8103,8163,8162]
private def parent : Fin 128 → Fin 128 := ![0,0,0,1,0,1,2,3,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
private def last : Fin 128 → Fin 7 := ![0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]
private theorem seed_mem (i : Fin 7) :
    nativeWord (seedMask i) ∈ LinearFive.F.map (MulAut.conj BridgeCertificates.bridge⁻¹).toMonoidHom := by
  fin_cases i
  · refine ⟨LinearFive.fValue 6,LinearFive.fValue_mem 6,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_0]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
  · refine ⟨LinearFive.fValue 590,LinearFive.fValue_mem 590,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_1]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
  · refine ⟨LinearFive.fValue 54,LinearFive.fValue_mem 54,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_2]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
  · refine ⟨LinearFive.fValue 47,LinearFive.fValue_mem 47,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_3]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
  · refine ⟨LinearFive.fValue 121,LinearFive.fValue_mem 121,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_4]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
  · refine ⟨LinearFive.fValue 109,LinearFive.fValue_mem 109,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_5]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
  · refine ⟨LinearFive.fValue 52,LinearFive.fValue_mem 52,?_⟩
    rw [← BridgeCertificates.bridge_conjugates_6]
    change (MulAut.conj BridgeCertificates.bridge⁻¹) ((MulAut.conj BridgeCertificates.bridge) _) = _
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    rfl
private theorem seedCoordinate_step (i : Fin 128) (hi : i ≠ 0) :
    parent i < i ∧ maskMultiply (seedCoordinate (parent i)).val (seedMask (last i)).val =
      (seedCoordinate i).val := by
  have h : ∀ i : Fin 128, i ≠ 0 →
      parent i < i ∧ maskMultiply (seedCoordinate (parent i)).val (seedMask (last i)).val =
        (seedCoordinate i).val := by decide +kernel
  exact h i hi

/-- All seed coordinates lie in the same actual F conjugate. -/
theorem seedCoordinate_mem (i : Fin 128) :
    nativeWord (seedCoordinate i) ∈
      LinearFive.F.map (MulAut.conj BridgeCertificates.bridge⁻¹).toMonoidHom := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases hi : i = 0
    · subst i
      change ((kernelProduct 0 : sourceSubgroup) : Model) ∈ _
      have hz : kernelProduct 0 = 1 := by simp [kernelProduct]
      rw [hz,Subgroup.coe_one]
      exact one_mem _
    · have hs := seedCoordinate_step i hi
      have he : nativeWord (seedCoordinate i) =
          nativeWord (seedCoordinate (parent i)) * nativeWord (seedMask (last i)) := by
        have h := source_mask_multiply (seedCoordinate (parent i)).val (seedMask (last i)).val
        rw [hs.2] at h
        exact congrArg (fun x : sourceSubgroup => (x : Model)) h
      rw [he]
      exact mul_mem (ih _ hs.1) (seed_mem _)

/-- Explicit source words moving the ten whole sixteen configurations. -/
@[expose] def placementWord : Fin 10 → List Bool := ![
  [true,false,true,true,false,true,false,true,true],
  [true,false,true,false,true,false,true,true,false,true,false],
  [false,true,true,false,true,false,true,true,false,true,false,true,false,true,true],
  [true,false,true,true,false,true,false,true,true,false,true,false,true,false],
  [true,false,true,false,true,true,false,true,true,false,true],
  [true,true,false,true,false,true,true,false],
  [true,true,false,true,false,true,false,true,false,true,true,false,true,false,true,true,false,true,false],
  [true,false,true,false,true,false,true,true,false,true,true,false,true,false],
  [false,true,true,false,true],
  [true,true,false,true,true,false,true,false,true,false,true,true,false]]

/-- The literal ambient conjugator, with the right-action convention retained. -/
@[expose] def sixteenConjugator (i : Fin 10) : Model :=
  (actorWord (placementWord i) : Model)⁻¹ * BridgeCertificates.bridge⁻¹

private theorem transported_seed_mem (i : Fin 10) (j : Fin 128) (m : Fin 8192)
    (hm : actMask (placementWord i) (seedCoordinate j).val = m.val) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator i)).toMonoidHom := by
  obtain ⟨u,hu,he⟩ := seedCoordinate_mem j
  refine ⟨u,hu,?_⟩
  have hc := nativeWord_conjugates (placementWord i) (seedCoordinate j) m hm
  rw [← he] at hc
  change (MulAut.conj (sixteenConjugator i)) u = nativeWord m
  change (MulAut.conj ((actorWord (placementWord i) : Model)⁻¹))
    ((MulAut.conj BridgeCertificates.bridge⁻¹) u) = nativeWord m at hc
  simpa only [sixteenConjugator,MulAut.conj_apply,mul_inv_rev,mul_assoc,inv_inv] using hc

private theorem sixteen_words_mem_0 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 0)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 0)).toMonoidHom := by
  change m ∈ ({0,1,1578,1579,2978,2979,3464,3465,4716,4717,5190,5191,6606,6607,8164,8165} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 0 0 0 (by decide +kernel)
  · exact transported_seed_mem 0 1 1 (by decide +kernel)
  · exact transported_seed_mem 0 97 1578 (by decide +kernel)
  · exact transported_seed_mem 0 96 1579 (by decide +kernel)
  · exact transported_seed_mem 0 69 2978 (by decide +kernel)
  · exact transported_seed_mem 0 68 2979 (by decide +kernel)
  · exact transported_seed_mem 0 37 3464 (by decide +kernel)
  · exact transported_seed_mem 0 36 3465 (by decide +kernel)
  · exact transported_seed_mem 0 65 4716 (by decide +kernel)
  · exact transported_seed_mem 0 64 4717 (by decide +kernel)
  · exact transported_seed_mem 0 33 5190 (by decide +kernel)
  · exact transported_seed_mem 0 32 5191 (by decide +kernel)
  · exact transported_seed_mem 0 4 6606 (by decide +kernel)
  · exact transported_seed_mem 0 5 6607 (by decide +kernel)
  · exact transported_seed_mem 0 101 8164 (by decide +kernel)
  · exact transported_seed_mem 0 100 8165 (by decide +kernel)

private theorem sixteen_words_mem_1 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 1)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 1)).toMonoidHom := by
  change m ∈ ({0,1,564,565,3464,3465,4028,4029,5190,5191,5746,5747,6606,6607,7162,7163} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 1 0 0 (by decide +kernel)
  · exact transported_seed_mem 1 1 1 (by decide +kernel)
  · exact transported_seed_mem 1 32 564 (by decide +kernel)
  · exact transported_seed_mem 1 33 565 (by decide +kernel)
  · exact transported_seed_mem 1 96 3464 (by decide +kernel)
  · exact transported_seed_mem 1 97 3465 (by decide +kernel)
  · exact transported_seed_mem 1 65 4028 (by decide +kernel)
  · exact transported_seed_mem 1 64 4029 (by decide +kernel)
  · exact transported_seed_mem 1 68 5190 (by decide +kernel)
  · exact transported_seed_mem 1 69 5191 (by decide +kernel)
  · exact transported_seed_mem 1 100 5746 (by decide +kernel)
  · exact transported_seed_mem 1 101 5747 (by decide +kernel)
  · exact transported_seed_mem 1 36 6606 (by decide +kernel)
  · exact transported_seed_mem 1 37 6607 (by decide +kernel)
  · exact transported_seed_mem 1 5 7162 (by decide +kernel)
  · exact transported_seed_mem 1 4 7163 (by decide +kernel)

private theorem sixteen_words_mem_2 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 2)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 2)).toMonoidHom := by
  change m ∈ ({0,1,1246,1247,2980,2981,3962,3963,4714,4715,5812,5813,6606,6607,7440,7441} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 2 0 0 (by decide +kernel)
  · exact transported_seed_mem 2 1 1 (by decide +kernel)
  · exact transported_seed_mem 2 91 1246 (by decide +kernel)
  · exact transported_seed_mem 2 90 1247 (by decide +kernel)
  · exact transported_seed_mem 2 98 2980 (by decide +kernel)
  · exact transported_seed_mem 2 99 2981 (by decide +kernel)
  · exact transported_seed_mem 2 56 3962 (by decide +kernel)
  · exact transported_seed_mem 2 57 3963 (by decide +kernel)
  · exact transported_seed_mem 2 13 4714 (by decide +kernel)
  · exact transported_seed_mem 2 12 4715 (by decide +kernel)
  · exact transported_seed_mem 2 87 5812 (by decide +kernel)
  · exact transported_seed_mem 2 86 5813 (by decide +kernel)
  · exact transported_seed_mem 2 111 6606 (by decide +kernel)
  · exact transported_seed_mem 2 110 6607 (by decide +kernel)
  · exact transported_seed_mem 2 52 7440 (by decide +kernel)
  · exact transported_seed_mem 2 53 7441 (by decide +kernel)

private theorem sixteen_words_mem_3 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 3)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 3)).toMonoidHom := by
  change m ∈ ({0,1,198,199,2390,2391,2448,2449,4190,4191,4248,4249,6408,6409,6606,6607} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 3 0 0 (by decide +kernel)
  · exact transported_seed_mem 3 1 1 (by decide +kernel)
  · exact transported_seed_mem 3 33 198 (by decide +kernel)
  · exact transported_seed_mem 3 32 199 (by decide +kernel)
  · exact transported_seed_mem 3 100 2390 (by decide +kernel)
  · exact transported_seed_mem 3 101 2391 (by decide +kernel)
  · exact transported_seed_mem 3 69 2448 (by decide +kernel)
  · exact transported_seed_mem 3 68 2449 (by decide +kernel)
  · exact transported_seed_mem 3 96 4190 (by decide +kernel)
  · exact transported_seed_mem 3 97 4191 (by decide +kernel)
  · exact transported_seed_mem 3 64 4248 (by decide +kernel)
  · exact transported_seed_mem 3 65 4249 (by decide +kernel)
  · exact transported_seed_mem 3 4 6408 (by decide +kernel)
  · exact transported_seed_mem 3 5 6409 (by decide +kernel)
  · exact transported_seed_mem 3 36 6606 (by decide +kernel)
  · exact transported_seed_mem 3 37 6607 (by decide +kernel)

private theorem sixteen_words_mem_4 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 4)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 4)).toMonoidHom := by
  change m ∈ ({0,1,564,565,2448,2449,2980,2981,4190,4191,4714,4715,6606,6607,7162,7163} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 4 0 0 (by decide +kernel)
  · exact transported_seed_mem 4 1 1 (by decide +kernel)
  · exact transported_seed_mem 4 64 564 (by decide +kernel)
  · exact transported_seed_mem 4 65 565 (by decide +kernel)
  · exact transported_seed_mem 4 100 2448 (by decide +kernel)
  · exact transported_seed_mem 4 101 2449 (by decide +kernel)
  · exact transported_seed_mem 4 37 2980 (by decide +kernel)
  · exact transported_seed_mem 4 36 2981 (by decide +kernel)
  · exact transported_seed_mem 4 33 4190 (by decide +kernel)
  · exact transported_seed_mem 4 32 4191 (by decide +kernel)
  · exact transported_seed_mem 4 97 4714 (by decide +kernel)
  · exact transported_seed_mem 4 96 4715 (by decide +kernel)
  · exact transported_seed_mem 4 68 6606 (by decide +kernel)
  · exact transported_seed_mem 4 69 6607 (by decide +kernel)
  · exact transported_seed_mem 4 5 7162 (by decide +kernel)
  · exact transported_seed_mem 4 4 7163 (by decide +kernel)

private theorem sixteen_words_mem_5 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 5)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 5)).toMonoidHom := by
  change m ∈ ({0,1,6,7,2384,2385,2390,2391,4248,4249,4254,4255,6600,6601,6606,6607} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 5 0 0 (by decide +kernel)
  · exact transported_seed_mem 5 1 1 (by decide +kernel)
  · exact transported_seed_mem 5 64 6 (by decide +kernel)
  · exact transported_seed_mem 5 65 7 (by decide +kernel)
  · exact transported_seed_mem 5 33 2384 (by decide +kernel)
  · exact transported_seed_mem 5 32 2385 (by decide +kernel)
  · exact transported_seed_mem 5 97 2390 (by decide +kernel)
  · exact transported_seed_mem 5 96 2391 (by decide +kernel)
  · exact transported_seed_mem 5 4 4248 (by decide +kernel)
  · exact transported_seed_mem 5 5 4249 (by decide +kernel)
  · exact transported_seed_mem 5 68 4254 (by decide +kernel)
  · exact transported_seed_mem 5 69 4255 (by decide +kernel)
  · exact transported_seed_mem 5 37 6600 (by decide +kernel)
  · exact transported_seed_mem 5 36 6601 (by decide +kernel)
  · exact transported_seed_mem 5 101 6606 (by decide +kernel)
  · exact transported_seed_mem 5 100 6607 (by decide +kernel)

private theorem sixteen_words_mem_6 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 6)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 6)).toMonoidHom := by
  change m ∈ ({0,1,1578,1579,2384,2385,3962,3963,4254,4255,5812,5813,6606,6607,8164,8165} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 6 0 0 (by decide +kernel)
  · exact transported_seed_mem 6 1 1 (by decide +kernel)
  · exact transported_seed_mem 6 117 1578 (by decide +kernel)
  · exact transported_seed_mem 6 116 1579 (by decide +kernel)
  · exact transported_seed_mem 6 118 2384 (by decide +kernel)
  · exact transported_seed_mem 6 119 2385 (by decide +kernel)
  · exact transported_seed_mem 6 2 3962 (by decide +kernel)
  · exact transported_seed_mem 6 3 3963 (by decide +kernel)
  · exact transported_seed_mem 6 62 4254 (by decide +kernel)
  · exact transported_seed_mem 6 63 4255 (by decide +kernel)
  · exact transported_seed_mem 6 74 5812 (by decide +kernel)
  · exact transported_seed_mem 6 75 5813 (by decide +kernel)
  · exact transported_seed_mem 6 72 6606 (by decide +kernel)
  · exact transported_seed_mem 6 73 6607 (by decide +kernel)
  · exact transported_seed_mem 6 61 8164 (by decide +kernel)
  · exact transported_seed_mem 6 60 8165 (by decide +kernel)

private theorem sixteen_words_mem_7 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 7)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 7)).toMonoidHom := by
  change m ∈ ({0,1,198,199,2916,2917,2978,2979,4716,4717,4778,4779,6408,6409,6606,6607} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 7 0 0 (by decide +kernel)
  · exact transported_seed_mem 7 1 1 (by decide +kernel)
  · exact transported_seed_mem 7 68 198 (by decide +kernel)
  · exact transported_seed_mem 7 69 199 (by decide +kernel)
  · exact transported_seed_mem 7 4 2916 (by decide +kernel)
  · exact transported_seed_mem 7 5 2917 (by decide +kernel)
  · exact transported_seed_mem 7 65 2978 (by decide +kernel)
  · exact transported_seed_mem 7 64 2979 (by decide +kernel)
  · exact transported_seed_mem 7 32 4716 (by decide +kernel)
  · exact transported_seed_mem 7 33 4717 (by decide +kernel)
  · exact transported_seed_mem 7 100 4778 (by decide +kernel)
  · exact transported_seed_mem 7 101 4779 (by decide +kernel)
  · exact transported_seed_mem 7 36 6408 (by decide +kernel)
  · exact transported_seed_mem 7 37 6409 (by decide +kernel)
  · exact transported_seed_mem 7 97 6606 (by decide +kernel)
  · exact transported_seed_mem 7 96 6607 (by decide +kernel)

private theorem sixteen_words_mem_8 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 8)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 8)).toMonoidHom := by
  change m ∈ ({0,1,6,7,4026,4027,4028,4029,5746,5747,5748,5749,6600,6601,6606,6607} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 8 0 0 (by decide +kernel)
  · exact transported_seed_mem 8 1 1 (by decide +kernel)
  · exact transported_seed_mem 8 2 6 (by decide +kernel)
  · exact transported_seed_mem 8 3 7 (by decide +kernel)
  · exact transported_seed_mem 8 62 4026 (by decide +kernel)
  · exact transported_seed_mem 8 63 4027 (by decide +kernel)
  · exact transported_seed_mem 8 61 4028 (by decide +kernel)
  · exact transported_seed_mem 8 60 4029 (by decide +kernel)
  · exact transported_seed_mem 8 117 5746 (by decide +kernel)
  · exact transported_seed_mem 8 116 5747 (by decide +kernel)
  · exact transported_seed_mem 8 118 5748 (by decide +kernel)
  · exact transported_seed_mem 8 119 5749 (by decide +kernel)
  · exact transported_seed_mem 8 75 6600 (by decide +kernel)
  · exact transported_seed_mem 8 74 6601 (by decide +kernel)
  · exact transported_seed_mem 8 73 6606 (by decide +kernel)
  · exact transported_seed_mem 8 72 6607 (by decide +kernel)

private theorem sixteen_words_mem_9 (m : Fin 8192)
    (hm : m ∈ rowMasks (sixteenIndex 9)) :
    nativeWord m ∈ LinearFive.F.map (MulAut.conj (sixteenConjugator 9)).toMonoidHom := by
  change m ∈ ({0,1,1246,1247,2916,2917,4026,4027,4778,4779,5748,5749,6606,6607,7440,7441} : Finset (Fin 8192)) at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transported_seed_mem 9 0 0 (by decide +kernel)
  · exact transported_seed_mem 9 1 1 (by decide +kernel)
  · exact transported_seed_mem 9 62 1246 (by decide +kernel)
  · exact transported_seed_mem 9 63 1247 (by decide +kernel)
  · exact transported_seed_mem 9 75 2916 (by decide +kernel)
  · exact transported_seed_mem 9 74 2917 (by decide +kernel)
  · exact transported_seed_mem 9 116 4026 (by decide +kernel)
  · exact transported_seed_mem 9 117 4027 (by decide +kernel)
  · exact transported_seed_mem 9 60 4778 (by decide +kernel)
  · exact transported_seed_mem 9 61 4779 (by decide +kernel)
  · exact transported_seed_mem 9 3 5748 (by decide +kernel)
  · exact transported_seed_mem 9 2 5749 (by decide +kernel)
  · exact transported_seed_mem 9 118 6606 (by decide +kernel)
  · exact transported_seed_mem 9 119 6607 (by decide +kernel)
  · exact transported_seed_mem 9 72 7440 (by decide +kernel)
  · exact transported_seed_mem 9 73 7441 (by decide +kernel)

/-- Each of the ten shared sixteen rows is contained in an actual F conjugate. -/
theorem sixteen_row_le_F_conjugate (i : Fin 10) :
    row (sixteenIndex i) ≤ LinearFive.F.map (MulAut.conj (sixteenConjugator i)).toMonoidHom := by
  apply (closure_le _).mpr
  rintro _ ⟨m,hm,rfl⟩
  fin_cases i
  · exact sixteen_words_mem_0 m hm
  · exact sixteen_words_mem_1 m hm
  · exact sixteen_words_mem_2 m hm
  · exact sixteen_words_mem_3 m hm
  · exact sixteen_words_mem_4 m hm
  · exact sixteen_words_mem_5 m hm
  · exact sixteen_words_mem_6 m hm
  · exact sixteen_words_mem_7 m hm
  · exact sixteen_words_mem_8 m hm
  · exact sixteen_words_mem_9 m hm

@[expose] def eightContainer : Fin 16 → Fin 10 := ![0,3,2,0,8,0,3,2,5,1,1,3,2,0,5,7]
private theorem eight_masks_le (i : Fin 16) (hi : i ≠ 5) :
    rowMasks (eightIndex i) ⊆ rowMasks (sixteenIndex (eightContainer i)) := by
  have h : ∀ i : Fin 16, i ≠ 5 →
      rowMasks (eightIndex i) ⊆ rowMasks (sixteenIndex (eightContainer i)) := by decide +kernel
  exact h i hi

/-- Every nonline eight uses the same F conjugator as its chosen actual sixteen. -/
theorem nonline_eight_le_F_conjugate (i : Fin 16) (hi : i ≠ 5) :
    row (eightIndex i) ≤
      LinearFive.F.map (MulAut.conj (sixteenConjugator (eightContainer i))).toMonoidHom := by
  apply le_trans ?_ (sixteen_row_le_F_conjugate (eightContainer i))
  exact closure_mono (Set.image_mono (eight_masks_le i hi))

/-- Whole-subgroup placement for all twenty-five nonline rows, independently
of census exhaustiveness or any normalizer-cover assertion. -/
theorem nonline_row_le_F_conjugate (i : Fin 26) (hi : i ≠ 5) :
    ∃ g : Model, row i ≤ LinearFive.F.map (MulAut.conj g).toMonoidHom := by
  by_cases h : i.val < 16
  · let j : Fin 16 := ⟨i.val,h⟩
    have hj : j ≠ 5 := by intro he; apply hi; exact Fin.ext (congrArg (fun x : Fin 16 => x.val) he)
    exact ⟨_,nonline_eight_le_F_conjugate j hj⟩
  · let j : Fin 10 := ⟨i.val - 16,by omega⟩
    have he : sixteenIndex j = i := by apply Fin.ext; dsimp [sixteenIndex,j]; omega
    exact ⟨sixteenConjugator j,he ▸ sixteen_row_le_F_conjugate j⟩

/-- The same placement supplies a literal elementary F inside the whole
centralizer, rather than only placing individual elements in unrelated locals. -/
theorem nonline_row_F_centralizer (i : Fin 26) (hi : i ≠ 5) :
    ∃ g : Model, row i ≤ LinearFive.F.map (MulAut.conj g).toMonoidHom ∧
      LinearFive.F.map (MulAut.conj g).toMonoidHom ≤ centralizer (row i : Set Model) := by
  obtain ⟨g,hg⟩ := nonline_row_le_F_conjugate i hi
  refine ⟨g,hg,?_⟩
  let := LinearFive.F_elementary
  let : IsElementaryAbelian 2 (LinearFive.F.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  exact (LinearFive.F.map (MulAut.conj g).toMonoidHom).le_centralizer.trans (centralizer_le hg)

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry
