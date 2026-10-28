module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.PermutationComparison

/-!
# Checked endpoint and generator tables

Each scalar line has one unordered pair of distinct endpoints. The inverse
table covers every pair. The two line target tables certify the images of
the row representatives under the literal matrices A and B; their endpoints
move by the inverses of the comparison permutations.

Tables were reproduced from `../source/projective-certificate.json` using
`../source/check_projective_certificate.py`. They are candidate witnesses:
all properties used here are checked by the Lean kernel against the published
vectors, matrices and permutations. The ATLAS attribution is retained in
`../../../LinearModel/source/`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
namespace CoreProjectiveAction

/-- The unordered endpoint pair of a published scalar line. -/
def endpointPair (i : Fin 231) : Finset (Fin 22) :=
  {(projectiveEndpoints i).1, (projectiveEndpoints i).2}

private def targetA : Fin 231 → Fin 231 :=
  ![3, 21, 24, 47, 62, 1, 4, 22, 26, 45, 43, 48, 2, 25, 12, 23, 46, 44, 0, 61, 60, 141, 214, 114, 29, 159, 156, 110, 135, 191, 134, 215, 217, 179, 17, 153, 79, 219, 163, 177, 126, 56, 176, 124, 58, 205, 91, 116, 230, 55, 7, 228, 50, 216, 84, 227, 196, 206, 229, 226, 188, 225, 213, 160, 223, 164, 201, 115, 85, 14, 203, 162, 130, 49, 187, 6, 155, 37, 99, 59, 28, 82, 80, 96, 113, 67, 81, 97, 112, 98, 95, 117, 136, 33, 83, 194, 193, 72, 181, 184, 173, 200, 129, 166, 186, 27, 127, 218, 146, 210, 132, 157, 189, 143, 76, 74, 142, 68, 78, 42, 54, 123, 105, 5, 180, 178, 39, 131, 51, 133, 90, 190, 18, 170, 93, 171, 197, 8, 20, 167, 109, 172, 122, 224, 220, 71, 40, 13, 100, 165, 202, 35, 154, 89, 151, 111, 198, 118, 101, 86, 36, 138, 119, 121, 102, 139, 140, 120, 16, 87, 137, 147, 125, 152, 209, 145, 88, 183, 38, 174, 106, 148, 104, 128, 15, 175, 169, 168, 53, 185, 92, 41, 199, 161, 182, 107, 207, 10, 65, 64, 11, 32, 30, 9, 63, 31, 66, 69, 34, 144, 158, 108, 208, 77, 57, 192, 94, 52, 204, 19, 150, 195, 149, 70, 222, 75, 221, 212, 211, 73, 103]

private def targetB : Fin 231 → Fin 231 :=
  ![2, 1, 0, 4, 3, 116, 115, 113, 117, 47, 112, 114, 141, 154, 188, 230, 111, 35, 213, 225, 205, 142, 143, 140, 139, 138, 137, 27, 32, 29, 30, 31, 28, 135, 179, 17, 110, 153, 177, 193, 218, 146, 194, 206, 82, 192, 127, 9, 212, 220, 222, 211, 93, 92, 94, 91, 56, 58, 57, 59, 197, 221, 169, 98, 172, 189, 171, 67, 68, 71, 70, 69, 72, 74, 73, 105, 103, 104, 106, 129, 183, 196, 44, 174, 168, 160, 195, 102, 90, 89, 88, 55, 53, 52, 54, 162, 164, 204, 63, 152, 208, 175, 87, 76, 77, 75, 78, 107, 108, 109, 36, 16, 10, 7, 11, 6, 5, 8, 118, 119, 123, 122, 121, 120, 173, 210, 132, 46, 184, 79, 219, 214, 126, 191, 134, 33, 136, 26, 25, 24, 23, 12, 21, 22, 161, 203, 41, 201, 228, 198, 224, 187, 99, 37, 13, 156, 155, 180, 209, 176, 85, 144, 95, 190, 96, 229, 227, 226, 84, 62, 170, 66, 64, 124, 83, 101, 159, 38, 185, 34, 157, 181, 199, 80, 128, 178, 207, 151, 14, 65, 163, 133, 45, 39, 42, 86, 81, 60, 149, 182, 200, 147, 217, 145, 97, 20, 43, 186, 100, 158, 125, 51, 48, 18, 131, 216, 215, 202, 40, 130, 49, 61, 50, 223, 150, 19, 167, 166, 148, 165, 15]

def pairIndex : Fin 22 → Fin 22 → Fin 231 :=
  ![![0, 178, 77, 124, 165, 193, 102, 174, 0, 78, 223, 218, 17, 65, 16, 196, 110, 158, 113, 66, 125, 115],
    ![178, 0, 99, 44, 46, 101, 38, 180, 129, 161, 209, 207, 204, 132, 3, 201, 74, 70, 139, 37, 164, 143],
    ![77, 99, 0, 159, 202, 183, 138, 135, 11, 71, 35, 90, 181, 41, 45, 51, 221, 97, 92, 162, 206, 227],
    ![124, 44, 159, 0, 225, 154, 63, 112, 14, 28, 40, 108, 88, 199, 52, 194, 140, 186, 76, 148, 179, 216],
    ![165, 46, 202, 225, 0, 49, 47, 50, 170, 190, 2, 188, 114, 85, 123, 230, 122, 79, 5, 205, 84, 8],
    ![193, 101, 183, 154, 49, 0, 203, 169, 220, 145, 39, 13, 80, 62, 131, 89, 214, 175, 59, 72, 118, 29],
    ![102, 38, 138, 63, 47, 203, 0, 58, 163, 200, 106, 32, 69, 187, 133, 219, 224, 144, 91, 184, 18, 167],
    ![174, 180, 135, 112, 50, 169, 58, 0, 160, 151, 189, 182, 146, 109, 12, 100, 94, 126, 75, 86, 64, 155],
    ![0, 129, 11, 14, 170, 220, 163, 160, 0, 9, 229, 19, 217, 222, 121, 15, 120, 127, 116, 20, 168, 117],
    ![78, 161, 71, 28, 190, 145, 200, 151, 9, 0, 87, 98, 25, 57, 150, 130, 191, 177, 55, 128, 213, 226],
    ![223, 209, 35, 40, 2, 39, 106, 189, 229, 87, 0, 173, 104, 83, 36, 81, 111, 185, 7, 171, 210, 6],
    ![218, 207, 90, 108, 188, 13, 32, 182, 19, 98, 173, 0, 176, 10, 23, 42, 93, 82, 103, 228, 34, 215],
    ![17, 204, 181, 88, 114, 80, 69, 146, 217, 25, 104, 176, 0, 33, 61, 211, 192, 152, 53, 95, 43, 166],
    ![65, 132, 41, 199, 85, 62, 187, 109, 222, 57, 83, 10, 33, 0, 54, 208, 141, 157, 105, 195, 172, 156],
    ![16, 3, 45, 52, 123, 131, 133, 12, 121, 150, 36, 23, 61, 54, 0, 60, 68, 73, 137, 48, 149, 142],
    ![196, 201, 51, 194, 230, 89, 219, 100, 15, 130, 81, 42, 211, 208, 60, 0, 197, 147, 31, 119, 107, 134],
    ![110, 74, 221, 140, 122, 214, 224, 94, 120, 191, 111, 93, 192, 141, 68, 197, 0, 4, 26, 212, 198, 21],
    ![158, 70, 97, 186, 79, 175, 144, 126, 127, 177, 185, 82, 152, 157, 73, 147, 4, 0, 24, 153, 96, 22],
    ![113, 139, 92, 76, 5, 59, 91, 75, 116, 55, 7, 103, 53, 105, 137, 31, 26, 24, 0, 30, 67, 1],
    ![66, 37, 162, 148, 205, 72, 184, 86, 20, 128, 171, 228, 95, 195, 48, 119, 212, 153, 30, 0, 56, 136],
    ![125, 164, 206, 179, 84, 118, 18, 64, 168, 213, 210, 34, 43, 172, 149, 107, 198, 96, 67, 56, 0, 27],
    ![115, 143, 227, 216, 8, 29, 167, 155, 117, 226, 6, 215, 166, 156, 142, 134, 21, 22, 1, 136, 27, 0]]

private theorem index_endpoints : ∀ i : Fin 231,
    pairIndex (projectiveEndpoints i).1 (projectiveEndpoints i).2 = i := by decide +kernel

private theorem index_symm : ∀ a b : Fin 22, pairIndex a b = pairIndex b a := by decide +kernel

theorem endpoints_ne : ∀ i : Fin 231,
    (projectiveEndpoints i).1 ≠ (projectiveEndpoints i).2 := by decide +kernel

theorem pairIndex_spec : ∀ a b : Fin 22, a ≠ b →
    endpointPair (pairIndex a b) = {a, b} := by decide +kernel

theorem endpointPair_injective : Function.Injective endpointPair := by
  intro i j h
  have hs : ({(projectiveEndpoints i).1, (projectiveEndpoints i).2} : Set (Fin 22)) =
      {(projectiveEndpoints j).1, (projectiveEndpoints j).2} := by
    simpa only [endpointPair, Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun s : Finset (Fin 22) => (s : Set (Fin 22))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [← index_endpoints i, h₁, h₂, index_endpoints]
  · rw [← index_endpoints i, h₁, h₂, index_symm, index_endpoints]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem generatorA_rows : ∀ i : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixA ∈
      scalarLine (projectiveVector (targetA i)) := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem generatorB_rows : ∀ i : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixB ∈
      scalarLine (projectiveVector (targetB i)) := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

private theorem generatorA_endpoints : ∀ i : Fin 231,
    endpointPair (targetA i) = (endpointPair i).image corePermA.symm := by decide +kernel

private theorem generatorB_endpoints : ∀ i : Fin 231,
    endpointPair (targetB i) = (endpointPair i).image corePermB.symm := by decide +kernel

theorem generatorA_data (i : Fin 231) : ∃ j : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixA ∈ scalarLine (projectiveVector j) ∧
    endpointPair j = (endpointPair i).image corePermA.symm :=
  ⟨targetA i, generatorA_rows i, generatorA_endpoints i⟩

theorem generatorB_data (i : Fin 231) : ∃ j : Fin 231,
    Matrix.vecMul (projectiveVector i) matrixB ∈ scalarLine (projectiveVector j) ∧
    endpointPair j = (endpointPair i).image corePermB.symm :=
  ⟨targetB i, generatorB_rows i, generatorB_endpoints i⟩

end CoreProjectiveAction
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
