module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarPair
/-!
# A native δ₃ pair with a common δ₁ line

The literal trios are already certified Golay objects. One coordinate linear
form annihilates all three octad radicals and excludes two octads of the
second trio; a disjoint octad proves membership of the third. Thus the actual
radical intersection has exactly one octad. The checked common δ₁ line is
transported to each ambient δ₃ pair using the original orbital action.

Source: Aschbacher–Segev (1991), (3.10), applied in (7.4), pp.596,603–604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Matrix
namespace ThreePair
open FarOrbit

def separator : BitVec 24 := 133130
def witness : Fin 3 → Fin 4096 := ![4042,4031,4042]

theorem row_identity (a : Fin 3) (i : Fin 12) :
    FarPair.dot (MathieuCode.wordOfMask separator) (MathieuCode.row i) =
      FarPair.restriction (support (FarPair.masks a))
        (MathieuCode.wordOfMask (m24GolayCode (witness a))) (MathieuCode.row i) := by
  revert a i; decide +kernel

theorem radicalSum_le_ker :
    radicalSum FarPair.line ≤ (FarPair.dot (MathieuCode.wordOfMask separator) ∘ₗ
      MathieuCode.golay.subtype).ker := by
  apply iSup_le
  rintro ⟨A,hA⟩
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  all_goals exact FarPair.radical_le_ker_dot (witness _) (row_identity _)

theorem radical_octads : octadsInRadicalSum FarPair.line (seedLine 1) =
    {support (seedMasks 1 2)} := by
  apply Set.ext
  intro A
  constructor
  · rintro ⟨hA,v,hv,he⟩
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
    have hz := radicalSum_le_ker hv
    change FarPair.dot (MathieuCode.wordOfMask separator) v.val = 0 at hz
    rw [he] at hz
    rcases ha with rfl|rfl|rfl
    · have hn : FarPair.dot (MathieuCode.wordOfMask separator)
          (fun i => if i ∈ support (seedMasks 1 0) then 1 else 0) ≠ 0 := by decide +kernel
      exact (hn hz).elim
    · have hn : FarPair.dot (MathieuCode.wordOfMask separator)
          (fun i => if i ∈ support (seedMasks 1 1) then 1 else 0) ≠ 0 := by decide +kernel
      exact (hn hz).elim
    · exact rfl
  · rintro rfl
    have ha : support (FarPair.masks 0) ∈ FarPair.line.parts := by decide +kernel
    have hb : support (seedMasks 1 2) ∈ (seedLine 1).parts := by decide +kernel
    obtain ⟨v,hv,he⟩ := octad_in_radicalSum_of_disjoint ha ((seedLine 1).octad _ hb)
      (by decide +kernel : Disjoint (support (FarPair.masks 0)) (support (seedMasks 1 2)))
    exact ⟨hb,v,hv,he⟩

theorem delta_three : Delta 3 FarPair.line (seedLine 1) := by
  change (octadsInRadicalSum FarPair.line (seedLine 1)).ncard = 1
  rw [radical_octads,Set.ncard_singleton]

theorem common_delta_one : Delta 1 FarPair.line (seedLine 3) ∧
    Delta 1 (seedLine 1) (seedLine 3) := by
  constructor
  · change FarPair.line.parts ≠ (seedLine 3).parts ∧
      (FarPair.line.parts ∩ (seedLine 3).parts).Nonempty
    decide +kernel
  · change (seedLine 1).parts ≠ (seedLine 3).parts ∧
      ((seedLine 1).parts ∩ (seedLine 3).parts).Nonempty
    decide +kernel

end ThreePair
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
