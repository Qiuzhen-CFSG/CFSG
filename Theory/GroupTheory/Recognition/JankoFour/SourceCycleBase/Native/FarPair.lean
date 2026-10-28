module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Hitting
/-!
# A checked far pair with a common perpendicular

The three trios and their two sextets are literal native Golay objects.
Two coordinate linear forms annihilate the radical sum of the first trio:
each is checked on the twelve generating rows against a restriction by an
explicit Golay word. They separate all three octads of the second trio,
proving the actual δ₄ relation. The third trio is δ₂ from both.
The ambient orbital transitivity transports this witness in `FarGeometry`.

Source: Aschbacher–Segev (1991), (3.13.2), p.596.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise Matrix
namespace FarPair
open FarOrbit

def masks : Fin 3 → BitVec 24 := ![133183,2908992,13735040]
def message : Fin 3 → Fin 4096 := ![1087,2880,128]

theorem word (j : Fin 3) : support (masks j) = m24GolayWord (message j) := by
  revert j; decide +kernel

def line : Line where
  parts := parts masks
  card := by decide +kernel
  octad := by
    intro A hA
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl
    all_goals rw [word]; apply m24GolayWord_mem_blocks_of_card_eq_eight
    all_goals decide +kernel
  disjoint := by
    intro A hA B hB hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hB
    simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl
    all_goals revert hne; decide +kernel
  cover := by decide +kernel

theorem line_incident : Incident line standardSextet := by
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  · exact ⟨standardTetrad 0,by decide +kernel,standardTetrad 4,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 3,by decide +kernel,standardTetrad 5,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact ⟨standardTetrad 1,by decide +kernel,standardTetrad 2,by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- Pairing against a literal binary coordinate word. -/
def dot (w : MathieuCode.Full) : MathieuCode.Full →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i, v i * w i
  map_add' v u := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_assoc,Finset.mul_sum]

def restriction (A : Finset (Fin 24)) (w : MathieuCode.Full) : MathieuCode.Full →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i ∈ A, v i * w i
  map_add' v u := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c v := by simp [mul_assoc,Finset.mul_sum]

/-- A checked row identity turns a codeword into a radical annihilator. -/
theorem radical_le_ker_dot {A : Finset (Fin 24)} {F : MathieuCode.Full}
    (u : Fin 4096)
    (ht : ∀ i : Fin 12, dot F (MathieuCode.row i) =
      restriction A (MathieuCode.wordOfMask (m24GolayCode u)) (MathieuCode.row i)) :
    radical A ≤ (dot F ∘ₗ MathieuCode.golay.subtype).ker := by
  intro v hv
  change dot F v.val = 0
  have he : dot F v.val = restriction A (MathieuCode.wordOfMask (m24GolayCode u)) v.val := by
    apply LinearMap.eqOn_span (s := Set.range MathieuCode.row) ?_ v.property
    rintro _ ⟨i,rfl⟩
    exact ht i
  rw [he]
  exact hv ⟨MathieuCode.wordOfMask (m24GolayCode u),MathieuCode.wordOfMask_code_mem u⟩

def separator : Fin 2 → BitVec 24 := ![2752,2577]
def witness : Fin 2 → Fin 3 → Fin 4096 := ![![4074,4066,4055],![3899,4072,4061]]

theorem row_identity (f : Fin 2) (a : Fin 3) (i : Fin 12) :
    dot (MathieuCode.wordOfMask (separator f)) (MathieuCode.row i) =
      restriction (support (seedMasks 2 a))
        (MathieuCode.wordOfMask (m24GolayCode (witness f a))) (MathieuCode.row i) := by
  revert f a i; decide +kernel

theorem radicalSum_le_ker (f : Fin 2) :
    radicalSum (seedLine 2) ≤ (dot (MathieuCode.wordOfMask (separator f)) ∘ₗ
      MathieuCode.golay.subtype).ker := by
  apply iSup_le
  rintro ⟨A,hA⟩
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl
  all_goals exact radical_le_ker_dot (witness f _) (row_identity f _)

theorem delta_four : Delta 4 (seedLine 2) line := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨hA,v,hv,he⟩ := hA
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at ha
  have zero (f : Fin 2) := radicalSum_le_ker f hv
  change ∀ f, dot (MathieuCode.wordOfMask (separator f)) v.val = 0 at zero
  rw [he] at zero
  rcases ha with rfl|rfl|rfl
  · have hz := zero 0
    have hn : dot (MathieuCode.wordOfMask (separator 0))
        (fun i => if i ∈ support (masks 0) then 1 else 0) ≠ 0 := by decide +kernel
    exact hn hz
  · have hz := zero 1
    have hn : dot (MathieuCode.wordOfMask (separator 1))
        (fun i => if i ∈ support (masks 1) then 1 else 0) ≠ 0 := by decide +kernel
    exact hn hz
  · have hz := zero 0
    have hn : dot (MathieuCode.wordOfMask (separator 0))
        (fun i => if i ∈ support (masks 2) then 1 else 0) ≠ 0 := by decide +kernel
    exact hn hz

/-- A literal representative of source (3.13.2), including both planes. -/
theorem common_delta_two : Delta 2 (seedLine 2) (seedLine 5) ∧ Delta 2 line (seedLine 5) := by
  constructor
  · exact ⟨by decide +kernel,nearPlane 1,seed_two_incident_plane,near_two_incident_plane⟩
  · exact ⟨by decide +kernel,standardSextet,line_incident,near_two_incident_standard⟩
end FarPair
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native
