module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit.Data
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlanePencil
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarPair
/-!
# The five native line-orbit representatives

The representative trios are entries of the existing catalogue. A checked
sextet identifies the disjoint coplanar pair. Restriction identities on the
twelve Golay rows supply annihilators for the radical sum; disjoint octads
supply all positive memberships. These certify the literal radical-defined
labels, not surrogate tags.

Source: AS91 (3.4), (5.4), pp.594,600.
-/
@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open scoped Pointwise Matrix
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
open SourceCycleBase.Native SourceCycleBase.Native.FarOrbit
noncomputable def rootLine (r : Fin 5) : Line := FarOrbit.entry (rootIndex r)
def rootMasks (r : Fin 5) : Fin 3 → BitVec 24 := (FarOrbit.row (rootIndex r)).masks
theorem root_parts (r : Fin 5) : (rootLine r).parts = parts (rootMasks r) :=
  FarOrbit.entry_parts _
def standardMasks : Fin 3 → BitVec 24 := ![1626816,2500912,12649487]
theorem standard_parts : standardTrio.parts = parts standardMasks := by decide +kernel

theorem root_zero : rootLine 0 = standardTrio := by
  apply line_parts_injective
  rw [root_parts,standard_parts]
  rfl

def separator : Fin 2 → BitVec 24 := ![14614530, 10354696]
def witness : Fin 2 → Fin 3 → Fin 4096 :=
  ![![197, 293, 21],
    ![128, 1072, 80]]

def allowed : Fin 5 → Fin 3 → Bool :=
  ![![true, true, true],
    ![true, true, true],
    ![true, true, true],
    ![false, true, false],
    ![false, false, false]]
def allowedParts (r : Fin 5) : Finset (Finset (Fin 24)) :=
  (Finset.univ.filter (fun j => allowed r j = true)).image (fun j => support (rootMasks r j))
def planeMasks : Fin 6 → BitVec 24 := ![10528, 20672, 66566, 1606144, 2490384, 12582921]
def planeMessage : Fin 6 → Fin 6 → Fin 4096 :=
  ![![0, 3552, 3366, 3872, 3376, 3369],
    ![3552, 0, 198, 704, 208, 201],
    ![3366, 198, 0, 518, 22, 15],
    ![3872, 704, 518, 0, 528, 521],
    ![3376, 208, 22, 528, 0, 25],
    ![3369, 201, 15, 521, 25, 0]]

theorem row_identity (f : Fin 2) (a : Fin 3) (i : Fin 12) :
    FarPair.dot (MathieuCode.wordOfMask (separator f)) (MathieuCode.row i) =
      FarPair.restriction (support (standardMasks a))
        (MathieuCode.wordOfMask (m24GolayCode (witness f a))) (MathieuCode.row i) := by
  revert f a i; decide +kernel

theorem radicalSum_le_ker (f : Fin 2) :
    radicalSum standardTrio ≤ (FarPair.dot (MathieuCode.wordOfMask (separator f)) ∘ₗ
      MathieuCode.golay.subtype).ker := by
  apply iSup_le
  rintro ⟨A,hA⟩
  rw [standard_parts] at hA
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
  simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at hb
  rcases hb with rfl|rfl|rfl
  all_goals exact FarPair.radical_le_ker_dot (witness f _) (row_identity f _)

theorem radical_octads (r : Fin 5) :
    octadsInRadicalSum standardTrio (rootLine r) = (allowedParts r : Set _) := by
  have exclude : ∀ (r : Fin 5) (j : Fin 3), allowed r j = false →
      ∃ f : Fin 2, FarPair.dot (MathieuCode.wordOfMask (separator f))
        (MathieuCode.wordOfSet (support (rootMasks r j))) ≠ 0 := by decide +kernel
  have include_octad : ∀ (r : Fin 5) (j : Fin 3), allowed r j = true →
      ∃ k : Fin 3, Disjoint (support (standardMasks k)) (support (rootMasks r j)) := by
    decide +kernel
  have memparts (a : Fin 3 → BitVec 24) (j : Fin 3) : support (a j) ∈ parts a := by
    apply Finset.mem_image.mpr
    refine ⟨a j,?_,rfl⟩
    fin_cases j <;> simp [maskParts]
  apply Set.ext
  intro A
  constructor
  · rintro ⟨hA,v,hv,he⟩
    rw [root_parts] at hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    have hbj : ∃ j : Fin 3, b = rootMasks r j := by
      simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with hb|hb|hb
      · exact ⟨0,hb⟩
      · exact ⟨1,hb⟩
      · exact ⟨2,hb⟩
    obtain ⟨j,rfl⟩ := hbj
    have ha : allowed r j = true := by
      by_contra hn
      obtain ⟨f,hf⟩ := exclude r j (Bool.eq_false_of_not_eq_true hn)
      have hh := radicalSum_le_ker f hv
      change FarPair.dot (MathieuCode.wordOfMask (separator f)) v.val = 0 at hh
      rw [he] at hh
      exact hf hh
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,rfl⟩
  · intro hA
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨k,hk⟩ := include_octad r j (Finset.mem_filter.mp hj).2
    have hB : support (rootMasks r j) ∈ (rootLine r).parts := by
      rw [root_parts]; exact memparts _ _
    have hC : support (standardMasks k) ∈ standardTrio.parts := by
      rw [standard_parts]; exact memparts _ _
    obtain ⟨v,hv,he⟩ := octad_in_radicalSum_of_disjoint hC ((rootLine r).octad _ hB) hk
    exact ⟨hB,v,hv,he⟩

theorem radical_octads_card (r : Fin 5) :
    (octadsInRadicalSum standardTrio (rootLine r)).ncard = (![3,3,3,1,0] : Fin 5 → ℕ) r := by
  rw [radical_octads,Set.ncard_coe_finset]
  revert r; decide +kernel

private theorem plane_word (i j : Fin 6) (hij : i ≠ j) :
    support (planeMasks i) ∪ support (planeMasks j) = m24GolayWord (planeMessage i j) := by
  revert i j; decide +kernel

private def witnessPlane : Plane where
  parts := Finset.univ.image (fun i => support (planeMasks i))
  card := by decide +kernel
  tetrad := by
    intro A hA
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    revert i; decide +kernel
  disjoint := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    revert i j; decide +kernel
  cover := by decide +kernel
  octad := by
    intro A hA B hB hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hB
    rw [plane_word i j (fun he => hne (he ▸ rfl))]
    apply m24GolayWord_mem_blocks_of_card_eq_eight
    revert i j; decide +kernel

private theorem root_two_coplanar : Coplanar standardTrio (rootLine 2) := by
  have hh : ∀ (r : Fin 5), r = 0 ∨ r = 2 → ∀ j : Fin 3,
      ∃ b c : Fin 6, b ≠ c ∧ support (rootMasks r j) =
        support (planeMasks b) ∪ support (planeMasks c) := by decide +kernel
  have incident (r : Fin 5) (hr : r = 0 ∨ r = 2) : Incident (rootLine r) witnessPlane := by
    intro A hA
    rw [root_parts] at hA
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hA
    have hbj : ∃ j : Fin 3, b = rootMasks r j := by
      simp only [maskParts,Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with hb|hb|hb
      · exact ⟨0,hb⟩
      · exact ⟨1,hb⟩
      · exact ⟨2,hb⟩
    obtain ⟨j,rfl⟩ := hbj
    obtain ⟨b,c,hbc,he⟩ := hh r hr j
    refine ⟨support (planeMasks b),Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩,
      support (planeMasks c),Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,?_,he⟩
    have hinj : Function.Injective (fun b : Fin 6 => support (planeMasks b)) := by decide +kernel
    exact hinj.ne hbc
  exact ⟨witnessPlane,root_zero ▸ incident 0 (Or.inl rfl),incident 2 (Or.inr rfl)⟩

private theorem not_root_coplanar (r : Fin 5) (hr : 2 < r.val) :
    ¬ Coplanar standardTrio (rootLine r) := by
  have cert : ∀ r : Fin 5, 2 < r.val → ∃ i j : Fin 3,
      ((support (standardMasks i)) ∩ support (rootMasks r j)).card = 2 := by decide +kernel
  obtain ⟨i,j,hij⟩ := cert r hr
  have hA : support (standardMasks i) ∈ standardTrio.parts := by
    rw [standard_parts]
    fin_cases i <;> decide +kernel
  have hB : support (rootMasks r j) ∈ (rootLine r).parts := by
    rw [root_parts]
    apply Finset.mem_image.mpr
    refine ⟨rootMasks r j,?_,rfl⟩
    fin_cases j <;> simp [maskParts]
  exact not_coplanar_of_inter_two hA hB hij

/-- Exactly one of the five source predicates holds at each representative. -/
theorem root_delta_iff (i r : Fin 5) : Delta i standardTrio (rootLine r) ↔ i = r := by
  have eqparts : ∀ r : Fin 5, (parts standardMasks = parts (rootMasks r)) ↔ r = 0 := by decide +kernel
  have shared : ∀ r : Fin 5,
      (parts standardMasks ≠ parts (rootMasks r) ∧
        (parts standardMasks ∩ parts (rootMasks r)).Nonempty) ↔ r = 1 := by decide +kernel
  have disjoint : ∀ r : Fin 5, Disjoint (parts standardMasks) (parts (rootMasks r)) ↔ 1 < r.val := by decide +kernel
  fin_cases i
  · change standardTrio.parts = (rootLine r).parts ↔ _
    rw [standard_parts,root_parts,eqparts,eq_comm]
    rfl
  · change (standardTrio.parts ≠ (rootLine r).parts ∧ _) ↔ _
    rw [standard_parts,root_parts,shared,eq_comm]
    rfl
  · change (Disjoint standardTrio.parts (rootLine r).parts ∧ Coplanar standardTrio (rootLine r)) ↔ _
    rw [standard_parts,root_parts,disjoint]
    constructor
    · rintro ⟨hd,hc⟩
      have hn : ¬ 2 < r.val := fun hr => not_root_coplanar r hr hc
      apply Fin.ext
      change 2 = r.val
      omega
    · rintro rfl
      exact ⟨by decide,root_two_coplanar⟩
  · change (octadsInRadicalSum standardTrio (rootLine r)).ncard = 1 ↔ _
    rw [radical_octads_card]
    revert r; decide +kernel
  · change octadsInRadicalSum standardTrio (rootLine r) = ∅ ↔ _
    rw [radical_octads]
    have hh : ∀ r : Fin 5, allowedParts r = ∅ ↔ r = 4 := by decide +kernel
    rw [Finset.coe_eq_empty,hh,eq_comm]
    rfl

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
