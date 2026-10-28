module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases.Data

/-!
# Soundness of literal packed certificate rows

All literals are compared with the supplied tables before their arithmetic is
used. Literal operands avoid repeated indexed reduction in the kernel's inner
multiplication loop. Coverage of the indices ensures every row is checked.
The actual consumers certify the original ATLAS M24 degree-1242 orbit bases;
source and conventions are recorded in `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases

/-- A row's index and its literal packed value; all table links are checked. -/
abbrev ValueRow := ℕ × ℕ

def inverseRowCheck (xs ys : List ℕ) (c : ValueRow) : Bool :=
  (entry ys c.1 == c.2) && (packedRow c.2 xs 0 == 2 ^ c.1)

def transposeRowCheck (xs ys : List ℕ) (c : ValueRow) : Bool :=
  (entry ys c.1 == c.2) && (transposeRow xs c.1 == c.2)

theorem inverseRow_sound (xs ys : List ℕ) (c : ValueRow)
    (h : inverseRowCheck xs ys c = true) :
    packedRow (entry ys c.1) xs 0 = 2 ^ c.1 := by
  simp only [inverseRowCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1]
  exact h.2

theorem transposeRow_sound (xs ys : List ℕ) (c : ValueRow)
    (h : transposeRowCheck xs ys c = true) :
    transposeRow xs c.1 = entry ys c.1 := by
  simp only [transposeRowCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.trans h.1.symm

structure StepRow where
  index : ℕ
  parent : ℕ
  letter : Bool
  input : ℕ
  output : ℕ

def stepRowCheck (xs parents letters a b : List ℕ) (c : StepRow) : Bool :=
  c.index == 0 ||
    ((c.parent == entry parents c.index) &&
    (c.letter == (entry letters c.index == 1)) &&
    (c.input == entry xs c.parent) &&
    (c.output == entry xs c.index) &&
    decide (c.parent < c.index) &&
    (packedRow c.input (if c.letter then b else a) 0 == c.output))

theorem stepRow_sound (xs parents letters a b : List ℕ) (c : StepRow)
    (h : stepRowCheck xs parents letters a b c = true) :
    (c.index == 0 || (decide (entry parents c.index < c.index) &&
      packedRow (entry xs (entry parents c.index))
        (if entry letters c.index == 1 then b else a) 0 == entry xs c.index)) = true := by
  simp only [stepRowCheck, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h ⊢
  rcases h with hz | ⟨⟨⟨⟨⟨hp, hl⟩, hu⟩, hv⟩, hlt⟩, he⟩
  · exact Or.inl hz
  · apply Or.inr
    refine ⟨by simpa only [hp] using hlt, ?_⟩
    simpa only [hu, hp, hl, hv, beq_iff_eq] using he

/-- A checked list whose indices cover the interval supplies every coordinate. -/
theorem all_of_cover {α : Type*} (n : ℕ) (index : α → ℕ)
    (cs : List α) (check : α → Bool)
    (hcover : cs.map index = List.range n) (hcheck : cs.all check = true) :
    ∀ i : Fin n, ∃ c ∈ cs, index c = i.val ∧ check c = true := by
  intro i
  have hi : i.val ∈ cs.map index := by
    rw [hcover]
    exact List.mem_range.mpr i.isLt
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hi
  exact ⟨c, hc, he, List.all_eq_true.mp hcheck c hc⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.OrbitBases
