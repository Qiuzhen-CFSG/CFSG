module
public import Theory.Mathieu.M12.Properties.ThreeConjugates.Data

/-!
# Kernel-checked generating triples in the M₁₂ automorphism carrier

Each explicit representative has two conjugators in the marked inner subgroup.
Short words in the resulting triple recover both inner generators, proving the
required containment directly. Every permutation identity is kernel-checked.
See `Data` and `source/generation.txt` for generator provenance and search data.
This is the finite generation input to `ThreeConjugates`, used for the degree
window in Aschbacher–Smith Chapter K, printed pp.451 and 457.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ThreeConjugates
open M12ExceptionalExtension Subgroup
set_option maxRecDepth 4096

theorem word_mem {G : Type*} [Group G] (H : Subgroup G)
    (s : Fin 3 → G) (hs : ∀ i, s i ∈ H) (w : List (Fin 3)) : word s w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hs i) ih

theorem representative_check : ∀ i : Fin 3,
    representativePerm i = ((word outerGenerators (representativeWords i) : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel
theorem firstConjugator_check : ∀ i : Fin 3,
    firstConjugatorPerm i = ((word innerGenerators (firstConjugatorWords i) : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel
theorem secondConjugator_check : ∀ i : Fin 3,
    secondConjugatorPerm i = ((word innerGenerators (secondConjugatorWords i) : Carrier) : Equiv.Perm (Fin 24)) := by
  decide +kernel

def representative (i : Fin 3) : Carrier :=
  ⟨representativePerm i, representative_check i ▸ (word outerGenerators (representativeWords i)).property⟩
def firstConjugator (i : Fin 3) : Carrier :=
  ⟨firstConjugatorPerm i, firstConjugator_check i ▸ (word innerGenerators (firstConjugatorWords i)).property⟩
def secondConjugator (i : Fin 3) : Carrier :=
  ⟨secondConjugatorPerm i, secondConjugator_check i ▸ (word innerGenerators (secondConjugatorWords i)).property⟩

def triple (i : Fin 3) : Fin 3 → Carrier :=
  ![representative i,
    firstConjugator i * representative i * (firstConjugator i)⁻¹,
    secondConjugator i * representative i * (secondConjugator i)⁻¹]
theorem innerA_check : ∀ i : Fin 3, word (triple i) (innerAWords i) = innerA := by
  decide +kernel
theorem innerB_check : ∀ i : Fin 3, word (triple i) (innerBWords i) = innerB := by
  decide +kernel


/-- Generation with both conjugators in the literal marked inner subgroup. -/
def Generates (t : Carrier) : Prop :=
  ∃ g ∈ inner, ∃ h ∈ inner, inner ≤
    zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹)

private theorem innerGenerators_mem (i : Fin 3) : innerGenerators i ∈ inner := by
  have ha : innerA ∈ inner := subset_closure (by simp)
  have hb : innerB ∈ inner := subset_closure (by simp)
  rw [innerGenerators_eq]
  fin_cases i
  · exact ha
  · exact hb
  · exact inner.inv_mem hb

/-- The first checked conjugator is in the index-two inner subgroup. -/
theorem firstConjugator_mem (i : Fin 3) : firstConjugator i ∈ inner := by
  have he : firstConjugator i = word innerGenerators (firstConjugatorWords i) :=
    Subtype.ext (firstConjugator_check i)
  rw [he]
  exact word_mem inner innerGenerators innerGenerators_mem _

/-- The second checked conjugator is in the index-two inner subgroup. -/
theorem secondConjugator_mem (i : Fin 3) : secondConjugator i ∈ inner := by
  have he : secondConjugator i = word innerGenerators (secondConjugatorWords i) :=
    Subtype.ext (secondConjugator_check i)
  rw [he]
  exact word_mem inner innerGenerators innerGenerators_mem _

/-- Each of the three concrete triples contains both generators of the whole
marked inner group; no group order inferred by the search is used. -/
theorem representative_generates (i : Fin 3) : Generates (representative i) := by
  refine ⟨firstConjugator i, firstConjugator_mem i,
    secondConjugator i, secondConjugator_mem i, ?_⟩
  let D := zpowers (representative i) ⊔
    zpowers (firstConjugator i * representative i * (firstConjugator i)⁻¹) ⊔
    zpowers (secondConjugator i * representative i * (secondConjugator i)⁻¹)
  have hs (j : Fin 3) : triple i j ∈ D := by
    fin_cases j
    · exact (show zpowers (representative i) ≤ D from le_sup_of_le_left le_sup_left) (mem_zpowers _)
    · exact (show zpowers (firstConjugator i * representative i * (firstConjugator i)⁻¹) ≤ D from le_sup_of_le_left le_sup_right) (mem_zpowers _)
    · exact (show zpowers (secondConjugator i * representative i * (secondConjugator i)⁻¹) ≤ D from le_sup_right) (mem_zpowers _)
  change Subgroup.closure ({innerA, innerB} : Set Carrier) ≤ D
  apply (closure_le D).mpr
  intro x hx
  rcases hx with (rfl | rfl)
  · rw [← innerA_check i]
    exact word_mem D (triple i) hs _
  · rw [← innerB_check i]
    exact word_mem D (triple i) hs _
end Sporadic.Mathieu.M12ThreeConjugates
