module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co2.CentralizerSection.ActionData
public import Theory.SpecificGroups.PSp4Three.Generation
public import Mathlib.Algebra.Field.ZMod

/-!
# The two block matrices generate Sp6(2)

One explicit word is a transvection. Its conjugates include every nonzero
transvection, because explicit words carry its center to each nonzero vector.
The uniform transvection-generation theorem then gives the full matrix group.
The finite certificates concern only 64 vectors, not enumeration of the group.

Source: GLS3 Table 5.3k; matrix data derived from ATLAS Co2G1-p2300B0.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co2.CentralizerSection
open Theory.GroupTheory Matrix.PSp4Three

noncomputable def matrixLetter : Fin 4 → S :=
  ![matrixGenerator 0, matrixGenerator 1, (matrixGenerator 0)⁻¹, (matrixGenerator 1)⁻¹]

def letterPacked : Fin 4 → Nat := ![26653917752799743781071378081828629891334047585236940674900366554574664037881563026202257794685683547153465681747520, 3565016276190824032825685685667220565243772959193906284612347982458825636674850509372558677260970644003560772222400, 33059631877171853165356072180876803594721540569811969267401391881584739133572027512089627820665731126087434196870720, 15066951700722321664784537145163260077885406515454155029557518616162105321368966621286740080417667254547957432488320]

def letterImage (i : Fin 4) (v : Fin 64) : Fin 64 :=
  ⟨((letterPacked i) >>> (6 * v.val)) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 20000 in
private theorem inverse_image_check : ∀ v,
    matrixImage 0 (letterImage 2 v) = v ∧ matrixImage 1 (letterImage 3 v) = v := by
  decide +kernel

/-- Inverse letters use inverse action, avoiding repeated matrix inversion. -/
theorem matrixLetter_image (i : Fin 4) (v : Fin 64) :
    matrixLetter i • vector v = vector (letterImage i v) := by
  fin_cases i
  · exact matrixGenerator_image 0 v
  · exact matrixGenerator_image 1 v
  · change (matrixGenerator 0)⁻¹ • vector v = vector (letterImage 2 v)
    rw [inv_smul_eq_iff, matrixGenerator_image, (inverse_image_check v).1]
  · change (matrixGenerator 1)⁻¹ • vector v = vector (letterImage 3 v)
    rw [inv_smul_eq_iff, matrixGenerator_image, (inverse_image_check v).2]

def wordImage : List (Fin 4) → Fin 64 → Fin 64
  | [], v => v
  | i :: w, v => letterImage i (wordImage w v)

theorem matrixWord_image (w : List (Fin 4)) (v : Fin 64) :
    evalWord matrixLetter w • vector v = vector (wordImage w v) := by
  induction w with
  | nil => exact one_smul _ _
  | cons i w ih => rw [evalWord, mul_smul, ih, matrixLetter_image, wordImage]

def transvectionWord : List (Fin 4) := [3, 2, 3, 3, 0, 1, 1, 0, 3, 3, 0, 1, 0]

def orbitWord : Fin 64 → List (Fin 4) := ![[], [3, 2, 1, 0], [3, 3, 3, 2], [0, 0, 1], [0, 0, 1, 0], [1, 2], [1, 2, 1, 0, 0], [0, 1], [3, 2, 2], [1, 0, 1, 0, 1], [0, 1, 0, 0], [2, 1], [0, 3, 0], [1, 1, 0], [2, 2, 1, 0], [3, 0, 0, 1], [2, 2, 2], [3, 0], [2, 1, 1], [1, 2, 2], [1, 0, 0, 1], [1, 1, 2], [3, 2, 1], [3, 0, 0, 0], [3, 2], [1, 1, 0, 0], [0, 1, 2], [3], [2, 3], [1, 2, 3], [3, 3, 0, 0], [0, 1, 0, 1], [1, 1, 1, 0], [1, 2, 1], [0, 1, 2, 3], [3, 3, 2], [2, 2, 1, 2], [1, 0, 0], [1, 0], [2, 1, 2, 2], [3, 2, 3, 0], [1, 2, 1, 1], [0, 1, 0], [], [1, 1], [1], [0, 0, 3, 0], [0, 1, 1, 2], [2, 1, 0, 0], [2, 2, 3], [0, 0], [2, 1, 2], [1, 2, 2, 1, 0], [2, 2], [1, 0, 1], [2, 1, 0], [0, 3, 2], [2, 3, 0], [3, 2, 2, 2], [1, 1, 2, 1], [0, 0, 0], [0], [3, 0, 0], [2]]

set_option maxRecDepth 20000 in
private theorem transvection_check : ∀ x : Fin 64,
    vector (wordImage transvectionWord x) =
      vector x + (form (vector x) (vector 43)) • vector 43 := by decide +kernel

set_option maxRecDepth 20000 in
private theorem orbit_check : ∀ v : Fin 64, v ≠ 0 → wordImage (orbitWord v) 43 = v := by
  decide +kernel

/-- A concrete word is the transvection with center numbered 43. -/
theorem transvectionWord_eq :
    evalWord matrixLetter transvectionWord = transvection (vector 43) 1 := by
  apply ext_action
  intro x
  obtain ⟨i, rfl⟩ := vector_surjective x
  rw [matrixWord_image, transvection_apply, one_mul]
  exact transvection_check i

/-- Every subgroup containing the two matrices contains the whole symplectic group. -/
theorem matrix_generators_generate (H : Subgroup S)
    (h : ∀ i, matrixGenerator i ∈ H) : H = ⊤ := by
  have hl : ∀ i, matrixLetter i ∈ H := by
    intro i
    fin_cases i
    · exact h 0
    · exact h 1
    · exact H.inv_mem (h 0)
    · exact H.inv_mem (h 1)
  have hw (w : List (Fin 4)) : evalWord matrixLetter w ∈ H := by
    induction w with
    | nil => exact H.one_mem
    | cons i w ih => exact H.mul_mem (hl i) ih
  have ht : transvection (vector 43) 1 ∈ H := transvectionWord_eq ▸ hw transvectionWord
  have htrans (v : V) (a : ZMod 2) : transvection v a ∈ H := by
    fin_cases a
    · change transvection v (0 : ZMod 2) ∈ H
      rw [transvection_zero]
      exact H.one_mem
    · change transvection v (1 : ZMod 2) ∈ H
      obtain ⟨i, rfl⟩ := vector_surjective v
      by_cases hi : i = 0
      · subst i
        have hz : vector 0 = 0 := by decide +kernel
        rw [hz, transvection_zero_vector]
        exact H.one_mem
      · have hc := H.mul_mem (H.mul_mem (hw (orbitWord i)) ht) (H.inv_mem (hw (orbitWord i)))
        rw [transvection_conjugate, matrixWord_image, orbit_check i hi] at hc
        exact hc
  have hle : transvectionGroup 3 (ZMod 2) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v, a, rfl⟩
    exact htrans v a
  rw [transvectionGroup_eq_top] at hle
  exact top_unique hle

end Sporadic.LeechRelated.Co2.CentralizerSection
