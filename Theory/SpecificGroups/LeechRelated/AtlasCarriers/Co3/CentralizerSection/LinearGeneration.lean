module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearData
public import Theory.SpecificGroups.PSp4Three.Generation
public import Mathlib.Algebra.Field.ZMod

/-!
# The three fixed Co₃ quotient matrices generate Sp₆(2)

Generator 0 is the transvection in the direction f₁+f₂. The retained words
of length at most four carry that direction to all 63 nonzero binary vectors.
Conjugation therefore supplies every transvection, and the structural generation
theorem gives the full symplectic matrix group. All finite checks use kernel
reduction on six-bit vectors, without enumerating the matrix group.

The structural theorem is reused from `PSp4Three.Generation`, whose
characteristic-independent ATLAS port retains its attribution and license.
The matrix and orbit witnesses are from `CentralizerSection/source/`; the
packed action tables below can be reproduced by `LinearGeneration/source/tables.py`.
Source motivation: GLS3 Table 5.3j; Aschbacher–Smith A.2.19, printed pp.40–41.
-/

namespace Sporadic.LeechRelated.Co3.CentralizerSection
open Matrix.PSp4Three

private abbrev V := Vector 3 (ZMod 2)

/-- Bits 0,1,2 are the first hyperbolic half; bits 3,4,5 are the second. -/
private def vector (i : Fin 64) : V :=
  fun j => if i.val.testBit (LinearData.coordinate j).val then 1 else 0

set_option maxRecDepth 20000 in
private theorem vector_surjective : Function.Surjective vector := by decide +kernel

private noncomputable def letter : Fin 6 → LinearData.Sp :=
  ![LinearData.generator 0, LinearData.generator 1, LinearData.generator 2,
    (LinearData.generator 0)⁻¹, (LinearData.generator 1)⁻¹, (LinearData.generator 2)⁻¹]

private def letterPacked : Fin 6 → Nat :=
  ![39157600251751410974374028707619041331417471266309328894014463100453110163472518803085247710462302094597077368415808,
    39287781691211503326038303773991547224421478905182991985063704512330464205863270525564631361789029576324170657264320,
    23906807030838148191605219819290851806971649497195821044507392885535724540392318763903224044643281251812499811120320,
    39157600251751410974374028707619041331417471266309328894014463100453110163472518803085247710462302094597077368415808,
    39269444235704349904243692946347201895660090209826906425459027712681647058640867481689560773214957780457830806131520,
    29177058839273179821234170302265139239391760269762463845356575452720454517166137054191273009423120014308738562702720]

private def letterImage (i : Fin 6) (v : Fin 64) : Fin 64 :=
  ⟨(letterPacked i >>> (6 * v.val)) % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 20000 in
private theorem generator_image : ∀ (i : Fin 3) (v : Fin 64),
    LinearData.generator i • vector v = vector (letterImage (i.castAdd 3) v) := by
  apply Tables.allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem inverse_image_check : ∀ v,
    letterImage 0 (letterImage 3 v) = v ∧
    letterImage 1 (letterImage 4 v) = v ∧
    letterImage 2 (letterImage 5 v) = v := by
  apply Tables.allFin
  decide +kernel

private theorem letter_image (i : Fin 6) (v : Fin 64) :
    letter i • vector v = vector (letterImage i v) := by
  fin_cases i
  · exact generator_image 0 v
  · exact generator_image 1 v
  · exact generator_image 2 v
  · change (LinearData.generator 0)⁻¹ • vector v = vector (letterImage 3 v)
    rw [inv_smul_eq_iff, generator_image]
    exact congrArg vector (inverse_image_check v).1.symm
  · change (LinearData.generator 1)⁻¹ • vector v = vector (letterImage 4 v)
    rw [inv_smul_eq_iff, generator_image]
    exact congrArg vector (inverse_image_check v).2.1.symm
  · change (LinearData.generator 2)⁻¹ • vector v = vector (letterImage 5 v)
    rw [inv_smul_eq_iff, generator_image]
    exact congrArg vector (inverse_image_check v).2.2.symm

private def wordImage : List (Fin 6) → Fin 64 → Fin 64
  | [], v => v
  | i :: w, v => letterImage i (wordImage w v)

private theorem word_image (w : List (Fin 6)) (v : Fin 64) :
    (w.map letter).prod • vector v = vector (wordImage w v) := by
  induction w with
  | nil => exact one_smul _ _
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons, mul_smul, ih, letter_image, wordImage]

private def orbitWord : Fin 64 → List (Fin 6) :=
  ![[], [1, 1, 5], [1, 1, 2, 4], [2, 1, 1], [5, 0, 2, 4], [0, 1, 1], [4, 4], [5, 0, 1, 1], [2, 0, 4], [1, 2, 1], [2, 4, 2], [2, 1, 1, 1], [5, 1, 2, 1], [1, 5], [5, 4], [1, 2, 2, 1], [4, 5], [4, 2], [1, 1, 2], [5, 0, 1], [2, 2], [0, 1, 5], [2, 4, 4], [2, 2, 1], [], [5, 0, 5], [5, 4, 4], [4, 0, 1, 1], [5, 4, 5], [1, 1], [0, 4, 4], [4, 4, 5], [2, 2, 4], [0, 1], [4], [4, 5, 0, 1], [1, 0, 1], [2, 4], [5], [1, 1, 1], [4, 2, 1], [0, 1, 2, 4], [5, 4, 2], [1, 0, 1, 2], [2, 1, 2], [2], [1, 2], [5, 5, 5], [2, 1], [1, 2, 4], [4, 0, 5], [4, 5, 1], [1, 0, 5], [5, 1], [0, 1, 2], [5, 1, 1, 2], [2, 2, 1, 1], [1], [0, 4], [4, 5, 4, 2], [1, 2, 1, 1], [0, 2, 4], [0, 5], [5, 5]]

set_option maxRecDepth 20000 in
private theorem orbit_check : ∀ v : Fin 64, v ≠ 0 → wordImage (orbitWord v) 24 = v := by
  apply Tables.allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem transvection_check : ∀ x : Fin 64,
    LinearData.generator 0 • vector x =
      vector x + (form (vector x) (vector 24)) • vector 24 := by
  apply Tables.allFin
  decide +kernel

private theorem generator_zero_eq_transvection :
    LinearData.generator 0 = transvection (vector 24) 1 := by
  apply ext_action
  intro x
  obtain ⟨i, rfl⟩ := vector_surjective x
  rw [transvection_apply, one_mul]
  exact transvection_check i

private theorem subgroup_eq_top (H : Subgroup LinearData.Sp)
    (h : ∀ i, LinearData.generator i ∈ H) : H = ⊤ := by
  have hl : ∀ i, letter i ∈ H := by
    intro i
    fin_cases i
    · exact h 0
    · exact h 1
    · exact h 2
    · exact H.inv_mem (h 0)
    · exact H.inv_mem (h 1)
    · exact H.inv_mem (h 2)
  have hw (w : List (Fin 6)) : (w.map letter).prod ∈ H := by
    induction w with
    | nil => exact H.one_mem
    | cons i w ih => exact H.mul_mem (hl i) ih
  have ht : transvection (vector 24) 1 ∈ H := generator_zero_eq_transvection ▸ h 0
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
      · have hc := H.mul_mem (H.mul_mem (hw (orbitWord i)) ht)
          (H.inv_mem (hw (orbitWord i)))
        rw [transvection_conjugate, word_image, orbit_check i hi] at hc
        exact hc
  have hle : transvectionGroup 3 (ZMod 2) ≤ H := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨v, a, rfl⟩
    exact htrans v a
  rw [transvectionGroup_eq_top] at hle
  exact top_unique hle

/-- The three displayed matrices generate the full binary symplectic matrix group. -/
public theorem linear_generators_generate :
    Subgroup.closure (Set.range LinearData.generator) = (⊤ : Subgroup LinearData.Sp) :=
  subgroup_eq_top _ (fun i => Subgroup.subset_closure ⟨i, rfl⟩)

end Sporadic.LeechRelated.Co3.CentralizerSection
