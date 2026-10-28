module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.OctadGeometry
public import Theory.Mathieu.M24.LocalGeometry.FourNormalizers.Overgroups.Rows
/-!
# Five ambient normalizers preserve the fixed-octad trio

Rows 3, 7, 11 and 13 recover the trio as their elements' fixed octads.
Row 19 recovers it as the nonempty fixed sets shared by distinct elements.
Conjugation therefore preserves the actual trio in the native Witt design.
The next module connects its stabilizer to the elementary candidate normalizer.

Source: GLS3 Table 5.3e; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
open Subgroup
open scoped Pointwise
set_option maxRecDepth 100000

/-- This is the actual stabilizer of the fixed-octad trio of row 3. -/
noncomputable def trioGroup : Subgroup M24 :=
  MulAction.stabilizer M24 (FourNormalizers.rowGeometry 2)

def trioRow : Fin 4 → Fin 22 := ![3,7,11,13]
def trioWord : Fin 3 → Fin 64 := ![1,2,3]

private theorem trio_fixed_check : ∀ (r : Fin 4) (j : Fin 64),
    (fixedSet (fixedClass (rowCode (trioRow r) j))).card = 8 →
      fixedSet (fixedClass (rowCode (trioRow r) j)) ∈ FourNormalizers.rowGeometry 2 := by
  decide +kernel

private theorem trio_witness_check : ∀ (r : Fin 4) (j : Fin 3),
    fixedSet (fixedClass (rowCode (trioRow r) (trioWord j))) = FourNormalizers.rowFixed 2 j := by
  decide +kernel

private theorem trio_octad_card : ∀ A ∈ FourNormalizers.rowGeometry 2, A.card = 8 := by
  intro A hA
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
  exact (show ∀ j : Fin 3, (FourNormalizers.rowFixed 2 j).card = 8 by decide +kernel) j

/-- Four rows recover the trio as all fixed octads of their elements. -/
theorem trioRow_le_trio (r : Fin 4) : localGroup (trioRow r) ≤ trioGroup := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro A hA
  have hcard := trio_octad_card A hA
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
  let a := rowElement (trioRow r) (trioWord j)
  have ha : a ∈ ambient (trioRow r) := rowElement_mem _ _
  have haf : fixedPoints a = FourNormalizers.rowFixed 2 j :=
    (fixedPoints_row _ _).trans (trio_witness_check r j)
  obtain ⟨k, hk⟩ := (mem_ambient_iff (trioRow r) (g*a*g⁻¹)).mp
    ((mem_set_normalizer_iff.mp hg a).mp ha)
  have he : fixedSet (fixedClass (rowCode (trioRow r) k)) = g • FourNormalizers.rowFixed 2 j := by
    rw [← fixedPoints_row, hk, fixedPoints_conj, haf]
  rw [← he]
  apply trio_fixed_check r k
  rw [he, Finset.card_smul_finset, hcard]

private theorem repeated19_check : ∀ (j k : Fin 64),
    rowCode 19 j ≠ rowCode 19 k →
    fixedClass (rowCode 19 j) = fixedClass (rowCode 19 k) →
    fixedClass (rowCode 19 j) = 0 ∨ fixedClass (rowCode 19 j) = 3 ∨
      fixedClass (rowCode 19 j) = 10 ∨ fixedClass (rowCode 19 j) = 22 := by decide +kernel

def repeatTrioFirst : Fin 3 → Fin 64 := ![1,11,4]
def repeatTrioSecond : Fin 3 → Fin 64 := ![25,5,22]

/-- Repeated nonempty fixed sets recover exactly the three octads for row 19. -/
theorem repeated19_iff (A : Finset (Fin 24)) :
    RepeatedFixedSet 19 A ↔ A ∈ FourNormalizers.rowGeometry 2 := by
  constructor
  · rintro ⟨hne, a, ha, b, hb, hab, haf, hbf⟩
    obtain ⟨j, rfl⟩ := (mem_ambient_iff 19 a).mp ha
    obtain ⟨k, rfl⟩ := (mem_ambient_iff 19 b).mp hb
    rw [fixedPoints_row] at haf hbf
    have hclass := fixedSet_injective (haf.trans hbf.symm)
    have hcode : rowCode 19 j ≠ rowCode 19 k := fun h => hab ((rowElement_eq_iff 19 j k).mpr h)
    rcases repeated19_check j k hcode hclass with he | he | he | he
    · rw [he] at haf
      exact (Finset.not_nonempty_empty (haf.symm ▸ hne)).elim
    all_goals rw [← haf, he]; decide +kernel
  · intro hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hA
    refine ⟨?_, rowElement 19 (repeatTrioFirst j), rowElement_mem _ _,
      rowElement 19 (repeatTrioSecond j), rowElement_mem _ _, ?_, ?_, ?_⟩
    · exact (show ∀ j : Fin 3, (FourNormalizers.rowFixed 2 j).Nonempty by decide +kernel) j
    · simp only [ne_eq, rowElement_eq_iff]
      exact (show ∀ j : Fin 3, rowCode 19 (repeatTrioFirst j) ≠
        rowCode 19 (repeatTrioSecond j) by decide +kernel) j
    · rw [fixedPoints_row]
      exact (show ∀ j : Fin 3, fixedSet (fixedClass (rowCode 19 (repeatTrioFirst j))) =
        FourNormalizers.rowFixed 2 j by decide +kernel) j
    · rw [fixedPoints_row]
      exact (show ∀ j : Fin 3, fixedSet (fixedClass (rowCode 19 (repeatTrioSecond j))) =
        FourNormalizers.rowFixed 2 j by decide +kernel) j

/-- The full normalizer of row 19 preserves the same actual trio. -/
theorem row19_le_trio : localGroup 19 ≤ trioGroup := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro A hA
  exact (repeated19_iff _).mp (repeatedFixedSet_smul 19 g hg A ((repeated19_iff A).mpr hA))

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
