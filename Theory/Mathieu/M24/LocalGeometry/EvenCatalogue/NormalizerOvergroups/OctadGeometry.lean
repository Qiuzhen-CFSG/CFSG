module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.Enumeration
/-!
# Fifteen ambient normalizers preserve a native octad

Fourteen rows distinguish the octad numbered 456 by point-orbit size. In the
remaining row, 17, it is the unique nonempty fixed set shared by two distinct
elements. Conjugation by the full ambient normalizer preserves both invariants.
No pointwise-kernel identification or restriction to a Sylow normalizer is used.

Source: GLS3 Table 5.3e; Aschbacher--Smith 15.3.41--42, printed p.1138.
-/
@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
open Subgroup
open scoped Pointwise
set_option maxRecDepth 100000

/-- The point orbit, computed from the exhaustive native row enumeration. -/
def orbitPoints (i : Fin 22) (x : Fin 24) : Finset (Fin 24) :=
  Finset.univ.image (fun j : Fin 64 => point (rowCode i j) x)

theorem mem_orbitPoints_iff (i : Fin 22) (x y : Fin 24) :
    y ∈ orbitPoints i x ↔ ∃ a ∈ ambient i, a.val x = y := by
  constructor
  · intro hy
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
    exact ⟨rowElement i j, rowElement_mem i j, (rowElement_apply i j x).trans hj⟩
  · rintro ⟨a, ha, hxy⟩
    obtain ⟨j, rfl⟩ := (mem_ambient_iff i a).mp ha
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, (rowElement_apply i j x).symm.trans hxy⟩

theorem orbitPoints_image (i : Fin 22) (g : M24) (hg : g ∈ localGroup i) (x : Fin 24) :
    (orbitPoints i x).image g.val = orbitPoints i (g.val x) := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨a, ha, rfl⟩ := (mem_orbitPoints_iff i x z).mp hz
    apply (mem_orbitPoints_iff i (g.val x) _).mpr
    refine ⟨g * a * g⁻¹, (mem_set_normalizer_iff.mp hg a).mp ha, ?_⟩
    change g.val (a.val (g.val.symm (g.val x))) = _
    rw [g.val.symm_apply_apply]
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := (mem_orbitPoints_iff i (g.val x) y).mp hy
    have hi := (localGroup i).inv_mem hg
    refine Finset.mem_image.mpr ⟨(g⁻¹ * a * g).val x, ?_, ?_⟩
    · exact (mem_orbitPoints_iff i x _).mpr
        ⟨g⁻¹ * a * g, by simpa using (mem_set_normalizer_iff.mp hi a).mp ha, rfl⟩
    · change g.val (g.val.symm (a.val (g.val x))) = _
      exact g.val.apply_symm_apply _

theorem orbit_card_invariant (i : Fin 22) (g : M24) (hg : g ∈ localGroup i) (x : Fin 24) :
    (orbitPoints i (g.val x)).card = (orbitPoints i x).card := by
  rw [← orbitPoints_image i g hg x]
  exact Finset.card_image_of_injective _ g.val.injective

noncomputable def commonOctad : Octad := ⟨m24BlockAt 456,
  Finset.mem_image.mpr ⟨456, Finset.mem_univ _, rfl⟩⟩

def octadRow : Fin 14 → Fin 22 := ![0,1,2,4,5,6,8,9,10,12,14,15,16,18]
def octadOrbitSize : Fin 14 → ℕ := ![1,1,2,1,2,2,4,4,1,2,2,4,8,4]

private theorem orbit_octad_check : ∀ (r : Fin 14) (x : Fin 24),
    (orbitPoints (octadRow r) x).card = octadOrbitSize r ↔ x ∈ commonOctad.val := by
  intro r
  fin_cases r <;> decide +kernel

/-- Orbit lengths distinguish the actual octad in fourteen catalogue rows. -/
theorem octadRow_le_octad (r : Fin 14) : localGroup (octadRow r) ≤ octadStabilizer commonOctad := by
  intro g hg
  apply MulAction.mem_stabilizer_finset.mpr
  intro x
  change g.val x ∈ commonOctad.val ↔ x ∈ commonOctad.val
  rw [← orbit_octad_check, ← orbit_octad_check, orbit_card_invariant _ g hg]

theorem fixedPoints_conj (g a : M24) : fixedPoints (g * a * g⁻¹) = g • fixedPoints a := by
  ext x
  rw [← Finset.inv_smul_mem_iff]
  simp only [fixedPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  change g.val (a.val (g.val.symm x)) = x ↔ a.val (g.val.symm x) = g.val.symm x
  exact g.val.eq_symm_apply.symm

/-- A nonempty fixed set shared by two different elements of the subgroup. -/
def RepeatedFixedSet (i : Fin 22) (A : Finset (Fin 24)) : Prop :=
  A.Nonempty ∧ ∃ a ∈ ambient i, ∃ b ∈ ambient i,
    a ≠ b ∧ fixedPoints a = A ∧ fixedPoints b = A

theorem repeatedFixedSet_smul (i : Fin 22) (g : M24) (hg : g ∈ localGroup i)
    (A : Finset (Fin 24)) (hA : RepeatedFixedSet i A) : RepeatedFixedSet i (g • A) := by
  obtain ⟨hne, a, ha, b, hb, hab, haf, hbf⟩ := hA
  refine ⟨?_, g*a*g⁻¹, (mem_set_normalizer_iff.mp hg a).mp ha,
    g*b*g⁻¹, (mem_set_normalizer_iff.mp hg b).mp hb, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨g • x, Finset.smul_mem_smul_finset hx⟩
  · exact fun he => hab ((MulAut.conj g).injective he)
  · rw [fixedPoints_conj, haf]
  · rw [fixedPoints_conj, hbf]

private theorem repeated17_check : ∀ (j k : Fin 64),
    rowCode 17 j ≠ rowCode 17 k →
    fixedClass (rowCode 17 j) = fixedClass (rowCode 17 k) →
    fixedClass (rowCode 17 j) = 0 ∨ fixedClass (rowCode 17 j) = 3 := by decide +kernel

theorem repeated17_iff (A : Finset (Fin 24)) : RepeatedFixedSet 17 A ↔ A = commonOctad.val := by
  constructor
  · rintro ⟨hne, a, ha, b, hb, hab, haf, hbf⟩
    obtain ⟨j, rfl⟩ := (mem_ambient_iff 17 a).mp ha
    obtain ⟨k, rfl⟩ := (mem_ambient_iff 17 b).mp hb
    rw [fixedPoints_row] at haf hbf
    have hclass := fixedSet_injective (haf.trans hbf.symm)
    have hcode : rowCode 17 j ≠ rowCode 17 k := fun h => hab ((rowElement_eq_iff 17 j k).mpr h)
    rcases repeated17_check j k hcode hclass with he | he
    · rw [he] at haf
      exact (Finset.not_nonempty_empty (haf.symm ▸ hne)).elim
    · rw [he] at haf
      exact haf.symm.trans (by decide +kernel)
  · rintro rfl
    refine ⟨by decide +kernel, rowElement 17 11, rowElement_mem 17 11,
      rowElement 17 5, rowElement_mem 17 5, ?_, ?_, ?_⟩
    · simp only [ne_eq, rowElement_eq_iff]; decide +kernel
    · rw [fixedPoints_row]; decide +kernel
    · rw [fixedPoints_row]; decide +kernel

/-- The exceptional equal-orbit row preserves its uniquely repeated nonempty fixed set. -/
theorem row17_le_octad : localGroup 17 ≤ octadStabilizer commonOctad := by
  intro g hg
  change g • commonOctad.val = commonOctad.val
  exact (repeated17_iff _).mp (repeatedFixedSet_smul 17 g hg _ ((repeated17_iff _).mpr rfl))

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.NormalizerOvergroupsProof
