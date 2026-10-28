module
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.WordModels
import Mathlib.Tactic
/-!
# Recovering the invariant blocks from square-one elements

Conjugation preserves the relation of being connected by a square-one element.
In the natural and diagonal models, its nontrivial classes occupy exactly the
four-point block. In the paired model these classes are exactly the three pairs
and the singleton. This gives structural upper bounds for the normalizers.
The relation is calculated on the twelve proved words, rather than on S₇.

Source: the action calculation used in Aschbacher–Smith 15.3.43, p.1140.
-/

@[expose] public section
open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals

/-- Points related by a square-one element of the given group. -/
def involutionRelated (H : Subgroup Perm7) (a b : Fin 7) : Prop :=
  ∃ h ∈ H, h ^ 2 = 1 ∧ h a = b

private theorem related_conj (H : Subgroup Perm7) (g : Perm7)
    (hg : g ∈ normalizer (H : Set Perm7)) {a b : Fin 7}
    (hab : involutionRelated H a b) : involutionRelated H (g a) (g b) := by
  obtain ⟨h, hh, h2, hab⟩ := hab
  refine ⟨g * h * g⁻¹, (hg h).mp hh, ?_, ?_⟩
  · simp [conj_pow, h2]
  · simp [Perm.mul_apply, hab]

theorem involutionRelated_normalizer_iff (H : Subgroup Perm7) (g : Perm7)
    (hg : g ∈ normalizer (H : Set Perm7)) (a b : Fin 7) :
    involutionRelated H a b ↔ involutionRelated H (g a) (g b) := by
  constructor
  · exact related_conj H g hg
  · intro h
    simpa using related_conj H g⁻¹ ((normalizer _).inv_mem hg) h

private theorem related_range {ι : Type*} (H : Subgroup Perm7) (w : ι → Perm7)
    (hw : ∀ h, h ∈ H ↔ ∃ i, w i = h) (a b : Fin 7) :
    involutionRelated H a b ↔ ∃ i, w i ^ 2 = 1 ∧ w i a = b := by
  constructor
  · rintro ⟨h, hh, h2, hab⟩
    obtain ⟨i, rfl⟩ := (hw h).mp hh
    exact ⟨i, h2, hab⟩
  · rintro ⟨i, h2, hab⟩
    exact ⟨w i, (hw _).mpr ⟨i, rfl⟩, h2, hab⟩

private theorem involution_moved_natural (a : Fin 7) :
    (∃ b, involutionRelated naturalFour a b ∧ b ≠ a) ↔ a ∈ fourPointSet := by
  rw [naturalFour_eq_explicit]
  simp only [related_range naturalExplicit (words12 naturalThree fourFlip) (fun _ => Iff.rfl)]
  change (∃ b, (∃ i : Fin 12, (words12 naturalThree fourFlip i) ^ 2 = 1 ∧
    words12 naturalThree fourFlip i a = b) ∧ b ≠ a) ↔ a.val < 4
  decide +revert +kernel

private theorem involution_moved_diagonal (a : Fin 7) :
    (∃ b, involutionRelated diagonalFour a b ∧ b ≠ a) ↔ a ∈ fourPointSet := by
  rw [diagonalFour_eq_explicit]
  simp only [related_range diagonalExplicit (words12 diagonalThree fourFlip) (fun _ => Iff.rfl)]
  change (∃ b, (∃ i : Fin 12, (words12 diagonalThree fourFlip i) ^ 2 = 1 ∧
    words12 diagonalThree fourFlip i a = b) ∧ b ≠ a) ↔ a.val < 4
  decide +revert +kernel

private theorem normalizer_le_fourPoint_of_moved (H : Subgroup Perm7)
    (hH : ∀ a, (∃ b, involutionRelated H a b ∧ b ≠ a) ↔ a ∈ fourPointSet) :
    normalizer (H : Set Perm7) ≤ fourPointSetwiseStabilizer := by
  intro g hg a
  constructor
  · intro ha
    obtain ⟨b, hab, hba⟩ := (hH a).mpr ha
    exact (hH (g a)).mp ⟨g b, related_conj H g hg hab,
      fun he => hba (g.injective he)⟩
  · intro ha
    obtain ⟨b, hab, hba⟩ := (hH (g a)).mpr ha
    apply (hH a).mp
    refine ⟨g⁻¹ b, ?_, ?_⟩
    · simpa using related_conj H g⁻¹ ((normalizer _).inv_mem hg) hab
    · intro he
      apply hba
      simpa using congrArg g he

theorem natural_normalizer_le_fourPoint :
    normalizer (naturalFour : Set Perm7) ≤ fourPointSetwiseStabilizer :=
  normalizer_le_fourPoint_of_moved naturalFour involution_moved_natural

theorem diagonal_normalizer_le_fourPoint :
    normalizer (diagonalFour : Set Perm7) ≤ fourPointSetwiseStabilizer :=
  normalizer_le_fourPoint_of_moved diagonalFour involution_moved_diagonal

private theorem involutionRelated_paired (a b : Fin 7) :
    involutionRelated pairedFour a b ↔ b = a ∨ b = pairing a := by
  rw [pairedFour_eq_explicit]
  rw [related_range pairedExplicit (words12 pairedThree fourFlip) (fun _ => Iff.rfl)]
  decide +revert +kernel

theorem paired_normalizer_le_centralizer :
    normalizer (pairedFour : Set Perm7) ≤ centralizer ({pairing} : Set Perm7) := by
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  apply Equiv.ext
  intro a
  change g (pairing a) = pairing (g a)
  symm
  have hc (a b : Fin 7) :
      (b = a ∨ b = pairing a) ↔ (g b = g a ∨ g b = pairing (g a)) := by
    simpa only [← involutionRelated_paired] using
      involutionRelated_normalizer_iff pairedFour g hg a b
  rcases (hc a (pairing a)).mp (Or.inr rfl) with he | he
  · have hfix : pairing a = a := g.injective he
    have h := (hc a (g⁻¹ (pairing (g a)))).mpr (by simp)
    rw [hfix, or_self] at h
    have hh := congrArg g h
    simpa [hfix] using hh
  · exact he.symm

end AlternatingSeven.ThreeResidualLocals
