module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.QuotientInvolutions.SylowFusion.Data
import Mathlib.Tactic.FinCases
/-!
# Exhaustive coverage of the fixed candidate by short words

Each transition of the four fixed generators on the 1024-word table is
checked in the kernel. Since the generators are self-inverse, induction on
words proves coverage of their subgroup closure. This argument neither needs
nor asserts that the candidate is Sylow, or that its order is 1024.

Source: the fixed candidate in `SylowData` and the breadth-first table `Data`.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
public section
namespace Janko4.Simplicity.Max1Fusion.QuotientInvolutions.SylowFusionCertificate
open Cardinality.QuotientCount.Image Theory.GroupTheory

private theorem stepCheck0 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (0, r) : Equiv.Perm (Fin 24)) =
      (element (step a (0, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck1 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (1, r) : Equiv.Perm (Fin 24)) =
      (element (step a (1, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck2 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (2, r) : Equiv.Perm (Fin 24)) =
      (element (step a (2, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck3 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (3, r) : Equiv.Perm (Fin 24)) =
      (element (step a (3, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck4 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (4, r) : Equiv.Perm (Fin 24)) =
      (element (step a (4, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck5 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (5, r) : Equiv.Perm (Fin 24)) =
      (element (step a (5, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck6 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (6, r) : Equiv.Perm (Fin 24)) =
      (element (step a (6, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck7 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (7, r) : Equiv.Perm (Fin 24)) =
      (element (step a (7, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck8 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (8, r) : Equiv.Perm (Fin 24)) =
      (element (step a (8, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck9 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (9, r) : Equiv.Perm (Fin 24)) =
      (element (step a (9, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck10 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (10, r) : Equiv.Perm (Fin 24)) =
      (element (step a (10, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck11 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (11, r) : Equiv.Perm (Fin 24)) =
      (element (step a (11, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck12 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (12, r) : Equiv.Perm (Fin 24)) =
      (element (step a (12, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck13 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (13, r) : Equiv.Perm (Fin 24)) =
      (element (step a (13, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck14 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (14, r) : Equiv.Perm (Fin 24)) =
      (element (step a (14, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck15 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (15, r) : Equiv.Perm (Fin 24)) =
      (element (step a (15, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck16 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (16, r) : Equiv.Perm (Fin 24)) =
      (element (step a (16, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck17 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (17, r) : Equiv.Perm (Fin 24)) =
      (element (step a (17, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck18 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (18, r) : Equiv.Perm (Fin 24)) =
      (element (step a (18, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck19 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (19, r) : Equiv.Perm (Fin 24)) =
      (element (step a (19, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck20 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (20, r) : Equiv.Perm (Fin 24)) =
      (element (step a (20, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck21 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (21, r) : Equiv.Perm (Fin 24)) =
      (element (step a (21, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck22 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (22, r) : Equiv.Perm (Fin 24)) =
      (element (step a (22, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck23 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (23, r) : Equiv.Perm (Fin 24)) =
      (element (step a (23, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck24 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (24, r) : Equiv.Perm (Fin 24)) =
      (element (step a (24, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck25 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (25, r) : Equiv.Perm (Fin 24)) =
      (element (step a (25, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck26 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (26, r) : Equiv.Perm (Fin 24)) =
      (element (step a (26, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck27 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (27, r) : Equiv.Perm (Fin 24)) =
      (element (step a (27, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck28 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (28, r) : Equiv.Perm (Fin 24)) =
      (element (step a (28, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck29 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (29, r) : Equiv.Perm (Fin 24)) =
      (element (step a (29, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck30 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (30, r) : Equiv.Perm (Fin 24)) =
      (element (step a (30, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

private theorem stepCheck31 : ∀ (a : Fin 4) (r : Fin 32),
    (sylowGenerator a : Equiv.Perm (Fin 24)) * (element (31, r) : Equiv.Perm (Fin 24)) =
      (element (step a (31, r)) : Equiv.Perm (Fin 24)) := by
  decide +kernel

theorem step_checked (a : Fin 4) (r : Index) :
    sylowGenerator a * element r = element (step a r) := by
  apply Subtype.ext
  rcases r with ⟨b, r⟩
  fin_cases b
  · exact stepCheck0 a r
  · exact stepCheck1 a r
  · exact stepCheck2 a r
  · exact stepCheck3 a r
  · exact stepCheck4 a r
  · exact stepCheck5 a r
  · exact stepCheck6 a r
  · exact stepCheck7 a r
  · exact stepCheck8 a r
  · exact stepCheck9 a r
  · exact stepCheck10 a r
  · exact stepCheck11 a r
  · exact stepCheck12 a r
  · exact stepCheck13 a r
  · exact stepCheck14 a r
  · exact stepCheck15 a r
  · exact stepCheck16 a r
  · exact stepCheck17 a r
  · exact stepCheck18 a r
  · exact stepCheck19 a r
  · exact stepCheck20 a r
  · exact stepCheck21 a r
  · exact stepCheck22 a r
  · exact stepCheck23 a r
  · exact stepCheck24 a r
  · exact stepCheck25 a r
  · exact stepCheck26 a r
  · exact stepCheck27 a r
  · exact stepCheck28 a r
  · exact stepCheck29 a r
  · exact stepCheck30 a r
  · exact stepCheck31 a r

theorem generator_inv (a : Fin 4) : sylowGenerator a = (sylowGenerator a)⁻¹ := by
  apply Subtype.ext
  have h : ∀ a : Fin 4, (sylowGenerator a : Equiv.Perm (Fin 24)) =
      (sylowGenerator a : Equiv.Perm (Fin 24))⁻¹ := by decide +kernel
  exact h a

theorem candidate_covered (w : StarGroup) (hw : w ∈ sylowCandidate) :
    ∃ r : Index, w = element r := by
  have hle : sylowCandidate ≤ wordSubgroup sylowGenerator id generator_inv := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨[a], by simp [evalWord]⟩
  have hcover : ∀ v : List (Fin 4), ∃ r : Index,
      evalWord sylowGenerator v = element r := by
    intro v
    induction v with
    | nil => exact ⟨(0, 0), rfl⟩
    | cons a v ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨step a r, ?_⟩
      change sylowGenerator a * evalWord sylowGenerator v = _
      rw [hr, step_checked]
  obtain ⟨v, hv⟩ := hle hw
  obtain ⟨r, hr⟩ := hcover v
  exact ⟨r, hv.symm.trans hr⟩
end Janko4.Simplicity.Max1Fusion.QuotientInvolutions.SylowFusionCertificate
