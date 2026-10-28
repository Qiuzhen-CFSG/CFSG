module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.GroupTheory.SubgroupCoverTransport

/-!
# Minimal binary parabolics as Sylow covers

The exhaustion of Sylow overgroups by partial flags identifies their minimal
members with deletion of one cut from the same full flag. This extends the
five-dimensional cover argument to arbitrary binary dimension, retaining the
specified Sylow subgroup and basis. Subgroup correspondence can therefore
transport these covers through the actual action kernel.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104; the cover argument
also appears in `FiveFlagGeometry/RankOneExchange` for 10.2.9.
-/

public section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions
variable {m : ℕ}

/-- Every Sylow overgroup is a partial stabilizer in the same marked flag. -/
theorem overgroup_eq_cutStabilizer (S : Sylow 2 (LinearGroup (m + 1)))
    (b : Basis m) (hb : (S : Subgroup _) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup (m + 1))) (hSP : (S : Subgroup _) ≤ P) :
    ∃ cuts : Set (Fin m), P = cutStabilizer b cuts := by
  obtain ⟨c,cuts,_,hc⟩ := exists_flag_of_sylow_le S P hSP
  exact ⟨cuts,hc.trans (cutStabilizer_eq_of_fullFlag_le b c cuts
    (hb ▸ hSP.trans_eq hc))⟩

/-- A minimal flag parabolic is a cover of the specified Sylow subgroup. -/
theorem fullFlag_covBy_minimalParabolic (S : Sylow 2 (LinearGroup (m + 1)))
    (b : Basis m) (hb : (S : Subgroup _) = cutStabilizer b Set.univ) (i : Fin m) :
    (S : Subgroup _) ⋖ minimalParabolic b i := by
  have hlt : (S : Subgroup _) < minimalParabolic b i := by
    rw [hb]
    refine lt_iff_le_not_ge.mpr ⟨(cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _),?_⟩
    intro h
    exact ((cutStabilizer_le_iff b _ _).mp h (Set.mem_univ i)) (Set.mem_singleton i)
  refine covBy_of_eq_or_eq hlt ?_
  intro Q hBQ hQP
  obtain ⟨s,hs⟩ := overgroup_eq_cutStabilizer S b hb Q hBQ
  have hslo : {i}ᶜ ⊆ s := (cutStabilizer_le_iff b _ _).mp (hs.symm.le.trans hQP)
  by_cases hi : i ∈ s
  · apply Or.inl
    rw [hb]
    have hall : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro j
      by_cases hj : j = i
      · exact hj ▸ hi
      · exact hslo hj
    exact hs.trans (congrArg (cutStabilizer b) hall)
  · apply Or.inr
    have he : s = {i}ᶜ := Set.Subset.antisymm (fun j hj hji => hi (hji ▸ hj)) hslo
    exact hs.trans (congrArg (cutStabilizer b) he)

/-- Covers of the specified Sylow are exactly the marked minimal parabolics. -/
theorem fullFlag_covBy_iff (S : Sylow 2 (LinearGroup (m + 1)))
    (b : Basis m) (hb : (S : Subgroup _) = cutStabilizer b Set.univ)
    (P : Subgroup (LinearGroup (m + 1))) :
    (S : Subgroup _) ⋖ P ↔ ∃ i : Fin m, P = minimalParabolic b i := by
  constructor
  · intro hP
    obtain ⟨s,hs⟩ := overgroup_eq_cutStabilizer S b hb P hP.le
    have hproper : ¬ Set.univ ⊆ s := by
      intro h
      exact hP.ne (hs.trans ((congrArg (cutStabilizer b)
        (Set.Subset.antisymm (Set.subset_univ _) h)).trans hb.symm)).symm
    obtain ⟨i,_,hi⟩ := Set.not_subset.mp hproper
    have hnode : minimalParabolic b i ≤ P := by
      rw [hs]
      exact (cutStabilizer_le_iff b _ _).mpr (fun j hj hji => hi (hji ▸ hj))
    have he := (covBy_iff_lt_and_eq_or_eq.mp hP).2 _
      (fullFlag_covBy_minimalParabolic S b hb i).le hnode
    exact ⟨i,(he.resolve_left (fullFlag_covBy_minimalParabolic S b hb i).ne.symm).symm⟩
  · rintro ⟨i,rfl⟩
    exact fullFlag_covBy_minimalParabolic S b hb i
end BinaryLinear.SylowFlagOvergroups
