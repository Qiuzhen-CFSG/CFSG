module
public import Theory.SpecificGroups.BinaryLinear.SevenFlagCore
import all Theory.SpecificGroups.BinaryLinear.SevenFlagCore

/-!
# Exact binary-four and binary-five flags with two-core quotient of order168

The actual full-Sylow flag theorem supplies a basis and cut set. The literal
quotient-cardinality calculation then leaves only the endpoint flags in
binary dimension4 and the adjacent/middle/adjacent flags in dimension5.
The small cut-set certificates are checked by the Lean kernel.

This is an internal continuation of SevenFlagCore. Its private quotient
coordinates are imported intentionally; no private name enters the public
statements and the frozen source file is unchanged.
-/

public noncomputable section
open Subgroup
open scoped Classical
namespace BinaryLinear.SevenFlagCore
open OuterCyclic InvariantNodeActions

private theorem four_exact_cuts : ∀ s : Finset (Fin 3), leviOrder s=168 →
    s={0} ∨ s={2} := by decide +kernel

private theorem five_exact_cuts : ∀ s : Finset (Fin 4), leviOrder s=168 →
    s={0,1} ∨ s={0,3} ∨ s={2,3} := by decide +kernel

/-- A full-Sylow overgroup in GL4(2) with intrinsic two-core quotient of
order168 is an endpoint flag, in a basis retaining the supplied Sylow. -/
theorem four_sylow_overgroup_of_quotient_card_168
    (S : Sylow 2 (LinearGroup 4)) (J : Subgroup (LinearGroup 4))
    (hSJ : (S : Subgroup _) ≤ J) (h168 : Nat.card (J ⧸ pCore 2 J)=168) :
    ∃ b : Basis 3, (S : Subgroup (LinearGroup 4))=cutStabilizer b Set.univ ∧
      (J=cutStabilizer b ({0} : Set (Fin 3)) ∨ J=cutStabilizer b ({2} : Set (Fin 3))) := by
  obtain ⟨b,cuts,hS,hJ⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S J hSJ
  have hc : leviOrder cuts.toFinset=168 := by
    rw [hJ,quotient_card] at h168
    exact h168
  refine ⟨b,hS,?_⟩
  rcases four_exact_cuts _ hc with hc | hc
  · have hs : cuts=({0} : Set (Fin 3)) := by
      ext i
      simpa only [Set.mem_toFinset,Finset.mem_singleton,Set.mem_singleton_iff] using
        (Iff.of_eq (congrArg (fun s : Finset (Fin 3) => i∈s) hc))
    exact Or.inl (hJ.trans (congrArg (cutStabilizer b) hs))
  · have hs : cuts=({2} : Set (Fin 3)) := by
      ext i
      simpa only [Set.mem_toFinset,Finset.mem_singleton,Set.mem_singleton_iff] using
        (Iff.of_eq (congrArg (fun s : Finset (Fin 3) => i∈s) hc))
    exact Or.inr (hJ.trans (congrArg (cutStabilizer b) hs))

/-- A full-Sylow overgroup in GL5(2) with intrinsic two-core quotient of
order168 is one of the three literal three-block flags. -/
theorem five_sylow_overgroup_of_quotient_card_168
    (S : Sylow 2 (LinearGroup 5)) (J : Subgroup (LinearGroup 5))
    (hSJ : (S : Subgroup _) ≤ J) (h168 : Nat.card (J ⧸ pCore 2 J)=168) :
    ∃ b : Basis 4, (S : Subgroup (LinearGroup 5))=cutStabilizer b Set.univ ∧
      (J=cutStabilizer b ({0,1} : Set (Fin 4)) ∨
        J=cutStabilizer b ({0,3} : Set (Fin 4)) ∨
        J=cutStabilizer b ({2,3} : Set (Fin 4))) := by
  obtain ⟨b,cuts,hS,hJ⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S J hSJ
  have hc : leviOrder cuts.toFinset=168 := by
    rw [hJ,quotient_card] at h168
    exact h168
  refine ⟨b,hS,?_⟩
  rcases five_exact_cuts _ hc with hc | hc | hc
  · have hs : cuts=({0,1} : Set (Fin 4)) := by
      ext i
      simpa only [Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] using (Iff.of_eq (congrArg (fun s : Finset (Fin 4) => i∈s) hc))
    exact Or.inl (hJ.trans (congrArg (cutStabilizer b) hs))
  · have hs : cuts=({0,3} : Set (Fin 4)) := by
      ext i
      simpa only [Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] using (Iff.of_eq (congrArg (fun s : Finset (Fin 4) => i∈s) hc))
    exact Or.inr (Or.inl (hJ.trans (congrArg (cutStabilizer b) hs)))
  · have hs : cuts=({2,3} : Set (Fin 4)) := by
      ext i
      simpa only [Set.mem_toFinset,Finset.mem_insert,Finset.mem_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] using (Iff.of_eq (congrArg (fun s : Finset (Fin 4) => i∈s) hc))
    exact Or.inr (Or.inr (hJ.trans (congrArg (cutStabilizer b) hs)))

end BinaryLinear.SevenFlagCore
