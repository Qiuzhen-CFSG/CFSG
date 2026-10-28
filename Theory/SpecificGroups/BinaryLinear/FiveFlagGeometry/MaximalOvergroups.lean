module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.SolvableFlags

/-!
# Maximal binary five-space parabolics above a solvable Sylow overgroup

Sylow-overgroup exhaustion and reconstruction of invariant subspaces show
that joins of flag stabilizers correspond to intersections of their cuts.
Thus distinct singleton-cut stabilizers are maximal and generate GL₅(2).
A solvable Sylow overgroup with three-part nine retains exactly two cuts,
so it lies in two such maximal parabolics.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
namespace BinaryLinear.FiveFlagGeometry.MaximalOvergroups

noncomputable def flagSylow (b : FiveBasis) : Sylow 2 (LinearGroup 5) :=
  (standardBasis.equiv b (Equiv.refl _)) • standardSylow

theorem flagSylow_coe (b : FiveBasis) :
    (flagSylow b : Subgroup (LinearGroup 5)) = flagStabilizer b Set.univ := by
  change (flagStabilizer standardBasis Set.univ).map
    (MulAut.conj (standardBasis.equiv b (Equiv.refl _))).toMonoidHom = _
  rw [flagStabilizer_map_conj]
  congr 1
  ext i
  simp

theorem flag_le_iff (b : FiveBasis) (s t : Set (Fin 4)) :
    flagStabilizer b s ≤ flagStabilizer b t ↔ t ⊆ s :=
  BinaryLinear.InvariantNodeActions.cutStabilizer_le_iff b s t

theorem overgroup_eq_flag (b : FiveBasis) (Q : Subgroup (LinearGroup 5))
    (h : flagStabilizer b Set.univ ≤ Q) :
    ∃ cuts : Set (Fin 4), Q = flagStabilizer b cuts := by
  obtain ⟨c, cuts, hc⟩ := isFlagParabolic_of_sylow_le (flagSylow b) Q
    ((flagSylow_coe b).symm ▸ h)
  refine ⟨cuts, hc.trans ?_⟩
  exact BinaryLinear.InvariantNodeActions.cutStabilizer_eq_of_fullFlag_le b c cuts (show flagStabilizer b Set.univ ≤ flagStabilizer c cuts from h.trans_eq hc)

theorem flag_sup (b : FiveBasis) (s t : Set (Fin 4)) :
    flagStabilizer b s ⊔ flagStabilizer b t = flagStabilizer b (s ∩ t) := by
  obtain ⟨u, hu⟩ := overgroup_eq_flag b (flagStabilizer b s ⊔ flagStabilizer b t)
    ((flag_le_iff b _ _).mpr (Set.subset_univ s) |>.trans le_sup_left)
  apply le_antisymm
  · exact sup_le ((flag_le_iff b _ _).mpr Set.inter_subset_left)
      ((flag_le_iff b _ _).mpr Set.inter_subset_right)
  · rw [hu, flag_le_iff]
    exact Set.subset_inter
      ((flag_le_iff b s u).mp (le_sup_left.trans_eq hu))
      ((flag_le_iff b t u).mp (le_sup_right.trans_eq hu))

theorem singleton_flag_isCoatom (b : FiveBasis) (i : Fin 4) :
    IsCoatom (flagStabilizer b {i}) := by
  constructor
  · intro he
    have h : flagStabilizer b ∅ ≤ flagStabilizer b {i} := by rw [he]; exact le_top
    simpa using (flag_le_iff b ∅ {i}).mp h (Set.mem_singleton i)
  · intro Q hQ
    obtain ⟨s, hs⟩ := overgroup_eq_flag b Q
      (((flag_le_iff b _ _).mpr (Set.subset_univ {i})).trans hQ.le)
    have hi : s ⊆ {i} := (flag_le_iff b _ _).mp (hQ.le.trans_eq hs)
    have he : s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj' : j = i := hi hj
      have hback : Q ≤ flagStabilizer b {i} := by
        rw [hs, flag_le_iff]
        exact Set.singleton_subset_iff.mpr (hj' ▸ hj)
      exact hQ.not_ge hback
    rw [hs, he, flagStabilizer_empty]

theorem two_maximal_flags_generate (b : FiveBasis) {i j : Fin 4} (hij : i ≠ j) :
    flagStabilizer b {i} ⊔ flagStabilizer b {j} = ⊤ := by
  rw [flag_sup]
  have he : ({i} : Set (Fin 4)) ∩ {j} = ∅ := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hki hkj
    exact hij (hki.symm.trans hkj)
  rw [he, flagStabilizer_empty]

/-- A solvable overgroup of a full Sylow with three-part nine is contained
in two distinct maximal parabolics that generate the whole group. -/
theorem solvable_overgroup_two_maximals (T : Sylow 2 (LinearGroup 5))
    (B : Subgroup (LinearGroup 5)) (hTB : (T : Subgroup _) ≤ B)
    (hsol : Group.IsSolvable B) (h3 : (Nat.card B).factorization 3 = 2) :
    ∃ (b : FiveBasis) (i j : Fin 4), i ≠ j ∧
      (T : Subgroup (LinearGroup 5)) = flagStabilizer b Set.univ ∧
      B ≤ flagStabilizer b {i} ∧ B ≤ flagStabilizer b {j} ∧
      IsCoatom (flagStabilizer b {i}) ∧ IsCoatom (flagStabilizer b {j}) ∧
      flagStabilizer b {i} ⊔ flagStabilizer b {j} = ⊤ := by
  obtain ⟨b, hb⟩ := sylow_eq_flagStabilizer T
  obtain ⟨s, hs⟩ := overgroup_eq_flag b B (hb ▸ hTB)
  obtain ⟨k, l, hkl, hn, he⟩ :=
    SmallParabolicLevi.TwoNodes.cuts_eq_compl_pair_of_solvable_three_part b s
      (hs ▸ hsol) (hs ▸ h3)
  have hex : ∃ i j : Fin 4, i ≠ j ∧ i ∉ ({k, l} : Set (Fin 4)) ∧
      j ∉ ({k, l} : Set (Fin 4)) := by
    revert hkl hn
    fin_cases k <;> fin_cases l <;> decide
  obtain ⟨i, j, hij, hi, hj⟩ := hex
  refine ⟨b, i, j, hij, hb, ?_, ?_, singleton_flag_isCoatom b i,
    singleton_flag_isCoatom b j, two_maximal_flags_generate b hij⟩
  · rw [hs, flag_le_iff, Set.singleton_subset_iff, he]
    exact hi
  · rw [hs, flag_le_iff, Set.singleton_subset_iff, he]
    exact hj
end BinaryLinear.FiveFlagGeometry.MaximalOvergroups

end
