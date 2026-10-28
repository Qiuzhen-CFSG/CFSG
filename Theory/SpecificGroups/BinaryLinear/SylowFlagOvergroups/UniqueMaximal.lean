module
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers
public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.Order.UniqueMaximalOver
public import Theory.GroupTheory.SolvableMutualCommutator
public import Theory.GroupTheory.UniqueMaximalQuotient

/-!
# Minimal Sylow overgroups in binary linear groups

Unique maximality above a full Sylow two-subgroup forces deletion of just
one flag cut. This gives index three, hence solvability by its action on three cosets. The same conclusion lifts through the literal two-group kernel.

The terminal natural-module application is in Chapter 12's
TerminalComponentProperLinear. Source: Aschbacher–Smith, 12.2.7,
printed pp.797–798, using the binary flag geometry of A.3.12.
-/

public section
open Subgroup
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions

theorem covBy_of_uniqueMaximal {m : ℕ} (S : Sylow 2 (LinearGroup (m+1)))
    (P : Subgroup (LinearGroup (m+1)))
    (h : Order.HasUniqueMaximalOver (S : Subgroup _) P) :
    (S : Subgroup _) ⋖ P := by
  classical
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1)))
    DFunLike.coe_injective
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨s,hs⟩ := overgroup_eq_cutStabilizer S b hb P h.1.le
  obtain ⟨M,hM,_⟩ := h.2
  obtain ⟨d,hd⟩ := overgroup_eq_cutStabilizer S b hb M hM.1
  have hsd : s ⊆ d := (cutStabilizer_le_iff b _ _).mp (hd.symm.le.trans hM.2.le |>.trans_eq hs)
  have hds : ¬ d ⊆ s := by
    intro hh
    apply hM.2.ne
    rw [hd,hs,Set.Subset.antisymm hh hsd]
  obtain ⟨i,hid,his⟩ := Set.not_subset.mp hds
  have hall : s = ({i} : Set (Fin m))ᶜ := by
    refine Set.Subset.antisymm ?_ ?_
    · intro j hj hji
      exact his ((Set.mem_singleton_iff.mp hji) ▸ hj)
    · intro j hji
      by_contra hjs
      let Q := cutStabilizer b (s ∪ {j})
      have hSQ : (S : Subgroup _) ≤ Q := by
        rw [hb]
        exact (cutStabilizer_le_iff b _ _).mpr (Set.subset_univ _)
      have hQP : Q < P := by
        rw [hs]
        refine lt_iff_le_not_ge.mpr ⟨(cutStabilizer_le_iff b _ _).mpr Set.subset_union_left,?_⟩
        intro hh
        exact hjs ((cutStabilizer_le_iff b _ _).mp hh (Set.mem_union_right _ (Set.mem_singleton j)))
      have hQM := h.le_maximal hM hSQ hQP
      have hsub : d ⊆ s ∪ {j} := (cutStabilizer_le_iff b _ _).mp (hQM.trans_eq hd)
      rcases hsub hid with hi | hi
      · exact his hi
      · exact hji (Set.mem_singleton_iff.mp hi).symm
  rw [hs,hall]
  exact fullFlag_covBy_minimalParabolic S b hb i

theorem solvable_of_uniqueMaximal {m : ℕ} (S : Sylow 2 (LinearGroup (m+1)))
    (P : Subgroup (LinearGroup (m+1)))
    (h : Order.HasUniqueMaximalOver (S : Subgroup _) P) : Group.IsSolvable P := by
  classical
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1)))
    DFunLike.coe_injective
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨i,hi⟩ := (fullFlag_covBy_iff S b hb P).mp (covBy_of_uniqueMaximal S P h)
  have hindex : (S : Subgroup _).relIndex P = 3 := by
    rw [hi,hb,CubicSylowGeneration.minimalParabolic_index]
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  exact (S : Subgroup _).isSolvable_of_relIndex_le_four P (by omega)

theorem solvable_of_two_kernel_uniqueMaximal {m : ℕ}
    {G : Type*} [Group G] [Finite G] (f : G →* LinearGroup (m+1))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    (h : Order.HasUniqueMaximalOver ((S : Subgroup G).subgroupOf P) ⊤) :
    Group.IsSolvable P := by
  let : Finite (LinearGroup (m+1)) := Finite.of_surjective f hf
  let a := f.subgroupMap P
  have hka : IsPGroup 2 a.ker := by
    change IsPGroup 2 (f.subgroupMap P).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hm := hasUniqueMaximalOver_map_of_surjective a (f.subgroupMap_surjective P)
    (hka.le_sylow_of_normal (S.subtype hSP)) h
  have ha := hasUniqueMaximalOver_map_subtype hm
  have he : (((S : Subgroup G).subgroupOf P).map a).map (P.map f).subtype =
      (S : Subgroup G).map f := by
    rw [map_map]
    change ((S : Subgroup G).subgroupOf P).map (f.comp P.subtype) = _
    rw [← map_map,map_subgroupOf_eq_of_le hSP]
  change Order.HasUniqueMaximalOver
    ((((S : Subgroup G).subgroupOf P).map a).map (P.map f).subtype) (P.map f) at ha
  rw [he] at ha
  let : Group.IsSolvable (P.map f) := solvable_of_uniqueMaximal (S.mapSurjective hf) _ ha
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  exact (Group.isSolvable_map_iff_of_solvable_ker f P).mp inferInstance
end BinaryLinear.SylowFlagOvergroups
