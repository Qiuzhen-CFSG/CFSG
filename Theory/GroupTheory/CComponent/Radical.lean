module

public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.SolvableRadical

/-!
# The radical quotient of a C-component

A proper subnormal subgroup of a C-component lies in a proper normal subgroup.
The latter is solvable by minimality of the C-component, so it lies in the
solvable radical. The radical is proper because a C-component is not solvable.
The subgroup correspondence then makes the radical quotient simple; perfectness
makes this nontrivial quotient nonabelian.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition A.3.3(1), pp. 41–42 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup

namespace Subgroup.IsCComponent
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- A C-component has proper solvable radical. -/
theorem solvableRadical_ne_top (hL : L.IsCComponent) : solvableRadical L ≠ ⊤ := by
  intro h
  apply hL.not_isSolvable
  have hs : Group.IsSolvable (solvableRadical L) := inferInstance
  rw [h] at hs
  exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup L).subtype)
    (MonoidHom.range_eq_top.mp (range_subtype ⊤))

/-- Every proper subnormal subgroup of a C-component lies in its solvable radical. -/
theorem le_solvableRadical_of_subnormal_proper (hL : L.IsCComponent) {N : Subgroup L}
    (hN : N.IsSubnormal) (hproper : N ≠ ⊤) : N ≤ solvableRadical L := by
  obtain ⟨K, hn, hNK, hK⟩ := hN.exists_normal_and_le_and_lt_top_of_ne hproper
  exact hNK.trans (le_solvableRadical K hn
    (hL.isSolvable_of_subnormal_lt_top hn.isSubnormal hK.ne))

/-- A.3.3(1): a C-component modulo its solvable radical is simple. -/
theorem isSimpleGroup_quotient_solvableRadical (hL : L.IsCComponent) : IsSimpleGroup (L ⧸ solvableRadical L) := by
  let q := QuotientGroup.mk' (solvableRadical L)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : Nontrivial (L ⧸ solvableRadical L) :=
    (QuotientGroup.nontrivial_iff).mpr hL.solvableRadical_ne_top
  refine ⟨fun K hK => ?_⟩
  let := hK
  by_cases ht : K.comap q = ⊤
  · right
    have := congrArg (Subgroup.map q) ht
    simpa only [map_comap_eq_self_of_surjective hq, map_top_of_surjective q hq] using this
  · left
    have hle := hL.le_solvableRadical_of_subnormal_proper (Subgroup.normal_comap q).isSubnormal ht
    have hker : K.comap q = solvableRadical L :=
      le_antisymm hle (by simpa [q] using (Subgroup.ker_le_comap q K))
    have := congrArg (Subgroup.map q) hker
    rw [map_comap_eq_self_of_surjective hq] at this
    simpa [q] using this

/-- A.3.3(1): the simple radical quotient of a C-component is nonabelian. -/
theorem not_isMulCommutative_quotient_solvableRadical (hL : L.IsCComponent) :
    ¬ IsMulCommutative (L ⧸ solvableRadical L) := by
  let := hL.perfect
  let := hL.isSimpleGroup_quotient_solvableRadical
  exact Group.IsPerfect.not_isMulCommutative _

/-- A.3.3(1): the radical is the greatest proper subnormal subgroup of a C-component. -/
theorem isGreatest_solvableRadical (hL : L.IsCComponent) :
    IsGreatest {N : Subgroup L | N.IsSubnormal ∧ N ≠ ⊤} (solvableRadical L) :=
  ⟨⟨(inferInstance : (solvableRadical L).Normal).isSubnormal, hL.solvableRadical_ne_top⟩,
    fun _ hN => hL.le_solvableRadical_of_subnormal_proper hN.1 hN.2⟩
end Subgroup.IsCComponent
