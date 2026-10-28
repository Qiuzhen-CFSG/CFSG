module

public import Theory.Mathieu.M22.Properties.LocalSubgroups
public import Theory.Mathieu.M22.Properties.Design

/-!
# The marked pair and hexad partition in M₂₂

The first local subgroup fixes the pair {1,2}. The second fixes a partition
of the standard hexad into three pairs, one of which is {1,2}. The same
configurations define subgroups in the full design automorphism group.
Restriction to its even subgroup recovers the original M₂₂ subgroups.

These definitions specify the geometry in Aschbacher–Smith E.4.3(2),
printed pp. 241–242. Quotient identifications, the Sylow property of the
intersection, and generation are separate mathematical obligations.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22ValueBound.Concrete
open Subgroup
open scoped Pointwise

/-- The partition of the standard hexad used for the rank-one parabolic. -/
def hexadPartition : Finset (Finset (Fin 22)) :=
  {{1, 2}, {3, 10}, {18, 20}}

theorem hexadPartition_card : hexadPartition.card = 3 := by
  decide +kernel

theorem hexadPartition_union : hexadPartition.biUnion id = m22Hexad123 := by
  decide +kernel

theorem pair_mem_hexadPartition : m22Pair12 ∈ hexadPartition := by
  decide +kernel

/-- The normal M₂₂ subgroup of the concrete full automorphism group. -/
noncomputable abbrev inner : Subgroup m22DesignAut := M22.subgroupOf m22DesignAut

instance inner_normal : inner.Normal := M22_normal_in_m22DesignAut

/-- The first and second subgroups inside M₂₂ itself. -/
noncomputable abbrev first : Subgroup M22 := m22PairStabilizer

noncomputable def second : Subgroup M22 :=
  MulAction.stabilizer M22 hexadPartition

/-- The same two stabilizers in the full design automorphism group. -/
noncomputable def outerFirst : Subgroup m22DesignAut :=
  MulAction.stabilizer m22DesignAut m22Pair12

noncomputable def outerSecond : Subgroup m22DesignAut :=
  MulAction.stabilizer m22DesignAut hexadPartition

/-- Inclusion retains the actual degree-22 permutations. -/
noncomputable def inclusion : M22 →* m22DesignAut := Subgroup.inclusion M22_le_hexadDesignAut

theorem inclusion_injective : Function.Injective inclusion :=
  Subgroup.inclusion_injective _

theorem inclusion_range : inclusion.range = inner := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact h.property
  · intro hg
    exact ⟨⟨g.val, hg⟩, Subtype.ext rfl⟩

theorem comap_outerFirst : outerFirst.comap inclusion = first := rfl

theorem comap_outerSecond : outerSecond.comap inclusion = second := rfl

theorem map_first : first.map inclusion = outerFirst ⊓ inner := by
  rw [← comap_outerFirst, Subgroup.map_comap_eq, inclusion_range, inf_comm]

theorem map_second : second.map inclusion = outerSecond ⊓ inner := by
  rw [← comap_outerSecond, Subgroup.map_comap_eq, inclusion_range, inf_comm]

/-- The intrinsic first inner intersection is exactly the M₂₂ pair stabilizer. -/
noncomputable def firstInnerEquiv : (outerFirst ⊓ inner : Subgroup m22DesignAut) ≃* first :=
  (MulEquiv.subgroupCongr map_first.symm).trans
    (first.equivMapOfInjective inclusion inclusion_injective).symm

/-- The intrinsic second inner intersection is exactly the M₂₂ partition stabilizer. -/
noncomputable def secondInnerEquiv : (outerSecond ⊓ inner : Subgroup m22DesignAut) ≃* second :=
  (MulEquiv.subgroupCongr map_second.symm).trans
    (second.equivMapOfInjective inclusion inclusion_injective).symm

end Sporadic.Mathieu.M22ValueBound.Concrete
