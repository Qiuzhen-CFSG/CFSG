module

public import Theory.SpecificGroups.PSL3Four.Collineations.OrderBound
public import Theory.GroupTheory.SimpleSubgroupSmallIndex
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect incidence actions on PG(2,4) land in the actual PSL image

The frame bound gives index at most six for the canonical PSL₃(4) subgroup
in the full incidence collineation group. Its simplicity and order 20,160
force its coset action to be trivial, so this subgroup is normal. The quotient
has order at most six and is solvable. Every perfect group's image in that
quotient is therefore trivial.

All inclusions refer to the actual determinant-one projective point action
and inverse-transpose line action. This removes the linear-image premise in
the plane-action comparison for Aschbacher–Smith F.4.8(2), printed p.278,
used by F.4.26, printed p.288. Existence of coordinates for an abstract plane
is a separate obligation.
-/

open Configuration
namespace Matrix.PSL3Four
noncomputable section
local instance : DecidableEq F := Classical.decEq _
local notation "C" => Collineation PG PG

public theorem pslCollineation_index_le_six :
    pslCollineation.range.index ≤ 6 := by
  have hb : Nat.card C ≤ 120960 := Configuration.PlaneFour.card_fullCollineation_le
  have hc : Nat.card pslCollineation.range = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective pslCollineation_injective).toEquiv, card_PSL]
  have hh := pslCollineation.range.card_mul_index
  rw [hc] at hh
  omega

public instance pslCollineation_range_normal : pslCollineation.range.Normal := by
  let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup pslCollineation.range :=
    (MonoidHom.ofInjective pslCollineation_injective).symm.isSimpleGroup
  apply pslCollineation.range.normal_of_simple_of_factorial_index_lt_card
  have h := Nat.factorial_le pslCollineation_index_le_six
  have hc : Nat.card pslCollineation.range = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective pslCollineation_injective).toEquiv, card_PSL]
  norm_num at h
  omega

public instance fullCollineation_quotient_isSolvable :
    Group.IsSolvable (C ⧸ pslCollineation.range) :=
  Group.isSolvable_of_card_le_six pslCollineation_index_le_six

public theorem perfect_hom_mem_pslCollineation {H : Type*} [Group H] [Group.IsPerfect H]
    (f : H →* C) (g : H) : f g ∈ pslCollineation.range := by
  let q := (QuotientGroup.mk' pslCollineation.range).comp f
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  have hs : Subsingleton q.range := by
    by_contra h
    let : Nontrivial q.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable q.range inferInstance
  have he : q g = 1 := congrArg Subtype.val (hs.elim (q.rangeRestrict g) 1)
  exact (QuotientGroup.eq_one_iff (f g)).mp he
end
end Matrix.PSL3Four
