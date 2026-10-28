module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Simple component quotients when the radical is a two-group

Subnormality carries the solvable radical into the ambient radical and
identifies the intrinsic two-core with its ambient intersection. Thus an
ambient radical equal to the two-core gives the same equality in every
subnormal subgroup. A C-component then has simple quotient by its two-core.

Source: the radical calculus in Aschbacher--Smith A.3.3(1), used in
14.6.19(2), printed p.1037.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem solvableRadical_eq_pCore_of_subnormal
    (hG : solvableRadical G = pCore 2 G)
    {K : Subgroup G} (hK : K.IsSubnormal) :
    solvableRadical K = pCore 2 K := by
  apply le_antisymm
  · rw [pCore_subnormal_eq_comap 2 hK]
    apply map_le_iff_le_comap.mp
    exact (map_solvableRadical_subtype_le_of_isSubnormal hK).trans hG.le
  · let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance

theorem IsCComponent.isSimpleGroup_quotient_twoCore_of_radical_eq
    {K : Subgroup G} (hK : K.IsCComponent)
    (hG : solvableRadical G = pCore 2 G) :
    IsSimpleGroup (K ⧸ pCore 2 K) := by
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact (QuotientGroup.quotientMulEquivOfEq
    (solvableRadical_eq_pCore_of_subnormal hG hK.subnormal)).symm.isSimpleGroup

end Subgroup
