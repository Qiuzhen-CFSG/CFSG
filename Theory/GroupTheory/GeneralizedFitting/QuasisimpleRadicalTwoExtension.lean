module

public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# Radical structure of a quasisimple two-extension

For a normal quasisimple subgroup D with two-group center and two-group
quotient G/D, the solvable radical of G is a two-group. Its intersection
with D lies in Z(D), so the restricted map to G/D has two-group kernel
and image. The radical quotient of D is its simple central quotient.
No splitting or specified outer action is needed.

Source: standard component calculus, Aschbacher--Smith A.3.3, pp.42--43;
the centralizer application is E.1.2(E2), printed p.210.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The full radical is a two-group, including nonsplit two-extensions. -/
theorem radical_isTwoGroup_of_quasisimple_two_quotient (D : Subgroup G) [D.Normal] [IsQuasisimple D]
    (hz : IsPGroup 2 (center D)) (hq : IsPGroup 2 (G ⧸ D)) :
    IsPGroup 2 (solvableRadical G) := by
  let R := solvableRadical G
  let f := (QuotientGroup.mk' D).comp R.subtype
  let j : f.ker →* center D :=
    { toFun := fun x => ⟨⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩,
        IsQuasisimple.solvableRadical_le_center (by
          rw [← radical_subgroupOf_normal D]
          exact x.val.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) h))
  have hk := hz.of_injective j hj
  exact ((hq.to_subgroup ⊤).comap_of_ker_isPGroup f hk).of_equiv
    ((MulEquiv.subgroupCongr (Subgroup.comap_top f)).trans topEquiv)

/-- Factoring out the radical of a quasisimple group gives its simple central quotient. -/
theorem quasisimple_radicalQuotient_isSimple (D : Subgroup G) [IsQuasisimple D] :
    IsSimpleGroup (D ⧸ solvableRadical D) := by
  let : Group.IsSolvable (center D) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hr : solvableRadical D = center D := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical (center D) inferInstance inferInstance)
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  exact (QuotientGroup.quotientMulEquivOfEq hr).isSimpleGroup

end Theory.GroupTheory
