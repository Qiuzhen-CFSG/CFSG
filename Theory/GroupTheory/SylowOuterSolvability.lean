module

public import Theory.GroupTheory.SylowOuterAutomorphisms
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Solvable outer groups from Sylow restrictions

The stabilizer of an actual Sylow subgroup in Aut(G) maps onto Out(G), by
Sylow conjugacy. Its restriction homomorphism into Aut(P) has kernel in the
pointwise fixer of P. Thus solvability of Aut(P) and of that fixer implies
solvability of the full outer group. No innerness hypothesis on the fixer
or automorphism-realization theorem is used.

This is the restriction-and-Frattini argument used with the finite-simple
S₂ theorem in the A.3.9 source application; the local Aut(P) input remains
explicit in this general group-theoretic result.
-/

namespace MulAut
open Subgroup
open scoped Pointwise

/-- Solvable restriction and pointwise-fixer groups make the full outer
automorphism group solvable, by literal Sylow conjugacy. -/
public theorem outer_isSolvable_of_sylow_aut
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [Group.IsSolvable (MulAut P)]
    [Group.IsSolvable (fixingSubgroup (MulAut G) (P : Set G))] :
    Group.IsSolvable (Outer G) := by
  let H := MulAction.stabilizer (MulAut G) (P : Subgroup G)
  let F := fixingSubgroup (MulAut G) (P : Set G)
  let r : H →* MulAut P :=
    { toFun := fun a => (a.val.subgroupMap (P : Subgroup G)).trans
        (MulEquiv.subgroupCongr a.property)
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let i : r.ker →* F :=
    (H.subtype.comp r.ker.subtype).codRestrict F (by
      intro a
      apply (mem_fixingSubgroup_iff (MulAut G)).mpr
      intro x hx
      change (a.val.val : MulAut G) x = x
      exact congrArg (fun b : MulAut P => ((b ⟨x, hx⟩ : P) : G)) a.property)
  have hi : Function.Injective i := by
    intro a b hab
    have hab' : (a.val.val : MulAut G) = b.val.val :=
      congrArg (fun z : F => (z : MulAut G)) hab
    exact Subtype.ext (Subtype.ext hab')
  let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective hi
  let : Group.IsSolvable H :=
    Group.isSolvable_of_ker_le_range r.ker.subtype r (by rw [Subgroup.range_subtype])
  let q := (QuotientGroup.mk' (innerSubgroup G)).comp H.subtype
  apply Group.isSolvable_of_surjective (f := q)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (a • P) P
  have hm : MulAut.conj g * a ∈ H := by
    change (MulAut.conj g * a) • (P : Subgroup G) = (P : Subgroup G)
    rw [mul_smul]
    exact congrArg Sylow.toSubgroup hg
  refine ⟨⟨MulAut.conj g * a, hm⟩, ?_⟩
  change QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g * a) = _
  have hi : QuotientGroup.mk' (innerSubgroup G) (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  rw [map_mul, hi, one_mul]

end MulAut
