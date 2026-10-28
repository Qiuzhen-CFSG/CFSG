module
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Images of a perfect cover in its own simple quotient

A perfect group with solvable kernel over a finite simple group has either
trivial or surjective image in another copy of that simple group. A proper
image would be too small to retain the simple section. Perfect subgroups
also avoid a normal two-group supplement to a normal subgroup.

These facts localize the conjugate component in Aschbacher--Smith 10.2.10,
printed p.753, without assuming all proper subgroups of the model solvable.
-/

public section
open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {F S : Type*} [Group F] [Group S] [Finite S]
  [IsSimpleGroup S] [Group.IsPerfect F]

theorem hom_eq_one_or_surjective_of_simple_quotient
    (q : F →* S) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (f : F →* S) : f = 1 ∨ Function.Surjective f := by
  by_cases hf : Function.Surjective f
  · exact Or.inr hf
  left
  have hz : f.rangeRestrict = 1 := hom_eq_one_of_no_simple_section q hq (by
    intro U g hg
    have hc : Nat.card S ≤ Nat.card f.range :=
      (Nat.card_le_card_of_surjective g hg).trans U.card_le_card_group
    have ht : f.range = ⊤ := eq_top_of_card_eq f.range
      (Nat.le_antisymm f.range.card_le_card_group hc)
    exact hf (MonoidHom.range_eq_top.mp ht)) f.rangeRestrict
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun hz x)
end Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem perfect_le_of_le_sup_two (A L Q : Subgroup G)
    [Group.IsPerfect A] [L.Normal] [Q.Normal] (hQ : IsPGroup 2 Q)
    (hA : A ≤ L ⊔ Q) : A ≤ L := by
  let U := L ⊔ Q
  let L' := L.subgroupOf U
  let Q' := Q.subgroupOf U
  let : Group.IsPerfect (A.subgroupOf U) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hA).symm.toMonoidHom) (subgroupOfEquivOfLe hA).symm.surjective
  have hgen : L' ⊔ Q' = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ U from le_sup_left) (show Q ≤ U from le_sup_right)]
    exact subgroupOf_self U
  let : Group.IsNilpotent (U ⧸ L') :=
    (isPGroup_quotient_of_sup_eq_top L' Q' hQ.comap_subtype hgen).isNilpotent
  have hn := le_of_isPerfect_of_solvable_quotient (A.subgroupOf U) L'
  intro a ha
  exact hn (show (⟨a,hA ha⟩ : U) ∈ A.subgroupOf U from ha)
end Subgroup

