module
public import Theory.GroupTheory.CComponent.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A nonsolvable subgroup in a normal intersection

A proper subnormal subgroup of a C-component is solvable. Consequently a
normal subgroup containing a nonsolvable subgroup of a C-component contains
the whole component. Applied to the centralizer of a normal subgroup, this
separates a component that moves it from one containing a nonsolvable
centralizing subgroup.

Source: Aschbacher–Smith, A.3.3(1), printed pp.41–42; the separation step in
10.2.6, printed pp.748–749.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup containing a nonsolvable part of a C-component contains
that whole C-component. -/
theorem IsCComponent.le_normal_of_nonsolvable_subgroup
    {I B C : Subgroup G} (hI : I.IsCComponent) [C.Normal]
    (hB : ¬ Group.IsSolvable B) (hBI : B ≤ I) (hBC : B ≤ C) : I ≤ C := by
  by_contra hnot
  let N := C.subgroupOf I
  have hn : N ≠ ⊤ := fun ht => hnot (subgroupOf_eq_top.mp ht)
  let : Group.IsSolvable N := hI.isSolvable_of_subnormal_lt_top
    (inferInstance : N.Normal).isSubnormal hn
  let f : B →* N :=
    { toFun := fun b => ⟨⟨b,hBI b.property⟩,hBC b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact hB (Group.isSolvable_of_isSolvable_injective
    (f := f) (fun x y he => Subtype.ext (congrArg (fun n : N => ((n : I) : G)) he)))

/-- Components containing respectively a moving and a nonsolvable fixing
subgroup of a normal subgroup are distinct. -/
theorem IsCComponent.ne_of_moving_and_centralizing
    {I J A B W : Subgroup G} [W.Normal] (hI : I.IsCComponent)
    (hAI : A ≤ I) (hBJ : B ≤ J) (hB : ¬ Group.IsSolvable B)
    (hm : ⁅W,A⁆ ≠ ⊥) (hc : ⁅W,B⁆ = ⊥) : I ≠ J := by
  intro he
  have hBC : B ≤ centralizer (W : Set G) := by
    rw [commutator_comm] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc
  have hIC := hI.le_normal_of_nonsolvable_subgroup hB (he.symm ▸ hBJ) hBC
  apply hm
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hAI.trans hIC)
end Subgroup
