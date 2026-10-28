module

public import Theory.GroupTheory.SimpleSectionSolvableLayers
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Alternating layers from permutation actions

A permutation action with solvable kernel gives two solvable normal layers
around a subgroup of the alternating group. Take the inverse image of the
alternating group for the outer layer, then quotient its restricted action
by its actual kernel. The first isomorphism theorem supplies the injection;
the outer quotient embeds into the sign group.

An action also descends along any surjection whose kernel it kills. Its
new kernel is a quotient of the old one, so remains solvable. This permits
actions of matrix groups to descend to their projective images.

These are elementary kernel and quotient arguments; no subgroup
classification is assumed.
-/

namespace Theory.GroupTheory

/-- The sign character removes the outer layer, and the kernel of the
restricted action removes the inner layer. -/
public theorem SolvableLayersEmbedding.of_permutation_solvable_kernel
    {G α : Type*} [Group G] [Fintype α] [DecidableEq α]
    (f : G →* Equiv.Perm α) [Group.IsSolvable f.ker] :
    SolvableLayersEmbedding G (alternatingGroup α) := by
  let s : G →* ℤˣ := Equiv.Perm.sign.comp f
  let N := s.ker
  let a : N →* alternatingGroup α :=
    { toFun := fun x => ⟨f x.val, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
  have houter : Group.IsSolvable (G ⧸ N) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective s)
  let k : a.ker →* f.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => z.val) h))
  refine ⟨N, inferInstance, houter, a.ker, inferInstance, ?_,
    QuotientGroup.kerLift a, QuotientGroup.kerLift_injective a⟩
  exact Group.isSolvable_of_isSolvable_injective hk

/-- Descending an action along a surjection sends its solvable kernel onto
the kernel of the descended action. -/
public theorem exists_solvable_kernel_hom_of_surjective
    {L G H : Type*} [Group L] [Group G] [Group H]
    (q : L →* G) (hq : Function.Surjective q) (f : L →* H)
    (hker : q.ker ≤ f.ker) [Group.IsSolvable f.ker] :
    ∃ d : G →* H, d.comp q = f ∧ Group.IsSolvable d.ker := by
  let d : G →* H := q.liftOfSurjective hq ⟨f, hker⟩
  have hd (x : L) : d (q x) = f x :=
    q.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hq) ⟨f, hker⟩ x
  let k : f.ker →* d.ker :=
    { toFun := fun x => ⟨q x.val, (hd x.val).trans x.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y => Subtype.ext (map_mul q x.val y.val) }
  have hk : Function.Surjective k := by
    intro y
    obtain ⟨x, hx⟩ := hq y.val
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x = 1
    rw [← hd x, hx]
    exact y.property
  exact ⟨d, MonoidHom.ext hd, Group.isSolvable_of_surjective hk⟩

end Theory.GroupTheory
