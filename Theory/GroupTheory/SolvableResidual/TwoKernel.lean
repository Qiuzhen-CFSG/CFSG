module
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
/-!
# Residuals over a perfect image with two-group kernel

The solvable residual maps onto a perfect quotient. Its supplement is the
original two-group kernel, so it is also the two-residual. The preimage
version retains the literal factor map used in natural paired actions.
-/
public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- A perfect image and two-group kernel identify the two original residuals. -/
theorem pResidual_eq_solvableResidual_of_perfect_image
    (q : G →* H) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) [Group.IsPerfect H] :
    pResidual 2 G = solvableResidual G := by
  let D := solvableResidual G
  have hi : D.map q = ⊤ := by
    rw [show D = solvableResidual G from rfl,map_solvableResidual_eq q hq,
      solvableResidual_eq_top]
  have hs : D ⊔ q.ker = ⊤ := by
    rw [←comap_map_eq,hi,comap_top]
  exact (residuals_of_perfect_normal_sup_twoGroup D q.ker hk hs).1

/-- The two-residual preimage factor equals the canonical perfect component. -/
theorem embedded_pResidual_eq_solvableResidual_of_two_kernel
    (q : G →* H) (A : Subgroup H) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) [Group.IsPerfect A] :
    (pResidual 2 (A.comap q)).map (A.comap q).subtype =
      (solvableResidual (A.comap q)).map (A.comap q).subtype := by
  let f := q.subgroupComap A
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨g,hg⟩ := hq a
    exact ⟨⟨g,show q g ∈ A from hg.symm ▸ a.property⟩,Subtype.ext hg⟩
  have hfk : IsPGroup 2 f.ker := by
    let i : f.ker →* q.ker := {
      toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    apply hk.of_injective i
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => (z : G)) h
  rw [pResidual_eq_solvableResidual_of_perfect_image f hf hfk]
end Subgroup
