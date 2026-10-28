module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Lifting containment through a normalizing prime-group kernel

If the kernel of a homomorphism is a p-group and normalizes Y, then a
p-perfect subgroup whose image lies in the image of Y already lies in Y.
Pass to Y ker(f), where Y is normal and the quotient is a p-group; the
p-perfect subgroup has trivial image in that quotient.

Source application: Aschbacher–Smith,13.5.14(3), printed p.919.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A]

theorem isPPerfect_le_of_map_le_of_kernel_normalizes {p : ℕ}
    (f : G →* A) (X Y : Subgroup G) (hX : IsPPerfect p X)
    (hk : IsPGroup p f.ker) (hn : f.ker ≤ normalizer (Y : Set G))
    (hi : X.map f ≤ Y.map f) : X ≤ Y := by
  let N := Y ⊔ f.ker
  have hXN : X ≤ N := by
    change X ≤ Y ⊔ f.ker
    rw [←comap_map_eq]
    exact (le_comap_map f X).trans (comap_mono hi)
  let : (Y.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le Y.le_normalizer hn)
  have hsup : Y.subgroupOf N ⊔ f.ker.subgroupOf N = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show Y≤N from le_sup_left),
      map_subgroupOf_eq_of_le (show f.ker≤N from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hquot := isPGroup_quotient_of_sup_eq_top (Y.subgroupOf N) (f.ker.subgroupOf N)
    hk.comap_subtype hsup
  have hp : IsPPerfect p (X.subgroupOf N) := hX.of_surjective
    (subgroupOfEquivOfLe hXN).symm.toMonoidHom (subgroupOfEquivOfLe hXN).symm.surjective
  have hle : X.subgroupOf N ≤ Y.subgroupOf N :=
    (le_pResidual_of_isPPerfect (X.subgroupOf N) hp).trans (sInf_le ⟨inferInstance,hquot⟩)
  intro x hx
  exact hle (show (⟨x,hXN hx⟩:N)∈X.subgroupOf N from hx)

end Subgroup
end
