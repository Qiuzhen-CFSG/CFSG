module
public import Theory.GroupTheory.PerfectNormalImage
public import Theory.GroupTheory.PerfectSimpleImage

/-!
# Kernels of nontrivial images of perfect simple extensions

If a perfect group has a simple quotient with solvable kernel, every
nontrivial homomorphism has kernel contained in that solvable kernel.
The image of the new kernel in the simple quotient is trivial or full;
full image would force the kernel to be the whole perfect group.

This retains the full covering actor in the C.4.5 application of
Aschbacher--Smith, *The Classification of Quasithin Groups*, p.152.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem ker_le_of_nontrivial_hom_of_simple_quotient
    {F S D : Type*} [Group F] [Group S] [Group D]
    [Group.IsPerfect F] [IsSimpleGroup S]
    (q : F →* S) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (f : F →* D) (hne : f ≠ 1) : f.ker ≤ q.ker := by
  let : (f.ker.map q).Normal := (inferInstance : f.ker.Normal).map q hq
  rcases (inferInstance : (f.ker.map q).Normal).eq_bot_or_eq_top with hb | ht
  · exact (Subgroup.map_eq_bot_iff _).mp hb
  · have hk := eq_top_of_perfect_of_solvable_kernel_image q f.ker ht
    exact (hne (by
      ext x
      exact (show x ∈ f.ker from hk.symm ▸ mem_top x))).elim

theorem solvable_ker_of_nontrivial_hom_of_simple_quotient
    {F S D : Type*} [Group F] [Group S] [Group D]
    [Group.IsPerfect F] [IsSimpleGroup S]
    (q : F →* S) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (f : F →* D) (hne : f ≠ 1) : Group.IsSolvable f.ker :=
  Group.isSolvable_of_isSolvable_injective
    (f := inclusion (ker_le_of_nontrivial_hom_of_simple_quotient q hq f hne))
    (inclusion_injective _)

end Theory.GroupTheory
