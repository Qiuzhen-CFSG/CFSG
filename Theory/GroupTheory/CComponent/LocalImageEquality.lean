module
public import Theory.GroupTheory.CComponent.Basic

/-!
# Lifting equality of local component images

If the kernel of a homomorphism lies in S, equality of the images of B≤K
puts K inside BS. A C-component K then remains a C-component of BS, where
minimality identifies it with the original local C-component B. No global
subnormality of B or solvability assumption on the kernel is required.

Source: the local C-component calculus of Aschbacher–Smith A.3.3 and A.3.11,
used in the radical quotient in 12.2.25, printed p.805.
-/

public section
open Subgroup
namespace Subgroup
/-- A local C-component equals a containing ambient C-component when their
images agree and the kernel lies in the original actor subgroup. -/
theorem local_cComponent_eq_of_map_eq {X Q : Type*} [Group X] [Group Q]
    {B K S : Subgroup X} (hB : (B.subgroupOf (B ⊔ S)).IsCComponent)
    (hK : K.IsCComponent) (hBK : B ≤ K) (f : X →* Q) (hk : f.ker ≤ S)
    (he : B.map f = K.map f) : B = K := by
  have hKJ : K ≤ B ⊔ S := by
    apply le_trans (le_comap_map f K)
    rw [← he,comap_map_eq]
    exact sup_le_sup_left hk B
  have hh := hB.eq_of_le (hK.subgroupOf hKJ) (comap_mono hBK)
  have hm := congrArg (map (B ⊔ S).subtype) hh
  simpa only [map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le hKJ] using hm
end Subgroup
