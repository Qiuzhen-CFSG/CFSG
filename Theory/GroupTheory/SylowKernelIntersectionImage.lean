module
public import Theory.GroupTheory.SylowPreimageNormalizerImage
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Intersecting a prime-subgroup image with a normal subgroup

If a p-subgroup R contains a Sylow subgroup of the kernel of f, then R is
Sylow in the preimage of f(R). Intersecting with a normal subgroup C and
mapping that Sylow intersection proves f(R ∩ C) = f(R) whenever f(R) ≤ f(C).
This retains the original intersection even for kernels with odd factors.

Source application: Aschbacher--Smith 4.3.14--16, pp.617--618, the passage
from the original radical to its inner component image.
-/

public section
open Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A p-subgroup containing a kernel Sylow lifts its image inside a normal subgroup.
The kernel may have non-p factors. -/
theorem map_inf_eq_map_of_kernel_sylow_le (R C : Subgroup G) [C.Normal] (hp : IsPGroup p R)
    (f : G →* A) (P : Sylow p f.ker)
    (hP : (P : Subgroup f.ker).map f.ker.subtype ≤ R)
    (hRC : R.map f ≤ C.map f) : (R ⊓ C).map f = R.map f := by
  have hi : (P : Subgroup f.ker).map f.ker.subtype = R ⊓ f.ker := by
    have he := P.is_maximal' hp.comap_subtype (by
      intro x hx
      exact hP (mem_map_of_mem _ hx))
    change R.subgroupOf f.ker = (P : Subgroup f.ker) at he
    have hm := congrArg (Subgroup.map f.ker.subtype) he
    simpa only [subgroupOf_map_subtype] using hm.symm
  obtain ⟨S,hS⟩ := exists_sylow_preimage_of_kernel_intersection R hp f P hi
  let U := (R.map f).comap f
  let B := C.subgroupOf U
  let g : B →* R.map f := (f.comp (U.subtype.comp B.subtype)).codRestrict _
    (fun x => x.val.property)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨x,hx,hxa⟩ := hRC a.property
    refine ⟨⟨⟨x,?_⟩,hx⟩,Subtype.ext hxa⟩
    change f x ∈ R.map f
    exact hxa ▸ a.property
  obtain ⟨Q,hQ⟩ := S.exists_subgroupOf_eq_of_normal B
  have ht : (Q.mapSurjective hg : Subgroup (R.map f)) = ⊤ := by
    exact (Q.mapSurjective hg).is_maximal'
      ((hp.map f).to_subgroup ⊤) le_top |>.symm
  apply le_antisymm (map_mono inf_le_left)
  intro a ha
  have hqa : (⟨a,ha⟩ : R.map f) ∈ (Q : Subgroup B).map g := by
    rw [←Sylow.coe_mapSurjective hg,ht]
    exact mem_top _
  obtain ⟨q,hq,hqa⟩ := hqa
  have hqR : ((q : U) : G) ∈ R := by
    rw [hQ,hS] at hq
    exact hq
  exact ⟨q,⟨hqR,q.property⟩,congrArg Subtype.val hqa⟩
end Subgroup
