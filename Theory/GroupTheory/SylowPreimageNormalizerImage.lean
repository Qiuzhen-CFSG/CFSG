module
public import Theory.GroupTheory.SylowPreimageNormalizer

/-!
# Normalizer lifting inside a homomorphism range

If a p-subgroup R contains a Sylow subgroup of the kernel, its kernel
intersection is that Sylow. Frattini in the actual preimage of the image
then lifts the image normalizer inside the homomorphism range. The target
need not be the range, and the kernel may have odd-order elements.

Source application: Aschbacher--Smith, paragraph preceding 4.3.15, p.618.
This extends SylowPreimageNormalizer with the nonsurjective formulation.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Subgroup
variable {G A : Type*} [Group G] [Group A] [Finite G] {p : ℕ} [Fact p.Prime]
/-- A kernel Sylow contained in R lifts the full image normalizer within the range. -/
theorem normalizer_image_of_kernel_sylow_le (R : Subgroup G) (hp : IsPGroup p R)
    (f : G →* A) (P : Sylow p f.ker)
    (hP : (P : Subgroup f.ker).map f.ker.subtype ≤ R) :
    f.range ⊓ normalizer (R.map f : Set A) ≤ (normalizer (R : Set G)).map f := by
  have hi : (P : Subgroup f.ker).map f.ker.subtype = R ⊓ f.ker := by
    have he := P.is_maximal' hp.comap_subtype (by
      intro x hx
      exact hP (mem_map_of_mem _ hx))
    change R.subgroupOf f.ker = (P : Subgroup f.ker) at he
    have hm := congrArg (Subgroup.map f.ker.subtype) he
    simpa only [subgroupOf_map_subtype] using hm.symm
  obtain ⟨S,hS⟩ := exists_sylow_preimage_of_kernel_intersection R hp f P hi
  let U := (R.map f).comap f
  let W := (normalizer (R.map f : Set A)).comap f
  have hfr := le_normalizer_sylow_sup U W
    (comap_mono (R.map f).le_normalizer)
    (comap_normalizer_eq_of_le_range (map_le_range f R)).le S
  rw [hS,map_subgroupOf_eq_of_le (le_comap_map f R)] at hfr
  have hm := map_mono (f := f) hfr
  rw [map_sup] at hm
  have hu : U.map f ≤ (normalizer (R : Set G)).map f := by
    rw [map_comap_eq]
    exact inf_le_right.trans (map_mono R.le_normalizer)
  have hw : W.map f ≤ (normalizer (R : Set G)).map f :=
    hm.trans (sup_le le_rfl hu)
  simpa only [W,map_comap_eq,inf_comm] using hw
end Subgroup

end
