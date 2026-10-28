module
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The radical of a supplement to the solvable radical

A supplement B maps onto G/O∞(G), and the kernel is B∩O∞(G).
Since the radical quotient has trivial solvable radical, the solvable
kernel correspondence proves O∞(B)=B∩O∞(G). The injective version
retains the original inclusion map for local-component applications.

Source: Aschbacher--Smith, the radical supplements in 13.1.8--9,
pp.868--869, using the standard solvable-kernel correspondence.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem solvableRadical_comap_of_radical_supplement (B : Subgroup G)
    (hgen : solvableRadical G ⊔ B = ⊤) :
    (solvableRadical G).comap B.subtype = solvableRadical B := by
  let q := QuotientGroup.mk' (solvableRadical G)
  let f := q.comp B.subtype
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (solvableRadical G) z
    have hg : g ∈ solvableRadical G ⊔ B := hgen.symm ▸ mem_top _
    obtain ⟨r,hr,b,hb,rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨⟨b,hb⟩,?_⟩
    change q b = q (r*b)
    rw [map_mul,show q r=1 from (QuotientGroup.eq_one_iff r).mpr hr,one_mul]
  have hker : f.ker = (solvableRadical G).comap B.subtype := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  let i : f.ker →* solvableRadical G :=
    (B.subtype.comp f.ker.subtype).codRestrict _ (by
      intro x
      have hx := x.property
      have hh : (x : B) ∈ (solvableRadical G).comap B.subtype := hker ▸ hx
      exact hh)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := i) (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : solvableRadical G => (z : G)) hab)
  let : Finite (G ⧸ solvableRadical G) := Finite.of_surjective q
    (QuotientGroup.mk'_surjective _)
  have he := comap_solvableRadical_eq_of_solvable_ker f hf
  rw [solvableRadical_quotient_solvableRadical] at he
  change f.ker = solvableRadical B at he
  exact hker.symm.trans he

variable {A : Type*} [Group A] [Finite A]

theorem solvableRadical_comap_of_injective_supplement (i : A →* G)
    (hi : Function.Injective i) (hgen : solvableRadical G ⊔ i.range = ⊤) :
    (solvableRadical G).comap i = solvableRadical A := by
  let f := i.rangeRestrict
  have hfi : Function.Injective f := fun a b he => hi (congrArg Subtype.val he)
  have hk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff f).mpr hfi
  let : Group.IsSolvable f.ker := by rw [hk]; infer_instance
  have he := comap_solvableRadical_eq_of_solvable_ker f i.rangeRestrict_surjective
  rw [← solvableRadical_comap_of_radical_supplement i.range hgen,comap_comap] at he
  exact he
end Subgroup
