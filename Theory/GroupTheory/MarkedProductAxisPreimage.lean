module
public import Theory.GroupTheory.MarkedProductAxis

/-!
# Restricting a marked product preimage to an axis

On a subgroup whose quotient image is a full first axis, the preimage
of a product subgroup is precisely the preimage of the first coordinate
subgroup. This retains the original quotient and coordinate map.
Source application: Baumann factor centralizers in10.2.1,p.743.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H X Z : Type*} [Group G] [Group H] [Group X] [Group Z]
set_option backward.isDefEq.respectTransparency false

theorem marked_first_axis_preimage (q : G →* H) (Y : Subgroup H)
    (e : Y ≃* X × Z) (P : Subgroup G)
    (hP : P.map q = ((⊤ : Subgroup X).prod (⊥ : Subgroup Z)).map
      (Y.subtype.comp e.symm.toMonoidHom))
    (f : P →* X)
    (hf : ∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (e ⟨q (g:G),hg⟩).1)
    (B : Subgroup X) (C : Subgroup Z) :
    (((B.prod C).map (Y.subtype.comp e.symm.toMonoidHom)).comap q).subgroupOf P = B.comap f := by
  ext g
  have hg := mem_map_of_mem q g.property
  rw [hP] at hg
  obtain ⟨z,hz,hzg⟩ := hg
  have hgy : q (g:G) ∈ Y := hzg ▸ (e.symm z).property
  have he : (⟨q (g:G),hgy⟩ : Y) = e.symm z := Subtype.ext hzg.symm
  have hfg : f g = z.1 := by rw [hf g hgy,he,e.apply_symm_apply]
  change q (g:G) ∈ (B.prod C).map (Y.subtype.comp e.symm.toMonoidHom) ↔ f g ∈ B
  rw [hfg]
  constructor
  · rintro ⟨w,hw,hwg⟩
    have hwe : e.symm w = e.symm z := Subtype.ext (hwg.trans hzg.symm)
    have hwz := e.symm.injective hwe
    exact hwz ▸ hw.1
  · intro hb
    refine ⟨z,⟨hb,?_⟩,hzg⟩
    rw [show z.2 = 1 from hz.2]
    exact C.one_mem
end Theory.GroupTheory
