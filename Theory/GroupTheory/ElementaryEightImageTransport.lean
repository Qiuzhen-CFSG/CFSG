module
public import Theory.GroupTheory.ElementaryEightPlanePoint
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Transport of actual elementary-eight point images

An injective group homomorphism transports a point-stabilizer subgroup of
the actual conjugation image into the ambient conjugation image. It also
preserves the intersection of a subgroup with an elementary subgroup's
centralizer. These identities retain the literal embedded subgroup needed
by the point-and-plane normalizer argument in Aschbacher--Smith 15.1.11.
-/

public section
open Subgroup
namespace ElementaryEightPointImage
variable {G H : Type*} [Group G] [Group H]

noncomputable def map {E : Subgroup G} (point : ElementaryEightPointImage E)
    (f : G →* H) (hf : Function.Injective f) : ElementaryEightPointImage (E.map f) := by
  let e := E.equivMapOfInjective f hf
  let φ := MulAut.congr e
  refine ⟨e point.z,fun h => point.ne_one (e.injective (h.trans e.map_one.symm)),
    point.J.map φ.toMonoidHom,?_,?_,?_⟩
  · rw [card_map_of_injective φ.injective]
    exact point.image_card
  · rintro _ ⟨a,ha,rfl⟩
    obtain ⟨g,hg⟩ := point.le_range ha
    let g' : normalizer (E.map f : Set H) := ⟨f g,
      E.le_normalizer_map f (mem_map_of_mem f g.property)⟩
    refine ⟨g',?_⟩
    rw [←hg]
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    apply Subtype.ext
    change f (g:G)*f (x:G)*(f (g:G))⁻¹ = f ((E.normalizerMonoidHom g (e.symm (e x)) : E) : G)
    rw [e.symm_apply_apply]
    change f (g:G)*f (x:G)*(f (g:G))⁻¹ = f ((g:G)*(x:G)*(g:G)⁻¹)
    simp only [map_mul,map_inv]
  · rintro ⟨_,a,ha,rfl⟩
    change e (a (e.symm (e point.z)))=e point.z
    rw [e.symm_apply_apply,point.fixed ⟨a,ha⟩]
end ElementaryEightPointImage
