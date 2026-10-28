module
public import Stellmacher.ElementaryAbelianMaxPair.CrossingEmbedding
public import Theory.GroupTheory.ClassTwoProduct
/-! # Class-two crossing Thompson products
The faithful crossing-core quotient embeds into the component Sylow quotient.
Class-two rows therefore pass from the component Sylow and crossing core to
the full maximum elementary Thompson product.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped Pointwise
namespace Stellmacher
variable {G:Type*} [Group G]
theorem crossing_thompson_class_two (S K:Subgroup G)
    (hJ:elementaryAbelianMaxJ S=(S⊓K)⊔
      (elementaryAbelianMaxJ S⊓centralizer (K:Set G)))
    (hSK:_root_.commutator (S.subgroupOf K)≤center (S.subgroupOf K))
    (x:G) (hx:x∈normalizer (S:Set G))
    (hd:Disjoint (S⊓centralizer (K:Set G)) ((S⊓centralizer (K:Set G)).conjBy x)) :
    _root_.commutator (elementaryAbelianMaxJ S)≤center (elementaryAbelianMaxJ S) := by
  let R:=elementaryAbelianMaxJ S
  let C:=R⊓centralizer (K:Set G)
  obtain ⟨j,hj,himage⟩:=crossing_thompson_core_embedding S K hJ x hx hd
  let eC:C≃*C.conjBy x:=C.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  let j':C→*(K⧸center K):=j.comp eC.toMonoidHom
  have hj':Function.Injective j':=hj.comp eC.injective
  have hi:j'.range≤(S.subgroupOf K).map (QuotientGroup.mk' (center K)):=by
    rintro _ ⟨c,rfl⟩
    exact himage ⟨eC c,rfl⟩
  have hC:_root_.commutator C≤center C:=Subgroup.ClassTwo.of_injective_range_le_image
    (S.subgroupOf K) (QuotientGroup.mk' (center K)) hSK j' hj' hi
  let f:(S⊓K:Subgroup G)→*S.subgroupOf K:={
    toFun a:=⟨⟨a.val,a.property.2⟩,a.property.1⟩
    map_one':=rfl
    map_mul' _ _:=rfl }
  have hf:Function.Injective f:=by
    intro a b h
    exact Subtype.ext (congrArg (fun c:S.subgroupOf K=>((c:K):G)) h)
  have hK:_root_.commutator (S⊓K:Subgroup G)≤center (S⊓K:Subgroup G):=
    Subgroup.ClassTwo.of_injective f hf hSK
  have hc:(S⊓K:Subgroup G)≤centralizer (C:Set G):=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (show S⊓K≤K from inf_le_right)))
  rw [hJ]
  exact Subgroup.ClassTwo.commuting_product _ _ hc hK hC
end Stellmacher
