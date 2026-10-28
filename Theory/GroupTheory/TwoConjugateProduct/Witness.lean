module
public import Theory.GroupTheory.TwoConjugateProduct.Perfect
public import Theory.GroupTheory.NormalCoreTwoClosedTransport

/-!
# Perfect paired witnesses and their marked quotient

Conjugate only in the first factor of an actual product. Perfectness removes
all diagonal coupling to the abelian second projection. The generated group
is the first witness times that projection, its original Borel core is the
second projection, and the quotient is the original perfect witness. The
Sylow, Borel, internal conjugator and quotient map survive marked embeddings.

Source: Aschbacher–Smith E.2.7, paired Bender paragraph, printed p.219.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace TwoConjugateProduct
variable {G A : Type*} [Group G] [Group A]

structure CoreFreePair (S M V : Subgroup G) where
  subgroup : Subgroup G
  le : V ≤ subgroup
  conjugator : subgroup
  generate : V.subgroupOf subgroup ⊔
    (V.subgroupOf subgroup).map (MulAut.conj conjugator).toMonoidHom = ⊤
  sylow : Sylow 2 subgroup
  sylow_eq : (sylow : Subgroup subgroup) = S.subgroupOf subgroup
  corefree : (M.subgroupOf subgroup).normalCore = ⊥

structure ProductPair (S M V : Subgroup G) (L : Type*) [Group L] where
  subgroup : Subgroup G
  le : V ≤ subgroup
  conjugator : subgroup
  generate : V.subgroupOf subgroup ⊔
    (V.subgroupOf subgroup).map (MulAut.conj conjugator).toMonoidHom = ⊤
  sylow : Sylow 2 subgroup
  sylow_eq : (sylow : Subgroup subgroup) = S.subgroupOf subgroup
  projection : subgroup →* L
  surjective : Function.Surjective projection
  kernel_two : IsPGroup 2 projection.ker
  core_eq : (M.subgroupOf subgroup).normalCore = projection.ker
  borel : Subgroup L
  borel_eq : M.subgroupOf subgroup = borel.comap projection

theorem pair_map {D : Type*} [Group D]
    (f : G →* D) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup,Subgroup.map_map,Subgroup.map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

variable [Finite G] [Finite A]

def CoreFreePair.product {S M : Subgroup G} {V : Subgroup (G × A)}
    (w : CoreFreePair S M (V.map (MonoidHom.fst G A)))
    [Group.IsPerfect w.subgroup] [IsMulCommutative (V.map (MonoidHom.snd G A))]
    (hV2 : IsPGroup 2 (V.map (MonoidHom.snd G A)))
    (S2 M2 : Subgroup A) (hVS : V.map (MonoidHom.snd G A) ≤ S2)
    (hVM : V.map (MonoidHom.snd G A) ≤ M2) :
    ProductPair (S.prod S2) (M.prod M2) V w.subgroup := by
  let W := V.map (MonoidHom.snd G A)
  let I := w.subgroup.prod W
  have hVI : V ≤ I := le_prod_iff.mpr ⟨w.le,le_rfl⟩
  let g : I := ⟨((w.conjugator:G),1),w.conjugator.property,W.one_mem⟩
  have hfirst : V.map (MonoidHom.fst G A) ⊔
      (V.map (MonoidHom.fst G A)).map (MulAut.conj (w.conjugator:G)).toMonoidHom =
        w.subgroup := by
    have hh := congrArg (map w.subgroup.subtype) w.generate
    rw [pair_map,map_subgroupOf_eq_of_le w.le,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hgen : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [pair_map,map_subgroupOf_eq_of_le hVI,← MonoidHom.range_eq_map,range_subtype]
    let : Group.IsPerfect ↥(V.map (MonoidHom.fst G A) ⊔
        (V.map (MonoidHom.fst G A)).map (MulAut.conj (w.conjugator:G)).toMonoidHom) :=
      hfirst.symm ▸ inferInstance
    exact (twoConjugate_eq_prod V (w.conjugator:G)).trans (by rw [hfirst])
  let r : I →* w.subgroup :=
    ((MonoidHom.fst G A).comp I.subtype).codRestrict w.subgroup (fun x => x.property.1)
  have hr : Function.Surjective r := by
    intro x
    exact ⟨⟨((x:G),1),x.property,W.one_mem⟩,rfl⟩
  have hk : IsPGroup 2 r.ker := by
    let f : r.ker →* W :=
      ((MonoidHom.snd G A).comp (I.subtype.comp r.ker.subtype)).codRestrict W
        (fun x => x.val.property.2)
    apply hV2.of_injective f
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hx : ((x.val : G × A).1) = 1 := congrArg Subtype.val x.property
      have hy : ((y.val : G × A).1) = 1 := congrArg Subtype.val y.property
      exact hx.trans hy.symm
    · exact congrArg Subtype.val hxy
  let P := w.sylow.comapOfKerIsPGroup r hk (by rw [MonoidHom.range_eq_top.mpr hr]; exact le_top)
  have hP : (P : Subgroup I) = (S.prod S2).subgroupOf I := by
    ext x
    change r x ∈ (w.sylow : Subgroup w.subgroup) ↔ (x:G×A) ∈ S.prod S2
    rw [w.sylow_eq]
    change (x.val).1 ∈ S ↔ (x.val).1 ∈ S ∧ (x.val).2 ∈ S2
    exact ⟨fun h => ⟨h,hVS x.property.2⟩,And.left⟩
  have hM : (M.prod M2).subgroupOf I = (M.subgroupOf w.subgroup).comap r := by
    ext x
    change (x.val).1 ∈ M ∧ (x.val).2 ∈ M2 ↔ (x.val).1 ∈ M
    exact ⟨And.left,fun h => ⟨h,hVM x.property.2⟩⟩
  have hcore : ((M.prod M2).subgroupOf I).normalCore = r.ker := by
    rw [hM,normalCore_comap_of_surjective r hr,w.corefree,MonoidHom.comap_bot]
  exact ⟨I,hVI,g,hgen,P,hP,r,hr,hk,hcore,M.subgroupOf w.subgroup,hM⟩

namespace ProductPair
variable {S M V : Subgroup G} {L : Type*} [Group L]

def quotientEquiv (w : ProductPair S M V L) :
    w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq w.core_eq).trans
    (QuotientGroup.quotientKerEquivOfSurjective w.projection w.surjective)

omit [Finite G] in
theorem quotientEquiv_mk (w : ProductPair S M V L) (x : w.subgroup) :
    w.quotientEquiv (QuotientGroup.mk' _ x) = w.projection x := rfl

omit [Finite G] in
theorem quotient_borel (w : ProductPair S M V L) :
    ((M.subgroupOf w.subgroup).map (QuotientGroup.mk' _)).map
      w.quotientEquiv.toMonoidHom = w.borel := by
  rw [map_map]
  change (M.subgroupOf w.subgroup).map w.projection = w.borel
  rw [w.borel_eq,map_comap_eq_self_of_surjective w.surjective]

variable {H : Type*} [Group H] [Finite H]
def map (w : ProductPair S M V L) (f : G →* H) (hf : Function.Injective f)
    (S' M' : Subgroup H) (hS : S'.comap f = S) (hM : M'.comap f = M) :
    ProductPair S' M' (V.map f) L := by
  let I := w.subgroup.map f
  let e : w.subgroup ≃* I := w.subgroup.equivMapOfInjective f hf
  have hmap (A : Subgroup H) (B : Subgroup G) (hAB : A.comap f = B) :
      (B.subgroupOf w.subgroup).map e.toMonoidHom = A.subgroupOf I := by
    have hc : (A.subgroupOf I).comap e.toMonoidHom = B.subgroupOf w.subgroup := by
      ext x
      change f x ∈ A ↔ (x:G) ∈ B
      exact SetLike.ext_iff.mp hAB (x:G)
    rw [← hc,map_comap_eq_self_of_surjective e.surjective]
  have hV := hmap (V.map f) V (comap_map_eq_self_of_injective hf V)
  have hS' := hmap S' S hS
  have hM' := hmap M' M hM
  let P := w.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  let r := w.projection.comp e.symm.toMonoidHom
  have hr : Function.Surjective r := w.surjective.comp e.symm.surjective
  have hk : IsPGroup 2 r.ker := by
    change IsPGroup 2 (w.projection.comp e.symm.toMonoidHom).ker
    change IsPGroup 2 (w.projection.ker.comap e.symm.toMonoidHom)
    exact w.kernel_two.comap_of_injective _ e.symm.injective
  have hgen : (V.map f).subgroupOf I ⊔
      ((V.map f).subgroupOf I).map (MulAut.conj (e w.conjugator)).toMonoidHom = ⊤ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) w.generate
    rw [pair_map,hV,map_top_of_surjective _ e.surjective] at hh
    exact hh
  have hMe : M'.subgroupOf I = (M.subgroupOf w.subgroup).comap e.symm.toMonoidHom := by
    exact hM'.symm.trans (comap_equiv_eq_map_symm e.symm (M.subgroupOf w.subgroup)).symm
  have hcore : (M'.subgroupOf I).normalCore = r.ker := by
    rw [hMe,normalCore_comap_of_surjective _ e.symm.surjective,w.core_eq]
    rfl
  have hb : M'.subgroupOf I = w.borel.comap r := by
    rw [hMe,w.borel_eq,comap_comap]
  refine ⟨I,map_mono w.le,e w.conjugator,hgen,P,?_,r,hr,hk,hcore,w.borel,hb⟩
  change (w.sylow : Subgroup w.subgroup).map e.toMonoidHom = _
  rw [w.sylow_eq,hS']
end ProductPair
end TwoConjugateProduct
