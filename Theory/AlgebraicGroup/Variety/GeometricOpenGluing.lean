module

public import Theory.AlgebraicGroup.Variety.OpenSubvariety
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing geometric morphisms from rational-point local representatives

Suppose actual open subvarieties cover a geometric variety and their morphisms
agree with one function on rational points. On each open intersection,
closed-point extensionality proves equality of the scheme morphisms. Transport
through the actual pullback square then supplies Scheme.Cover.glueMorphisms.
The glued morphism is over the base field, restricts exactly to every local
map, and represents the prescribed rational-point function uniquely.

This is ordinary scheme gluing, used in the regular-family construction for
Borel, Linear Algebraic Groups, 10.8/13.13. The inputs are genuine local
morphisms; no global regularity of the common point function is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric
noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Equality on rational points determines geometric morphisms over an algebraically closed field. -/
private theorem morphism_eq_of_pointwise_eq {V W : Geometric k} (f g : Morphism V W)
    (h : ∀ x : Point V, f x = g x) : f = g := by
  let : LocallyOfFiniteType (f.hom ≫ W.structureMap) := by
    rw [f.commutes]
    infer_instance
  apply Morphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq W.structureMap
      (Set.univ : Set V.toScheme) isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    let p : Point V := ⟨pointOfClosedPoint V.structureMap x hx,
      pointOfClosedPoint_comp V.structureMap x hx⟩
    have hp : p.val (IsLocalRing.closedPoint k) = x :=
      pointOfClosedPoint_apply V.structureMap x hx _
    calc
      f.hom x = f.hom (p.val (IsLocalRing.closedPoint k)) := congrArg f.hom hp.symm
      _ = g.hom (p.val (IsLocalRing.closedPoint k)) := by
        change (f p).val (IsLocalRing.closedPoint k) = (g p).val (IsLocalRing.closedPoint k)
        rw [h p]
      _ = g.hom x := congrArg g.hom hp
  · exact f.commutes.trans g.commutes.symm

/-- The geometric inclusion of one actual open subvariety in another. -/
def openInclusionOfLE {V : Geometric k} {U U' : V.toScheme.Opens} (h : U ≤ U') :
    Morphism (openSubvariety V U).toGeometric (openSubvariety V U').toGeometric where
  hom := V.toScheme.homOfLE h
  commutes := by
    change V.toScheme.homOfLE h ≫ (U'.ι ≫ V.structureMap) = U.ι ≫ V.structureMap
    rw [← Category.assoc,Scheme.homOfLE_ι]

omit [IsAlgClosed k] in
@[simp] theorem openInclusionOfLE_comp_inclusion {V : Geometric k}
    {U U' : V.toScheme.Opens} (h : U ≤ U') :
    Morphism.comp (openInclusionOfLE h) (openSubvariety V U').inclusion =
      (openSubvariety V U).inclusion := by
  apply Morphism.ext
  exact V.toScheme.homOfLE_ι h

set_option backward.isDefEq.respectTransparency false in
theorem open_gluing_compatible {V W : Geometric k} {ι : Type v}
    (U : ι → V.toScheme.Opens)
    (F : ∀ i, Morphism (openSubvariety V (U i)).toGeometric W)
    (ψ : Point V → Point W)
    (hF : ∀ i p, F i p = ψ ((openSubvariety V (U i)).inclusion p)) (i j : ι) :
    pullback.fst (U i).ι (U j).ι ≫ (F i).hom =
      pullback.snd (U i).ι (U j).ι ≫ (F j).hom := by
  let left : Morphism (openSubvariety V (U i ⊓ U j)).toGeometric
      (openSubvariety V (U i)).toGeometric := openInclusionOfLE inf_le_left
  let right : Morphism (openSubvariety V (U i ⊓ U j)).toGeometric
      (openSubvariety V (U j)).toGeometric := openInclusionOfLE inf_le_right
  have he : Morphism.comp left (F i) = Morphism.comp right (F j) := by
    apply morphism_eq_of_pointwise_eq
    intro p
    rw [Morphism.comp_apply_point,Morphism.comp_apply_point,hF,hF]
    apply congrArg ψ
    have hl := congrArg (fun m : Morphism (openSubvariety V (U i ⊓ U j)).toGeometric V => m p)
      (openInclusionOfLE_comp_inclusion (V := V) (U := U i ⊓ U j) (U' := U i) inf_le_left)
    have hr := congrArg (fun m : Morphism (openSubvariety V (U i ⊓ U j)).toGeometric V => m p)
      (openInclusionOfLE_comp_inclusion (V := V) (U := U i ⊓ U j) (U' := U j) inf_le_right)
    exact hl.trans hr.symm
  let e := (isPullback_opens_inf (U i) (U j)).isoPullback
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc,← Category.assoc]
  change e.hom ≫ pullback.fst _ _ ≫ _ = e.hom ≫ pullback.snd _ _ ≫ _
  rw [(isPullback_opens_inf (U i) (U j)).isoPullback_hom_fst_assoc,
    (isPullback_opens_inf (U i) (U j)).isoPullback_hom_snd_assoc]
  exact congrArg Morphism.hom he

set_option backward.isDefEq.respectTransparency false in
/-- Glue genuine local morphisms agreeing with one rational-point function. -/
def glueOpenMorphisms {V W : Geometric k} {ι : Type v}
    (U : ι → V.toScheme.Opens) (hU : ⨆ i, U i = ⊤)
    (F : ∀ i, Morphism (openSubvariety V (U i)).toGeometric W)
    (ψ : Point V → Point W)
    (hF : ∀ i p, F i p = ψ ((openSubvariety V (U i)).inclusion p)) : Morphism V W where
  hom := (V.toScheme.openCoverOfIsOpenCover U hU).glueMorphisms (fun i => (F i).hom)
    (open_gluing_compatible U F ψ hF)
  commutes := by
    let C := V.toScheme.openCoverOfIsOpenCover U hU
    apply C.hom_ext
    intro i
    change C.f i ≫ (C.glueMorphisms (fun i => (F i).hom)
      (open_gluing_compatible U F ψ hF) ≫ W.structureMap) = _
    rw [← Category.assoc,C.ι_glueMorphisms]
    exact (F i).commutes

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem glueOpenMorphisms_restrict {V W : Geometric k} {ι : Type v}
    (U : ι → V.toScheme.Opens) (hU : ⨆ i, U i = ⊤)
    (F : ∀ i, Morphism (openSubvariety V (U i)).toGeometric W)
    (ψ : Point V → Point W)
    (hF : ∀ i p, F i p = ψ ((openSubvariety V (U i)).inclusion p)) (i : ι) :
    Morphism.comp (openSubvariety V (U i)).inclusion (glueOpenMorphisms U hU F ψ hF) = F i := by
  apply Morphism.ext
  change (U i).ι ≫ (V.toScheme.openCoverOfIsOpenCover U hU).glueMorphisms
    (fun j => (F j).hom) (open_gluing_compatible U F ψ hF) = (F i).hom
  exact (V.toScheme.openCoverOfIsOpenCover U hU).ι_glueMorphisms
    (fun j => (F j).hom) (open_gluing_compatible U F ψ hF) i

set_option backward.isDefEq.respectTransparency false in
theorem glueOpenMorphisms_apply {V W : Geometric k} {ι : Type v}
    (U : ι → V.toScheme.Opens) (hU : ⨆ i, U i = ⊤)
    (F : ∀ i, Morphism (openSubvariety V (U i)).toGeometric W)
    (ψ : Point V → Point W)
    (hF : ∀ i p, F i p = ψ ((openSubvariety V (U i)).inclusion p)) (p : Point V) :
    glueOpenMorphisms U hU F ψ hF p = ψ p := by
  have hm : p.val (IsLocalRing.closedPoint k) ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hm
  obtain ⟨q,hq,-⟩ := (point_mem_openSubvariety_iff V (U i) p).mp hi
  have he := congrArg (fun m : Morphism (openSubvariety V (U i)).toGeometric W => m q)
    (glueOpenMorphisms_restrict U hU F ψ hF i)
  change glueOpenMorphisms U hU F ψ hF ((openSubvariety V (U i)).inclusion q) = F i q at he
  rw [hq,hF,hq] at he
  exact he

/-- The common point function is represented by a unique geometric morphism. -/
theorem existsUnique_morphism_of_open_local_representatives
    {V W : Geometric k} {ι : Type v}
    (U : ι → V.toScheme.Opens) (hU : ⨆ i, U i = ⊤)
    (F : ∀ i, Morphism (openSubvariety V (U i)).toGeometric W)
    (ψ : Point V → Point W)
    (hF : ∀ i p, F i p = ψ ((openSubvariety V (U i)).inclusion p)) :
    ∃! f : Morphism V W, ∀ p, f p = ψ p := by
  refine ⟨glueOpenMorphisms U hU F ψ hF,glueOpenMorphisms_apply U hU F ψ hF,?_⟩
  intro g hg
  apply morphism_eq_of_pointwise_eq
  intro p
  exact (hg p).trans (glueOpenMorphisms_apply U hU F ψ hF p).symm

end
end Theory.AlgebraicGroup.Variety.Geometric
