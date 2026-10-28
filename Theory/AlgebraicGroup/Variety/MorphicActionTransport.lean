module

public import Theory.AlgebraicGroup.Variety.MorphicActionPullback
public import Theory.AlgebraicGroup.Variety.ClosedLocus

/-!
# Transporting regular actions along scheme isomorphisms

An isomorphism over the base field gives a rational-point equivalence and
transports the entire action morphism. Two reduced closed immersions with the
same support have equal ideal sheaves and hence are isomorphic over their
ambient variety. These constructions let a geometric orbit model carry its
original group action through a independently constructed curve isomorphism.
The concrete Borel-orbit consumer is in `Bor1.RankOneGeometry.OrbitTransport`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {X Y : Geometric k}

@[expose]
def schemeIsoPointEquiv (e : X.toScheme ≅ Y.toScheme)
    (he : e.hom ≫ Y.structureMap = X.structureMap) : Point X ≃ Point Y where
  toFun x := ⟨x.1 ≫ e.hom,by rw [Category.assoc,he,x.2]⟩
  invFun y := ⟨y.1 ≫ e.inv,by
    calc
      (y.1 ≫ e.inv) ≫ X.structureMap = y.1 ≫ (e.inv ≫ X.structureMap) := Category.assoc _ _ _
      _ = y.1 ≫ Y.structureMap := by rw [←he,e.inv_hom_id_assoc]
      _ = 𝟙 _ := y.2⟩
  left_inv x := by apply Subtype.ext; simp only [Category.assoc,e.hom_inv_id,Category.comp_id]
  right_inv y := by apply Subtype.ext; simp only [Category.assoc,e.inv_hom_id,Category.comp_id]

@[expose]
def MorphicAction.transportSchemeIso (A : MorphicAction G X)
    (e : X.toScheme ≅ Y.toScheme)
    (he : e.hom ≫ Y.structureMap = X.structureMap) : MorphicAction G Y := by
  let ep := schemeIsoPointEquiv e he
  let f : Morphism X Y := ⟨e.hom,he⟩
  let b : Morphism Y X := ⟨e.inv,by rw [←he,←Category.assoc,e.inv_hom_id,Category.id_comp]⟩
  let act : MulAction (Variety.Point G) (Point Y) :=
    { smul := fun g y => ep (A.toMulAction.smul g (ep.symm y))
      one_smul := by
        intro y
        change ep (A.toMulAction.smul 1 (ep.symm y))=y
        exact (congrArg ep (A.toMulAction.one_smul (ep.symm y))).trans (ep.apply_symm_apply y)
      mul_smul := by
        intro g h y
        change ep (A.toMulAction.smul (g*h) (ep.symm y))=
          ep (A.toMulAction.smul g (ep.symm (ep (A.toMulAction.smul h (ep.symm y)))))
        rw [ep.symm_apply_apply]
        exact congrArg ep (A.toMulAction.mul_smul g h (ep.symm y)) }
  let p := Morphism.pair (fst (ofAffine G) Y) (Morphism.comp (snd (ofAffine G) Y) b)
  refine MorphicAction.mk act (Morphism.comp (Morphism.comp p A.actionMorphism) f) ?_
  intro g y
  change f (A.actionMorphism (p (prodPoint ((affinePointEquiv G).symm g) y))) = _
  rw [Morphism.pair_apply,fst_prodPoint,Morphism.comp_apply_point,snd_prodPoint]
  rw [A.actionMorphism_apply]
  rfl

theorem MorphicAction.transportSchemeIso_smul (A : MorphicAction G X)
    (e : X.toScheme ≅ Y.toScheme)
    (he : e.hom ≫ Y.structureMap = X.structureMap)
    (g : Variety.Point G) (x : Point X) :
    (A.transportSchemeIso e he).toMulAction.smul g (schemeIsoPointEquiv e he x) =
      schemeIsoPointEquiv e he (A.toMulAction.smul g x) := by
  change schemeIsoPointEquiv e he (A.toMulAction.smul g
      ((schemeIsoPointEquiv e he).symm (schemeIsoPointEquiv e he x))) = _
  rw [Equiv.symm_apply_apply]


omit [IsAlgClosed k] in
theorem closedImmersion_ker_eq_of_range_eq
    {Z : Geometric k} (f : Morphism X Z) (g : Morphism Y Z)
    [IsClosedImmersion f.hom] [IsClosedImmersion g.hom]
    (he : Set.range f.hom=Set.range g.hom) : f.hom.ker=g.hom.ker := by
  let S : TopologicalSpace.Closeds Z.toScheme := ⟨Set.range f.hom,f.hom.isClosedEmbedding.isClosed_range⟩
  have hf : f.hom.ker.support=S := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker]
    exact f.hom.isClosedEmbedding.isClosed_range.closure_eq
  have hg : g.hom.ker.support=S := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.support_ker,g.hom.isClosedEmbedding.isClosed_range.closure_eq]
    exact he.symm
  have ef : f.hom.ker=Scheme.IdealSheafData.vanishingIdeal S := by
    apply le_antisymm
    · rw [←hf,Scheme.IdealSheafData.vanishingIdeal_support]
      exact Scheme.IdealSheafData.le_radical _
    · exact vanishingIdeal_le_ker_of_isReduced S f.hom (by rfl)
  have eg : g.hom.ker=Scheme.IdealSheafData.vanishingIdeal S := by
    apply le_antisymm
    · rw [←hg,Scheme.IdealSheafData.vanishingIdeal_support]
      exact Scheme.IdealSheafData.le_radical _
    · exact vanishingIdeal_le_ker_of_isReduced S g.hom he.symm.subset
  exact ef.trans eg.symm

omit [IsAlgClosed k] in
theorem exists_schemeIso_of_closedImmersion_range_eq
    {Z : Geometric k} (f : Morphism X Z) (g : Morphism Y Z)
    [IsClosedImmersion f.hom] [IsClosedImmersion g.hom]
    (he : Set.range f.hom=Set.range g.hom) :
    ∃ e : X.toScheme ≅ Y.toScheme,
      e.hom ≫ g.hom=f.hom ∧ e.hom ≫ Y.structureMap=X.structureMap := by
  have hk := closedImmersion_ker_eq_of_range_eq g f he.symm
  let t := IsClosedImmersion.lift g.hom f.hom hk.le
  have : IsIso t := IsClosedImmersion.isIso_lift g.hom f.hom hk
  let e := asIso t
  have ht : e.hom ≫ g.hom=f.hom := IsClosedImmersion.lift_fac _ _ _
  refine ⟨e,ht,?_⟩
  rw [←g.commutes,←Category.assoc,ht,f.commutes]


end Theory.AlgebraicGroup.Variety.Geometric
