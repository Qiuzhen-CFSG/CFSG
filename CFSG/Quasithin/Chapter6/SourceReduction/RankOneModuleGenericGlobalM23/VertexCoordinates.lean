module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.EdgeRigidity
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.VertexCoordinates

/-!
# Coordinates on the original source vertex group

The source field-extension theorem identifies L join H with PSL₃(4) extended
by Frobenius. In either parabolic orientation, inverse transpose and an inner
coordinate change then send the original L to the native pointwise edge fixer.
The original completion map still marks both parabolics and the entire Borel;
an equation on every element identifies its adjusted map with the restriction
of this same vertex equivalence.

The second theorem equips the already constructed original coset system with
these coordinates, retaining its fixed heptad marking and all its local maps.
Agreement of the vertex map with that heptad marking on Ix and its sixteen-core
remains unproved here. These are initial coordinates for 5.2.20(5), not an
unconditional ambient-recognition theorem.

Source: Aschbacher--Smith 5.2.16, 5.2.18 and 5.2.20(5), printed pp.655--657.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

private theorem map_of_restriction {G K Y : Type*} [Group G] [Group K] [Group Y]
    (R C X : Subgroup G) (hRC : R ≤ C) (hCX : C ≤ X)
    (e : C ≃* K) (f : X ≃* Y) (j : K →* Y)
    (hf : ∀ c : C, f ⟨c,hCX c.property⟩ = j (e c)) :
    (R.subgroupOf X).map f.toMonoidHom =
      ((R.subgroupOf C).map e.toMonoidHom).map j := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨e ⟨x,hRC hx⟩,⟨⟨x,hRC hx⟩,hx,rfl⟩,?_⟩
    exact (hf ⟨x,hRC hx⟩).symm
  · rintro ⟨_,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨⟨c,hCX c.property⟩,hc,hf c⟩

variable {G : Type*} [Group G] [Finite G]

/-- The original vertex has an actual pair-stabilizer isomorphism carrying L
onto the native edge fixer. Its restriction to the entire linear subgroup is
explicit, and the original completion map retains both parabolics and the Borel. -/
theorem Preparation.linear_nonmaximal_edge_marked_vertex
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ (e : (L ⊔ residual H : Subgroup G) ≃* Matrix.PSL3Four.PSL)
      (δ : MulAut Matrix.PSL3Four.PSL)
      (β : (L ⊔ H : Subgroup G) ≃* pairStabilizer),
      (((L.subgroupOf (L ⊔ residual H)).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F ∧
        ((residual H).subgroupOf (L ⊔ residual H)).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F) ∨
       (((residual H).subgroupOf (L ⊔ residual H)).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F ∧
        (L.subgroupOf (L ⊔ residual H)).map e.toMonoidHom =
          Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F)) ∧
      ((L ⊓ residual H).subgroupOf (L ⊔ residual H)).map e.toMonoidHom =
        Matrix.PSL3.LinearThree.borel Matrix.PSL3Four.F ∧
      (L.subgroupOf (L ⊔ H)).map β.toMonoidHom =
        standardSystem.edgeGroup.subgroupOf pairStabilizer ∧
      ((L ⊔ residual H).subgroupOf (L ⊔ H)).map β.toMonoidHom = pointwisePairStabilizer ∧
      ∀ c : (L ⊔ residual H : Subgroup G),
        β ⟨c,(sup_le le_sup_left ((map_subtype_le _).trans le_sup_right)) c.property⟩ =
          (PairPlane.pointwiseEquiv.symm (δ (e c))).val := by
  have hP := d.linear_nonmaximal_parabolic_eq h hH hp F hm hF he hnonmax 0
  have hQ := d.linear_nonmaximal_parabolic_eq h hH hp F hm hF he hnonmax 1
  change ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 = L at hP
  change ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 = residual H at hQ
  have hex := d.linear_nonmaximal_field_extension h hH hp F hm hF he hnonmax
  dsimp only at hex
  rw [hP,hQ] at hex
  obtain ⟨e,f,hPQ,hB,hf⟩ := hex
  let C := L ⊔ residual H
  let X := L ⊔ H
  have hCX : C ≤ X := sup_le le_sup_left ((map_subtype_le _).trans le_sup_right)
  have hX : C ⊔ (T : Subgroup G) = X := by
    change (L ⊔ residual H) ⊔ (T : Subgroup G) = L ⊔ H
    rw [sup_assoc,residual_sup_sylow T H hH.1.1.2]
  let fX : X ≃* Matrix.PSL3Four.FieldExtension :=
    (MulEquiv.subgroupCongr hX.symm).trans f
  have hfX (c : C) : fX ⟨c,hCX c.property⟩ = Matrix.PSL3Four.linearInclusion (e c) := hf c
  obtain ⟨b,hb⟩ : ∃ b : Bool, (L.subgroupOf C).map e.toMonoidHom =
      Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F b := by
    rcases hPQ with ⟨hl,_⟩ | ⟨_,hl⟩
    · exact ⟨true,hl⟩
    · exact ⟨false,hl⟩
  obtain ⟨a,δ,ha,hδ⟩ := SourceVertex.exists_edge_coordinates b
  let β : X ≃* pairStabilizer := fX.trans a
  let e' := e.trans δ
  have hβ (c : C) : β ⟨c,hCX c.property⟩ =
      (PairPlane.pointwiseEquiv.symm (e' c)).val := by
    change a (fX ⟨c,hCX c.property⟩) = _
    rw [hfX,hδ]
    rfl
  refine ⟨e,δ,β,hPQ,hB,?_,?_,hβ⟩
  · change (L.subgroupOf X).map (a.toMonoidHom.comp fX.toMonoidHom) = _
    rw [←Subgroup.map_map,map_of_restriction L C X le_sup_left hCX e fX _ hfX,hb,ha,
      standardSystem_edgeGroup]
  · ext z
    constructor
    · rintro ⟨c,hc,rfl⟩
      change (c : G) ∈ C at hc
      change β ⟨(⟨(c : G),hc⟩ : C),hCX hc⟩ ∈ pointwisePairStabilizer
      rw [hβ]
      exact (PairPlane.pointwiseEquiv.symm (e' ⟨c,hc⟩)).property
    · intro hz
      let c := e'.symm (PairPlane.pointwiseEquiv ⟨z,hz⟩)
      refine ⟨⟨c,hCX c.property⟩,c.property,?_⟩
      change β ⟨c,hCX c.property⟩ = z
      rw [hβ]
      change (PairPlane.pointwiseEquiv.symm (e' (e'.symm
        (PairPlane.pointwiseEquiv ⟨z,hz⟩)))).val = z
      rw [e'.apply_symm_apply,PairPlane.pointwiseEquiv.symm_apply_apply]

/-- Equip the same original coset system and heptad marking with a vertex
isomorphism preserving the edge fixer and the whole linear subgroup. No
agreement on Ix or its sixteen-core is asserted by this initial coordinate step. -/
theorem Preparation.linear_nonmaximal_coset_vertex_coordinates
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ J : Subgroup G, J ∈ Chapter1.LStar G (T : Subgroup G) ∧ residual H < J ∧
      ∃ (U : System G (G ⧸ (L ⊔ H : Subgroup G))) (ζ : J ≃* heptadStabilizer) (_hUJ : U.H ≤ J)
        (β : U.vertexGroup ≃* pairStabilizer),
      U.x = ((1 : G) : G ⧸ (L ⊔ H : Subgroup G)) ∧
      U.vertexGroup = L ⊔ H ∧ U.edgeGroup = L ∧
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      (U.H.subgroupOf J).map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.vertexGroup).subgroupOf J).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      ((U.H ⊓ U.edgeSetGroup).subgroupOf J).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      (∀ a b : J, a • U.x = b • U.x ↔ ζ a • x.val = ζ b • x.val) ∧
      (∃ t : J, (t:G) ∈ U.H ∧ t • U.x = U.y ∧ ζ t • x.val = y.val) ∧
      AutomorphismRigid (U.H.subgroupOf U.edgeGroup) ∧
      J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup ∧
      (∀ a : U.vertexGroup, (a : G) ∈ U.edgeGroup ↔
        (β a : Sporadic.Mathieu.M23) ∈ standardSystem.edgeGroup) ∧
      ((L ⊔ residual H).subgroupOf U.vertexGroup).map β.toMonoidHom =
        pointwisePairStabilizer := by
  obtain ⟨J,hJ,hKJ,U,ζ,hx,hv,he0,hUJ,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid⟩ :=
    d.linear_nonmaximal_rigid_coset_system h hH hp F hm hF he hnonmax
  have hcoreEdge : J.pCoreIn 2 ≤ U.H ⊓ U.edgeGroup := by
    rintro _ ⟨u,hu,rfl⟩
    have hz : ζ u ∈ heptadKernel := hcore ▸ mem_map_of_mem ζ.toMonoidHom hu
    have hm : ζ u ∈ ((U.H ⊓ U.edgeGroup).subgroupOf J).map ζ.toMonoidHom := by
      rw [hedgeM]
      exact heptadKernelAmbient_le_twoPair ⟨ζ u,hz,rfl⟩
    exact (mem_map_iff_mem (f := ζ.toMonoidHom) ζ.injective).mp hm
  obtain ⟨_,_,β₀,_,_,hβedge,hβlinear,_⟩ :=
    d.linear_nonmaximal_edge_marked_vertex h hH hp F hm hF he hnonmax
  let c := MulEquiv.subgroupCongr hv
  let β := c.trans β₀
  refine ⟨J,hJ,hKJ,U,ζ,hUJ,β,hx,hv,he0,hcore,hK,hHm,hMm,hIm,hvM,hedgeM,hesM,
    horbit,ht,hrigid,hcoreEdge,?_,?_⟩
  · intro a
    constructor
    · intro ha
      have hm : β a ∈ (L.subgroupOf (L ⊔ H)).map β₀.toMonoidHom := by
        refine ⟨c a,?_,rfl⟩
        change (a : G) ∈ L
        exact he0.le ha
      rw [hβedge] at hm
      exact hm
    · intro ha
      have hm : β₀ (c a) ∈ (L.subgroupOf (L ⊔ H)).map β₀.toMonoidHom := by
        rw [hβedge]
        exact ha
      rw [mem_map_equiv,β₀.symm_apply_apply] at hm
      rw [he0]
      exact hm
  · have hc : ((L ⊔ residual H).subgroupOf U.vertexGroup).map c.toMonoidHom =
        (L ⊔ residual H).subgroupOf (L ⊔ H) := by
      ext a
      rw [mem_map_equiv]
      rfl
    change ((L ⊔ residual H).subgroupOf U.vertexGroup).map
      (β₀.toMonoidHom.comp c.toMonoidHom) = _
    rw [←map_map,hc,hβlinear]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
