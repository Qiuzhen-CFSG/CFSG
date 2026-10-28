module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Selection
/-!
# An opposite conjugator inside the actual pair

The first-plane Weyl element belongs to the marked SL₂ pair and takes the
original point to the same opposite point as y. Lift it first to L, then to
I through the full action on V. The first adjustment lies in the point
normalizer; the second lies in O₂(LT). Both normalize the original W.
Thus W and Wʸ are conjugate inside I itself, as required to compare the two
factors of the literal quotient Q/((W∩Wʸ)V).

Source: Aschbacher--Smith, 11.5.7, printed p.783.
-/

open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open OppositeGeometry
private theorem conjugates_eq_of_difference_normalizes {G : Type*} [Group G]
    (W : Subgroup G) (a b : G) (h : b⁻¹*a ∈ normalizer (W : Set G)) :
    W.map (MulAut.conj a).toMonoidHom = W.map (MulAut.conj b).toMonoidHom := by
  have hn := mem_normalizer_iff_map_conj_eq.mp h
  change W.map (MulAut.conj (b⁻¹*a)).toMonoidHom = W at hn
  have he : (MulAut.conj b).toMonoidHom.comp (MulAut.conj (b⁻¹*a)).toMonoidHom =
      (MulAut.conj a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [← he,← map_map,hn]

private def firstOpposition {F : Type*} [Field F] [CharP F 2] : Sp F :=
  OppositeLongRootPair.embedding ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩

private theorem firstOpposition_mem {F : Type*} [Field F] [CharP F 2] :
    firstOpposition (F := F) ∈ OppositeLongRootPair.pair := by
  rw [← OppositeLongRootPair.embedding_range]
  exact ⟨_,rfl⟩

private theorem firstOpposition_point {F : Type*} [Field F] [CharP F 2] :
    (point F).map (toLinear (firstOpposition (F := F))).toLinearMap =
      (point F).map (toLinear (TwoConjugate.opposition (F := F))).toLinearMap := by
  rw [point,Submodule.map_span,Set.image_singleton,Submodule.map_span,Set.image_singleton]
  congr 2
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [firstOpposition,OppositeLongRootPair.embedding,OppositeLongRootPair.matrix,
      Theory.SpecificGroups.SymplecticFour.e,toLinear_apply,
      TwoConjugate.opposition]

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The opposite generators are conjugate inside the literal I. -/
theorem exists_inner_opposite_conjugator (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = LocalGeometry.Sp4.ModelFlag.movedStage g 1)
    (y : L) (hy : PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹)
    (hi : actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m)) :
    ∃ i ∈ oppositeJoin (auxiliaryW E) (y:G),
      (auxiliaryW E).map (MulAut.conj i).toMonoidHom =
        (auxiliaryW E).map (MulAut.conj (y:G)).toMonoidHom := by
  let c := LocalGeometry.Coordinates.sp4 m.action
  obtain ⟨z,hz⟩ := c.quotientMap_surjective (g * firstOpposition * g⁻¹)
  have hz' : PointModel.quotientMap m z = g * firstOpposition * g⁻¹ := hz
  have hpoints : E.V₁.map (MulAut.conj (z:G)).toMonoidHom =
      E.V₁.map (MulAut.conj (y:G)).toMonoidHom := by
    rw [m.point_preimage]
    change (c.preimage (m.flag.space 0)).map _ = (c.preimage (m.flag.space 0)).map _
    rw [← c.preimage_map_action,← c.preimage_map_action]
    congr 1
    change (m.flag.space 0).map (toLinear (PointModel.quotientMap m z)).toLinearMap =
      (m.flag.space 0).map (toLinear (PointModel.quotientMap m y)).toLinearMap
    rw [hz',hy,hpoint]
    change ((point E.input.field.Carrier).map (toLinear g).toLinearMap).map _ =
      ((point E.input.field.Carrier).map (toLinear g).toLinearMap).map _
    have he (b : Sp E.input.field.Carrier) :
        ((point E.input.field.Carrier).map (toLinear g).toLinearMap).map
          (toLinear (g*b*g⁻¹)).toLinearMap =
        ((point E.input.field.Carrier).map (toLinear b).toLinearMap).map (toLinear g).toLinearMap := by
      rw [← Submodule.map_comp,← Submodule.map_comp]
      congr 1
      apply LinearMap.ext
      intro v
      change (g*b*g⁻¹) • (g • v) = g • (b • v)
      simp only [mul_smul,inv_smul_smul]
    rw [he,he,firstOpposition_point]
  have hnorm : (y:G)⁻¹*(z:G) ∈ normalizer (E.V₁ : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change E.V₁.map (MulAut.conj ((y:G)⁻¹*(z:G))).toMonoidHom = E.V₁
    have he : (MulAut.conj (y:G)⁻¹).toMonoidHom.comp (MulAut.conj (z:G)).toMonoidHom =
        (MulAut.conj ((y:G)⁻¹*(z:G))).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [← he,← map_map,hpoints,map_map]
    have he' : (MulAut.conj (y:G)⁻¹).toMonoidHom.comp (MulAut.conj (y:G)).toMonoidHom =
        MonoidHom.id G := by ext x; simp [MulAut.conj_apply,mul_assoc]
    rw [he',map_id]
  have hzW := conjugates_eq_of_difference_normalizes (auxiliaryW E) (z:G) (y:G)
    (G₁_normalizes_auxiliaryW E hnorm)
  have hmem : FullAction.modelHom m (PointModel.quotientMap m z) ∈
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) := by
    rw [hi,hz']
    exact mem_map_of_mem _ (mem_map_of_mem (MulAut.conj g).toMonoidHom firstOpposition_mem)
  let J := L ⊔ (T : Subgroup G)
  have hIJ := oppositeJoin_le_large E m hW y.property
  rw [← largeAction_image E _ hIJ] at hmem
  obtain ⟨i,hiI,hiEq⟩ := hmem
  have hEq : largeAction E i = largeAction E ⟨z,mem_sup_left z.property⟩ := by
    rw [FullAction.modelHom_quotientMap] at hiEq
    exact hiEq
  have hk : i⁻¹ * ⟨z,mem_sup_left z.property⟩ ∈ (largeAction E).ker := by
    change largeAction E (i⁻¹ * ⟨z,mem_sup_left z.property⟩) = 1
    rw [map_mul,map_inv,hEq,inv_mul_cancel]
  have hcore : (i:G)⁻¹*(z:G) ∈ J.pCoreIn 2 :=
    (large_centralizer_eq_core E).le ⟨(i⁻¹ * ⟨z,mem_sup_left z.property⟩).property,
      (largeAction_ker E).le hk⟩
  have hiW := conjugates_eq_of_difference_normalizes (auxiliaryW E) (z:G) (i:G)
    ((large_core_normalizes_pair E m y.property).1 hcore)
  exact ⟨i,hiI,hiW.symm.trans hzW⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
