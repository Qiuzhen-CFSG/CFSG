module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.CoreIndex
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.QKPlacement.SourceCompletion

/-!
# Earlier normalizer and Sylow inputs for the original roots

The residual/Sylow supplement puts L ∩ H inside L₁T, and the proved
normalizer of V then identifies N_H(V) with L₁T. Transporting the actual
upper-unipotent Sylow of SL₂(4) through the original marking proves that
the two-core of L₁* is Sylow in K*. Thus neither input to the subsequent
root construction is an additional source premise.

Source: Aschbacher–Smith 14.7.64, 14.7.67 and the opening of 14.7.73,
printed pp.1069, 1071 and 1076.
-/

public section
noncomputable section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
private theorem left_intersection_le
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    L ⊓ F.H ≤ F.Li L 1 ⊔ (T : Subgroup G) := by
  let N := L ⊓ F.H
  let J := N ⊔ (T : Subgroup G)
  have hTN : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    (le_inf (d.natural.sylow_normalizes structural)
      ((F.invariant 1).trans F.H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  let : (N.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le N.le_normalizer hTN)
  obtain ⟨R, hR⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal (N.subgroupOf J)
  have hs := congrArg (fun B : Subgroup (N.subgroupOf J) =>
    (B.map (N.subgroupOf J).subtype).map J.subtype) (pResidual_sup_sylow_eq_top R)
  rw [Subgroup.map_sup, Subgroup.map_sup, map_embedded_pResidual,
    map_subgroupOf_eq_of_le (show N ≤ J from le_sup_left),
    ← MonoidHom.range_eq_map, range_subtype,
    map_subgroupOf_eq_of_le (show N ≤ J from le_sup_left), hR, subgroupOf_map_subtype] at hs
  apply le_trans hs.symm.le
  apply sup_le
  · have he : F.Li L 1 = (pResidual 2 N).map N.subtype := by
      simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, if_false]
      rfl
    rw [← he]
    exact le_sup_left
  · exact (map_mono inf_le_left).trans (by
      rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)]
      exact le_sup_right)

theorem source_point_normalizer
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) :
    F.H ⊓ normalizer (V : Set G) = F.Li L 1 ⊔ (T : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ ((T : Subgroup G) : Set G) * (L : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ (d.natural.sylow_normalizes structural),
        sup_comm, d.lemma_14_7_67_five sep]
      exact hx.2
    obtain ⟨t,ht,l,hl,he⟩ := hx'
    have hlH : l ∈ F.H := by
      have h := F.H.mul_mem (F.H.inv_mem (F.invariant 1 ht)) hx.1
      rwa [← he, inv_mul_cancel_left] at h
    rw [← he]
    exact mul_mem (mem_sup_right ht) (left_intersection_le d structural ⟨hl,hlH⟩)
  · apply sup_le
    · exact le_inf ((F.Li_le L 1).trans inf_le_right)
        (((F.Li_le L 1).trans inf_le_left).trans d.natural.chosen.normalizes)
    · exact le_inf (F.invariant 1) (d.natural.sylow_normalizes_seed structural)

private theorem marked_star (A : Subgroup G) :
    (star F A).map d.model.toMonoidHom = (A.subgroupOf F.H).map d.qH := by
  rw [CriticalFusion.Source.star, map_map]
  rfl

theorem source_starred_sylow (hb : CompatibleBorel d) :
    Geometry.Images.EarlierSylow (L := L) (F := F) := by
  apply (Geometry.Images.earlierSylow_iff (L := L) (F := F)).mpr
  apply (Chapter1.IsSylowIn.map_iff d.model.toMonoidHom d.model.injective).mp
  rw [map_pCoreIn_of_injective 2 _ _ d.model.injective, marked_star, hb.left_image,
    borel_twoCore, marked_star, d.K_image]
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow SL2FourNatural.F 2
  have hp : Chapter1.IsSylowIn 2 (P : Subgroup SL2FourNatural.SL) ⊤ :=
    Chapter1.isSylowIn_iff.mpr ⟨P.isPGroup',le_top,fun _ hA hPA _ => P.is_maximal' hA hPA⟩
  have hm := (Chapter1.IsSylowIn.map_iff (markingHom d.naturalQuotient)
    (markingHom_injective d.naturalQuotient)).mpr hp
  have ht : (⊤ : Subgroup SL2FourNatural.SL).map (markingHom d.naturalQuotient) =
      alternatingGroup (Fin 5) := by
    rw [markingHom, ← map_map, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr d.naturalQuotient.marking.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [ht] at hm
  exact hm

theorem source_geometry_earlier
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (sep : d.ModuleSeparation) (mark : UpperMarking d) : Geometry.Images.Earlier d where
  sylow_normalizes := d.natural.sylow_normalizes structural
  separation := sep
  point_normalizer := source_point_normalizer d structural sep
  sylow := source_starred_sylow d (compatibleBorel_of_upperMarking d structural mark)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.SourceCompletion
