module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction.Action
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The inner residual image of the actual Y-action

The two-perfect subgroup Y_L is normal in Y_L(S ∩ L), with two-group
quotient, so it is that group's two-residual. Surjective residual transport
identifies its actual quotient image with the parabolic residual. When Y_C
centralizes L and Y = Y_L Y_C, the normalizer action of Y has precisely the
corresponding inner-automorphism image. No quotient map is applied to Y itself.

Source: Aschbacher–Smith, 15.3.23, printed pp.1128–1129, using C.2.7(3).
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
variable {G : Type*} [Group G]

private theorem residual_join (A B : Subgroup G)
    (hA : IsPPerfect 2 A) (hB : IsPGroup 2 B)
    (hn : B ≤ normalizer (A : Set G)) :
    (pResidual 2 (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype = A := by
  let H := A ⊔ B
  let : (A.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have ha : IsPPerfect 2 (A.subgroupOf H) :=
    hA.of_surjective (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).symm.surjective
  have hsup : A.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup (show A ≤ H from le_sup_left) (show B ≤ H from le_sup_right)]
    exact subgroupOf_self H
  change (pResidual 2 H).map H.subtype = A
  rw [pResidual_eq_of_isPPerfect_sup (A.subgroupOf H) (B.subgroupOf H) ha
    hB.comap_subtype hsup, map_subgroupOf_eq_of_le (show A ≤ H from le_sup_left)]

variable [Finite G]

/-- Two-perfectness, normalization and the parabolic image determine Y_L’s image. -/
theorem YL_image (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (hSYL : d.S ≤ normalizer (YL d L : Set G)) (M : Subgroup SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map (quotientMap L e) = M) :
    ((YL d L).subgroupOf L).map (quotientMap L e) = residual M := by
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hp := ComponentIntersection.intersectionResidual_isPPerfect d.Yplus L
  have hA : IsPPerfect 2 ((YL d L).subgroupOf L) :=
    hp.of_surjective (subgroupOfEquivOfLe hAL).symm.toMonoidHom
      (subgroupOfEquivOfLe hAL).symm.surjective
  have hB : IsPGroup 2 (d.S ⊓ L : Subgroup G) :=
    d.T.isPGroup'.to_le (inf_le_left.trans (show d.S ≤ (d.T : Subgroup G) from inf_le_left))
  have hn : (d.S ⊓ L).subgroupOf L ≤ normalizer (((YL d L).subgroupOf L : Subgroup L) : Set L) :=
    (comap_mono (inf_le_left.trans hSYL)).trans (le_normalizer_comap L.subtype)
  have hr := residual_join ((YL d L).subgroupOf L) ((d.S ⊓ L).subgroupOf L)
    hA hB.comap_subtype hn
  rw [← subgroupOf_sup hAL inf_le_right] at hr
  have ht := map_embedded_pResidual 2 ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L) (quotientMap L e)
  rw [hr, hM] at ht
  exact ht

omit [Finite G] in
/-- Subgroups contained in L have the expected inner-action image. -/
theorem action_image_of_le (L A : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL) (hAL : A ≤ L) :
    (A.subgroupOf (normalizer (L : Set G))).map (action L e) =
      ((A.subgroupOf L).map (quotientMap L e)).map MulAut.conj := by
  ext α
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨quotientMap L e ⟨n,hAL hn⟩, mem_map_of_mem _ hn, ?_⟩
    exact (action_inner L e ⟨n,hAL hn⟩).symm
  · rintro ⟨_, ⟨l,hl,rfl⟩, rfl⟩
    exact ⟨⟨l, L.le_normalizer l.property⟩, hl, action_inner L e l⟩

/-- The actual Y-action has the inner parabolic residual as its full image. -/
theorem action_image_Y (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL)
    (hY : d.Y = YL d L ⊔ YC d L)
    (hC : YC d L ≤ centralizer (L : Set G))
    (hSYL : d.S ≤ normalizer (YL d L : Set G)) (M : Subgroup SL)
    (hM : ((YL d L ⊔ (d.S ⊓ L)).subgroupOf L).map (quotientMap L e) = M) :
    (d.Y.subgroupOf (normalizer (L : Set G))).map (action L e) =
      (residual M).map MulAut.conj := by
  have hAL : YL d L ≤ L :=
    (ComponentIntersection.intersectionResidual_le _ _).trans inf_le_right
  have hAN := hAL.trans L.le_normalizer
  have hCN := hC.trans (Subgroup.centralizer_le_normalizer _)
  have hzero : ((YC d L).subgroupOf (normalizer (L : Set G))).map (action L e) = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨n,hn,rfl⟩
    exact action_centralizer L e n (hC hn)
  rw [hY, subgroupOf_sup hAN hCN, Subgroup.map_sup, hzero, sup_bot_eq,
    action_image_of_le L (YL d L) e hAL, YL_image d L e hSYL M hM]

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
