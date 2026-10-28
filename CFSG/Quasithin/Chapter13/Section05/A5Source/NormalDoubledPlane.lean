module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalPlaneModel
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrders
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ExtendedAffinePlane

/-!
# The literal plane endpoint in the doubled normal A₅ source branch

The original plane order is 1,920 in the doubled branch, so the already marked
affine-plane source dichotomy selects the full symmetric-five extension.
The concrete extended-unitary affine comparison carries the original module,
central line and common Borel to the literal extended plane core, root and
overlap, all through one equivalence.

Source: Aschbacher--Smith 13.5.17, printed p.922, doubled branch LT≠L.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The original doubled plane endpoint, retaining the module, central
line and overlap, is the literal extended binary-unitary plane. -/
theorem source_normal_doubled_plane_unitary
    (hdoubled : L ⊔ (T : Subgroup G) ≠ L) :
    ∃ E : (L ⊔ (T : Subgroup G) : Subgroup G) ≃* Extension.plane 1 (Nat.le_refl 1),
      (V.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom = ExtendedAffinePlane.planeCore ∧
      (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map E.toMonoidHom = zpowers ExtendedAffinePlane.longRight ∧
      ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map E.toMonoidHom =
        (Extension.overlap 1 (Nat.le_refl 1)).subgroupOf (Extension.plane 1 (Nat.le_refl 1)) := by
  have hc : Nat.card (L ⊔ (T : Subgroup G) : Subgroup G) = 1920 := by
    rcases normal_local_orders d hA312 hH hU hn with ⟨_,_,hc⟩ | ⟨_,_,hc⟩
    · exfalso
      apply hdoubled
      exact (eq_of_le_of_card_ge le_sup_left (by
        rw [hc,normal_local_card d hA312 hH hU hn])).symm
    · exact hc
  rcases source_normal_plane_marked_models d hA312 hH hU hn with ⟨e,_,_,_⟩ | ⟨e,hV,hline,hB⟩
  · have hA : Nat.card BinaryPermutation.AlternatingFiveExtension.AlternatingModel = 960 := by
      rw [SemidirectProduct.card]
      have hV : Nat.card (Multiplicative (BinaryPermutation.core (Fin 5))) = 16 := by
        change Nat.card (BinaryPermutation.core (Fin 5)) = 16
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,BinaryPermutation.finrank_core]
        rfl
      rw [hV,nat_card_alternatingGroup,Nat.card_fin]
      rfl
    have he := Nat.card_congr e.toEquiv
    rw [hc,hA] at he
    contradiction
  · obtain ⟨f,hz,hR,hC⟩ := ExtendedAffinePlane.exists_marked_plane_equiv
    refine ⟨e.trans f,?_,?_,?_⟩
    · change (V.subgroupOf (L ⊔ (T : Subgroup G))).map (f.toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,hV,hR]
    · change (V₁.subgroupOf (L ⊔ (T : Subgroup G))).map (f.toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,hline,MonoidHom.map_zpowers]
      exact congrArg zpowers hz
    · change ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map (f.toMonoidHom.comp e.toMonoidHom) = _
      rw [←map_map,hB,hC]

end CFSG.Quasithin.Chapter13.Section05.A5Source
