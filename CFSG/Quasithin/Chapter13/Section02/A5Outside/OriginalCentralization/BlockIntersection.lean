module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreFrattini
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCenters

/-!
# The intersection of the two original block cores

Apply the short-block Frattini calculation separately in LT and KT=H.
The resulting Frattini images centralize L and K respectively. Their
intersection is contained in the common Sylow centralizer, which is trivial
by the original maximal-local uniqueness. Frattini functoriality now makes
the literal intersection of the two local cores elementary abelian.

The two Frattini images also commute, since each is normalized by T.
This concerns blocks in their separate original local groups; it does not
assume that L and K commute or are subnormal in their join. The actual
nonsolvable consumer is SourceAssembly/NonsolvableBlockIntersection.
Source: Aschbacher--Smith C.1.7--8, pp.123--124, 1.2.7, pp.506--507,
and the nonsolvable pair of 13.2.8(1), p.880.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The literal core Frattini images of two original blocks are disjoint. -/
theorem original_block_pair_frattini_disjoint
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hbL : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (hbK : IsBlock (K.subgroupOf H)) :
    Disjoint ((frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subtype)
      ((frattini (H.pCoreIn 2)).map (H.pCoreIn 2).subtype) := by
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hL := relative_core_frattini_centralizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hbL
  have hK := relative_core_frattini_centralizes
    ((show K ≤ K ⊔ (T : Subgroup G) from le_sup_left).trans_eq hjoin) hbK
  apply disjoint_iff.mpr
  apply bot_unique
  intro x hx
  exact (common_sylow_centralizer_eq_bot d hH e.normalizes_L hjoin).le
    ⟨⟨hQT ((map_subtype_le _) hx.1),hL hx.1⟩,hK hx.2⟩

/-- The intersection is elementary without a core-order or core-equality premise. -/
theorem original_block_pair_core_intersection_elementary
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hbL : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (hbK : IsBlock (K.subgroupOf H)) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 : Subgroup G) := by
  have hf := frattini_eq_bot_of_disjoint_images
    (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))) (isPGroup_pCoreIn 2 H)
    (show ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 from inf_le_left) inf_le_right
    (original_block_pair_frattini_disjoint d e hjoin hH hbL hbK)
  let : Fact (IsPGroup 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 : Subgroup G)) :=
    ⟨(isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le inf_le_left⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hf

/-- The disjoint Frattini images commute inside the same original Sylow. -/
theorem original_block_pair_frattini_commute
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hbL : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (hbK : IsBlock (K.subgroupOf H)) :
    ⁅(frattini ((L ⊔ (T : Subgroup G)).pCoreIn 2)).map
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subtype,
      (frattini (H.pCoreIn 2)).map (H.pCoreIn 2).subtype⁆ = ⊥ := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := H.pCoreIn 2
  let FQ := (frattini Q).map Q.subtype
  let FP := (frattini P).map P.subtype
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hPT : P ≤ (T : Subgroup G) :=
    map_le_iff_le_comap.mpr (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans
      ((L ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))))
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    hH.1.1.2.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hTFQ : (T : Subgroup G) ≤ normalizer (FQ : Set G) :=
    hTQ.trans (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  have hTFP : (T : Subgroup G) ≤ normalizer (FP : Set G) :=
    hTP.trans (normalizer_le_normalizer_characteristic_image P (frattini P))
  have hdis := original_block_pair_frattini_disjoint d e hjoin hH hbL hbK
  apply bot_unique
  exact (le_inf
    (le_normalizer_iff_commutator_le_left.mp (((map_subtype_le _).trans hPT).trans hTFQ))
    (le_normalizer_iff_commutator_le_right.mp (((map_subtype_le _).trans hQT).trans hTFP))).trans
      hdis.eq_bot.le

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
