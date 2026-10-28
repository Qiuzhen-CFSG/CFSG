module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# The normal closure of a natural A₅ layer inside a two-core

When a full Sylow normalizes an A₅ block, the ambient two-core normalizes
the same block. If it contains U(L), the projective natural-module split
identifies the normal closure of U(L) as U(L) times its L-centralizer.
The closure is elementary abelian and central in the ambient two-core,
and the two factors meet trivially. In characteristic two, the same split
also forces O₂(L) into the ambient two-core.

Source: Aschbacher–Smith 10.2.1, printed p.743, using C.1.13(c).
The module and normal closure are the original embedded subgroups.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_commutator {L P : Subgroup G} (hp : IsPGroup 2 P)
    (hLP : L ≤ normalizer (P : Set G)) (hPL : P ≤ normalizer (L : Set G)) :
    ⁅L,P⁆ ≤ L.pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
    (hp.to_le (le_normalizer_iff_commutator_le_right.mp hLP))
    (le_normalizer_iff_commutator_le_left.mp hPL)
    (normalizer_commutator_ge_left L P)

/-- Characteristic two forces the full block core into the ambient core. -/
theorem IsAlternatingBlock.core_le_ambient_core_of_layer_le (L : Subgroup G) (h : IsAlternatingBlock L 5)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hU : (blockU L).map L.subtype ≤ pCore 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    L.pCoreIn 2 ≤ pCore 2 G := by
  let U := (blockU L).map L.subtype
  have hPL : pCore 2 G ≤ normalizer (L : Set G) :=
    (pCore_isPGroup.le_sylow_of_normal T).trans hTL
  have hs := h.two_subgroup_eq_module_sup_centralizer pCore_isPGroup
    le_normalizer_of_normal hU (core_commutator pCore_isPGroup le_normalizer_of_normal hPL)
  apply le_trans ?_ hchar
  apply le_centralizer_iff.mpr
  rw [hs]
  apply sup_le
  · rintro u ⟨b,hb,rfl⟩ x ⟨a,ha,rfl⟩
    exact congrArg L.subtype (h.2.1.central hb a ha)
  · exact inf_le_right.trans (centralizer_le (pCoreIn_le 2 L))

/-- The original normal closure is elementary, central in O₂, and splits over the original layer. -/
theorem IsAlternatingBlock.normalClosure_layer_split (L : Subgroup G) (h : IsAlternatingBlock L 5)
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hU : (blockU L).map L.subtype ≤ pCore 2 G) :
    let U := (blockU L).map L.subtype
    let W := normalClosure (U : Set G)
    W ≤ pCore 2 G ∧ W ≤ centralizer (pCore 2 G : Set G) ∧
    IsElementaryAbelian 2 W ∧
    W = U ⊔ (W ⊓ centralizer (L : Set G)) ∧
    U ⊓ (W ⊓ centralizer (L : Set G)) = ⊥ := by
  let U := (blockU L).map L.subtype
  let W := normalClosure (U : Set G)
  have hPL : pCore 2 G ≤ normalizer (L : Set G) :=
    (pCore_isPGroup.le_sylow_of_normal T).trans hTL
  have hUP : U ≤ centralizer (pCore 2 G : Set G) := le_centralizer_iff.mp
    (h.2.1.normalizing_twoGroup_centralizes_blockU pCore_isPGroup
      le_normalizer_of_normal hPL)
  have hWP : W ≤ pCore 2 G := normalClosure_le_normal hU
  have hWC : W ≤ centralizer (pCore 2 G : Set G) := normalClosure_le_normal hUP
  let : IsElementaryAbelian 2 U := h.2.1.elementary.map L.subtype
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hWC.trans (centralizer_le hWP))
  have he : IsElementaryAbelian 2 W := IsElementaryAbelian.normalClosure_of_isMulCommutative U
  refine ⟨hWP,hWC,he,?_,?_⟩
  · exact h.two_subgroup_eq_module_sup_centralizer (pCore_isPGroup.to_le hWP)
      le_normalizer_of_normal le_normalClosure
      (core_commutator (pCore_isPGroup.to_le hWP) le_normalizer_of_normal (hWP.trans hPL))
  · apply bot_unique
    rintro x ⟨⟨a,ha,rfl⟩,_,hc⟩
    have hac : a ∈ center L := mem_center_iff.mpr fun l => Subtype.ext (hc l l.property)
    have hz : blockU L ⊓ center L = ⊥ := by
      rw [←blockFixed_map,h.blockFixed_eq_bot,Subgroup.map_bot]
    have ha1 : a=1 := mem_bot.mp (hz ▸ (show a ∈ blockU L ⊓ center L from ⟨ha,hac⟩))
    rw [ha1]
    exact one_mem _

end CFSG.Quasithin.ChapterC
