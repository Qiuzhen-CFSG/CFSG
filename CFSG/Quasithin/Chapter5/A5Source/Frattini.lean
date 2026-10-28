module
public import CFSG.Quasithin.Chapter5.A5Source.ConjugateCore
public import Theory.Frattini.Intersection
public import Theory.Frattini.CentralElementarySupplement

/-!
# Vanishing of the original core Frattini subgroup after crossing

The actual source product Q=V C_S(L) gives Φ(Q)=Φ(C_S(L)). If C_S(L)
lies in Q^g, functoriality puts this subgroup in its conjugate; equal orders
force equality. It is LT-normal, so the original escaping g contradicts
local uniqueness unless it is trivial. This is the paragraph following
C_S(L)≤Q^g in source5.1.7(1), printed p.633.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB ChapterC
open ChapterC.Section05.CounterexampleCharacteristic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem baumann_core_elementary_of_crossing
    (hout : ¬normalizer (baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : g ∉ normalizer (L : Set G))
    (hcross : baumann (T : Subgroup G) ⊓ centralizer (L : Set G) ≤
      ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2).map (MulAut.conj g⁻¹).toMonoidHom) :
    IsElementaryAbelian 2 ((L ⊔ baumann (T : Subgroup G)).pCoreIn 2) := by
  let S := baumann (T : Subgroup G)
  let Q := (L ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (L : Set G)
  let W := (frattini D).map D.subtype
  let e := MulAut.conj g⁻¹
  have hQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 _
  have hQD : Q = V ⊔ D := baumann_core_product_of_escape d hout
  have hVQ : V ≤ centralizer (Q : Set G) := by
    obtain ⟨_,hb,hV,_⟩ := alternating_block_of_baumann_escape d hout
    have he := ReducedMarking.normal_short_extension_centralizer L S hb.2.1
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
      (inf_le_left.trans d.normalizes_L)
    apply le_centralizer_iff.mp
    rw [←hV]
    exact he.ge.trans inf_le_right
  have hphi : (frattini Q).map Q.subtype = W :=
    frattini_map_eq_of_central_elementary_supplement Q D V hQ d.elementary hVQ hQD
  have hle : W ≤ W.map e.toMonoidHom := by
    have hi := frattini_image_le_of_le hcross (hQ.map e.toMonoidHom)
    rw [frattini_image_map _ e.toMonoidHom e.injective,hphi] at hi
    exact hi
  have he : W.map e.toMonoidHom = W := eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective e.injective]) |>.symm
  have hWD : W ≤ D := map_subtype_le _
  have hWT : W ≤ (T : Subgroup G) := hWD.trans (inf_le_left.trans inf_le_left)
  have hTN : (T : Subgroup G) ≤ normalizer (D : Set G) := by
    have hS := (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
    exact (le_inf hS (d.normalizes_L.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hLN : L ≤ normalizer (W : Set G) :=
    ((le_centralizer_iff.mp (hWD.trans inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  have hWN : (W.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le hLN
      (hTN.trans (normalizer_le_normalizer_characteristic_image D (frattini D))))
  have hW : W = ⊥ := by
    by_contra hne
    have hN := normalizer_of_local_normal d W hne hWT hWN
    have hgm : g⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
    apply hg
    simpa only [inv_inv] using (normalizer (L : Set G)).inv_mem (hN hgm)
  have hbot : frattini Q = ⊥ := (map_eq_bot_iff_of_injective _ Q.subtype_injective).mp
    (hphi.trans hW)
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (R := Q) (p := 2)).mp hbot
end CFSG.Quasithin.Chapter5.A5Source
