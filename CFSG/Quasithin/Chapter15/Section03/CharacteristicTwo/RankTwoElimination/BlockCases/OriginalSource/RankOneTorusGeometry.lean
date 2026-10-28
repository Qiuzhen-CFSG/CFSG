module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneA5
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import Theory.GroupTheory.SylowCentralizerComplement

/-!
# The actual natural block inside the rank-two span

The noncentral span W_L is an elementary normal subgroup of LR. The short
block support theorem identifies [W_L,L] with the literal U(L). Averaging
its Sylow-fixed seed gives W_L = U(L) C_{W_L}(L), preserving the possible
central covering layers. These are the geometric inputs shared by the
field restriction and exchanged-plane argument in original15.3.18.

Source: Aschbacher--Smith B.2.14 and15.3.18, pp.78,1126--1127.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem natural_block_support
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hRL : d.R ≤ normalizer (c.L : Set G))
    (hW : IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R))
    (hWL : d.componentSpan c.L ≤ c.L ⊔ d.R)
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hs : IsShort c.L) :
    (blockU c.L).map c.L.subtype = ⁅d.componentSpan c.L,c.L⁆ := by
  let J := c.L ⊔ d.R
  let L := c.L.subgroupOf J
  let W := (d.componentSpan c.L).subgroupOf J
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hRL)
  let : W.Normal := hW.normal
  let : IsElementaryAbelian 2 W := hW.elementary
  let e : L ≃* c.L := subgroupOfEquivOfLe (show c.L ≤ J from le_sup_left)
  have hb : IsBlock L := ⟨inferInstance,hs.of_mulEquiv e.symm,(inferInstance : L.Normal).isSubnormal⟩
  have hm : ⁅W,L⁆.map J.subtype = ⁅d.componentSpan c.L,c.L⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hWL,
      map_subgroupOf_eq_of_le (show c.L ≤ J from le_sup_left)]
  have hn : ⁅W,L⁆ ≠ ⊥ := by
    intro he
    have he' : ⁅d.componentSpan c.L,c.L⁆ = ⊥ := by rw [←hm,he,Subgroup.map_bot]
    apply c.outside
    exact (le_centralizer_iff.mp
      ((le_conjugateSpanBy d.V c.L).trans
        (commutator_eq_bot_iff_le_centralizer.mp he'))).trans hC
  have h := congrArg (map J.subtype)
    (RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator L W hb hn)
  rw [hm] at h
  have hu : ((blockU L).map L.subtype).map J.subtype = (blockU c.L).map c.L.subtype := by
    have he : (blockU L).map e.toMonoidHom = blockU c.L := by
      rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective]
      rfl
    rw [map_map]
    change (blockU L).map (c.L.subtype.comp e.toMonoidHom) = _
    rw [←map_map,he]
  exact hu.symm.trans h

theorem natural_block_span_split
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hRL : d.R ≤ normalizer (c.L : Set G))
    (hR : d.R = (d.T : Subgroup G) ⊓ centralizer (d.V : Set G))
    (hSyl : Chapter1.IsSylowIn 2 d.R (c.L ⊔ d.R))
    (hs : IsShort c.L)
    (hU : (blockU c.L).map c.L.subtype = ⁅d.componentSpan c.L,c.L⁆) :
    d.componentSpan c.L = (blockU c.L).map c.L.subtype ⊔
      (d.componentSpan c.L ⊓ centralizer (c.L : Set G)) := by
  let U := (blockU c.L).map c.L.subtype
  let W := d.componentSpan c.L
  have hUW : U ≤ W := hU.le.trans
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy d.V c.L))
  have hLN : c.L ≤ normalizer (U : Set G) :=
    c.L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image c.L (blockU c.L))
  let : IsElementaryAbelian 2 (blockU c.L) := hs.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map c.L.subtype
  let : (c.L.subgroupOf (c.L ⊔ d.R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hRL)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (show c.L ≤ c.L ⊔ d.R from le_sup_left)
    (inferInstance : (c.L.subgroupOf (c.L ⊔ d.R)).Normal).isSubnormal
  have hV : d.V ≤ U ⊔ (W ⊓ centralizer (c.L : Set G)) := by
    intro v hv
    obtain ⟨u,hu,hc⟩ := fixed_coset_of_sylow c.L U hLN
      (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) P v
      (fun l hl => by
        change ⁅l,v⁆ ∈ (blockU c.L).map c.L.subtype
        rw [hU,commutator_comm]
        exact commutator_mem_commutator hl (le_conjugateSpanBy d.V c.L hv))
      (fun p hp => (V_le_center_R d hR hv).2 p ((hP ▸ mem_map_of_mem c.L.subtype hp).1))
    have hh := mul_mem_sup (U.inv_mem hu)
      (show u*v ∈ W ⊓ centralizer (c.L : Set G) from
        ⟨W.mul_mem (hUW hu) (le_conjugateSpanBy d.V c.L hv),hc⟩)
    simpa only [inv_mul_cancel_left] using hh
  apply le_antisymm ?_ (sup_le hUW inf_le_left)
  apply conjugateSpanBy_le hV
  apply le_normalizer_iff.mpr
  intro l hl x hx
  have hCW : c.L ≤ normalizer ((W ⊓ centralizer (c.L : Set G) : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_conjugateSpanBy d.V c.L)
      (c.L.le_normalizer.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  exact ((normalizer_inf_normalizer_le_normalizer_sup U
    (W ⊓ centralizer (c.L : Set G))) ⟨hLN hl,hCW hl⟩ x).mp hx
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
