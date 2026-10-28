module

public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannProduct
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.GroupTheory.DihedralFourElementaryOrder
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The original zero-center module has largest elementary order

The two original alternating-five block layers each have order sixteen.
Their disjoint commuting product is the two-core, hence the source module
has order 256. Source saturation places it in the original Baumann subgroup.
The four-dihedral recognition bounds every elementary subgroup there by
256, so the actual source module belongs to the maximum-order family.
The final export transports that same module under a prescribed coordinate
marking for the canonical central-enlargement geometry.

Source: Aschbacher–Smith 10.2.1, pp.742–743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
set_option backward.isDefEq.respectTransparency false

/-- The two order-sixteen natural layers give the actual source module order. -/
theorem source_a5_zero_module_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card D.moduleSubgroup = 256 := by
  let H := localJoin T L
  let A := L.subgroupOf H
  obtain ⟨_,ha,_⟩ := source_a5_original_block_of_baumann_not_controlled D e hn hout
  obtain ⟨t,ht,hne,hcomm,horbit,hsplit,hkA,hkB,hjoint⟩ :=
    source_a5_zero_centralizer_pair_centralizers D e hn hout hz
  let B := A.map (MulAut.conj t).toMonoidHom
  have hb : IsAlternatingBlock B 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv ((MulAut.conj t).subgroupMap A) ha
  let K₁ := (blockU A).map A.subtype
  let K₂ := (blockU B).map B.subtype
  have hK₁ : K₁ ≤ centralizer (B : Set H) := by
    rw [show K₁ = pCore 2 H ⊓ centralizer (B : Set H) from hkA.symm]
    exact inf_le_right
  have hK₂ : K₂ ≤ centralizer (A : Set H) := by
    rw [show K₂ = pCore 2 H ⊓ centralizer (A : Set H) from hkB.symm]
    exact inf_le_right
  have hd : Disjoint K₁ K₂ :=
    disjoint_of_pair_centralizer_layers A B K₁ K₂ hK₁ hK₂ hjoint
  have hc : K₁ ≤ centralizer (K₂ : Set H) :=
    hK₁.trans (centralizer_le (map_subtype_le _))
  obtain ⟨f,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K₁ K₂ hd hc
  have hcard : Nat.card (pCore 2 H) = 256 := by
    rw [hsplit,←Nat.card_congr f.toEquiv,Nat.card_prod]
    change Nat.card ((blockU A).map A.subtype) * Nat.card ((blockU B).map B.subtype) = _
    rw [card_map_of_injective A.subtype_injective,card_map_of_injective B.subtype_injective,
      ha.blockU_card,hb.blockU_card]
  rw [source_a5_zero_centralizer_module_eq_core D e hn hout hz]
  change Nat.card ((pCore 2 H).map H.subtype) = 256
  rw [card_map_of_injective H.subtype_injective,hcard]

/-- Source saturation places the actual module in the original Baumann subgroup. -/
theorem source_a5_zero_module_le_baumann
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    D.moduleSubgroup ≤ ChapterB.baumann (T : Subgroup G) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hc := Subgroup.map_mono (f := H.subtype)
    (source_a5_zero_core_le_baumann D e hn hout hz)
  have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
  change (ChapterB.baumann (S : Subgroup H)).map H.subtype =
    ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
  have hs : (S : Subgroup H).map H.subtype = T :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
  rw [he,hs] at hc
  rw [source_a5_zero_centralizer_module_eq_core D e hn hout hz]
  exact hc

/-- The actual source module has maximum elementary order in Baum(T). -/
theorem source_a5_zero_module_maximum_elementary
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    D.moduleSubgroup ∈ elementaryAbelianMaxSubgroups (ChapterB.baumann (T : Subgroup G)) := by
  refine ⟨source_a5_zero_module_le_baumann D e hn hout hz,D.module_elementary,?_⟩
  intro E hER hE
  let := hE
  obtain ⟨f⟩ := source_a5_zero_original_baumann_dihedral_four_product D e hn hout hz
  have hbound := dihedral_four_elementary_card_le_of_equiv f
    (E.subgroupOf (ChapterB.baumann (T : Subgroup G))) (hE.subgroupOf hER)
  rw [Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv] at hbound
  rwa [source_a5_zero_module_card D e hn hout hz]


/-- The actual source module remains largest elementary, of order 256, under
any specified four-coordinate marking of the Baumann subgroup. -/
theorem source_a5_zero_module_maximum_coordinates
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥)
    (eR : ChapterB.baumann (T : Subgroup G) ≃* (Fin 4 → DihedralGroup 4)) :
    let V := (D.moduleSubgroup.subgroupOf (ChapterB.baumann (T : Subgroup G))).map
      eR.toMonoidHom
    V ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup (Fin 4 → DihedralGroup 4)) ∧
      Nat.card V = 256 := by
  let R := ChapterB.baumann (T : Subgroup G)
  have hVR : D.moduleSubgroup ≤ R := source_a5_zero_module_le_baumann D e hn hout hz
  have hmax := source_a5_zero_module_maximum_elementary D e hn hout hz
  have hs : D.moduleSubgroup.subgroupOf R ∈ elementaryAbelianMaxSubgroups
      (⊤ : Subgroup R) := by
    apply (maxFamily_map_injective_iff R.subtype R.subtype_injective ⊤ _).mp
    have hsub : (D.moduleSubgroup.subgroupOf R).map R.subtype = D.moduleSubgroup :=
      map_subgroupOf_eq_of_le hVR
    rw [hsub,←MonoidHom.range_eq_map,range_subtype]
    exact hmax
  constructor
  · have hm := (maxFamily_map_injective_iff eR.toMonoidHom eR.injective ⊤
      (D.moduleSubgroup.subgroupOf R)).mpr hs
    simpa only [map_top_of_surjective eR.toMonoidHom eR.surjective] using hm
  · change Nat.card ((D.moduleSubgroup.subgroupOf R).map eR.toMonoidHom) = 256
    rw [card_map_of_injective eR.injective,
      Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv,source_a5_zero_module_card D e hn hout hz]

end CFSG.Quasithin.Chapter10
