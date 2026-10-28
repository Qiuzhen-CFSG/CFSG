module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingGeneratedSource
public import Theory.SpecificGroups.SymmetricFourWreath.NormalElementaryGeometry
/-!
# Relative indices of the original natural module and Thompson subgroup

The marked wreath Sylow model identifies the literal Borel residual core
intrinsically. The original natural module is normal, elementary of order
sixteen, and disjoint from the marked central factor. Its image modulo the
core and central factor has order two; the Thompson subgroup has image of
order four. Every placement and model premise is discharged from the
original MinimalBlockSetup.

Source: Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_core_relative_indices
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let R := (d.S : Subgroup d.H).map d.H.subtype
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    (P ⊔ D).relIndex (sourceModule (d.block.map d.H.subtype)) = 2 ∧
      (P ⊔ D).relIndex (elementaryAbelianMaxJ R) = 4 := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let Di := centralizer (d.block : Set d.H)
  let Ui := (blockU d.block).map d.block.subtype
  let U := sourceModule (d.block.map d.H.subtype)
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : Ui.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  obtain ⟨hdis,_,hDe,hcore,hDS⟩ :=
    d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA
  let : IsElementaryAbelian 2 Di := hDe
  obtain ⟨e,he⟩ := d.single_alternating_marked_ambient_sylow_model hG T hM hTM hu hST hsingle hA
  have hUi : Ui.map d.H.subtype = U :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hUS : Ui ≤ (d.S : Subgroup d.H) :=
    (le_sup_left.trans hcore.symm.le).trans (pCore_isPGroup.le_sylow_of_normal d.S)
  have hUR : U ≤ R := hUi ▸ map_mono hUS
  have hDm : Di.map d.H.subtype = D := d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA
  have hDR : D ≤ R := by
    rw [←hDm]
    exact map_mono hDS
  have hUd : Disjoint U D := by
    rw [←hUi,←hDm]
    exact disjoint_map d.H.subtype_injective hdis
  have hUn : R ≤ normalizer (U : Set G) := by
    have hi := Ui.le_normalizer_map d.H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hUi] at hi
    exact (map_subtype_le _).trans hi
  let : (U.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hUR).mpr hUn
  let : IsElementaryAbelian 2 (U.subgroupOf R) := by
    let := hA.2.1.elementary
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (d.block.map d.H.subtype).subtype
    exact IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hUR).toMonoidHom
      (subgroupOfEquivOfLe hUR).injective
  have hcU : Nat.card (U.subgroupOf R)=16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv]
    obtain ⟨_,eU,_⟩ := d.single_alternating_marked_action hsingle hA
    rw [←hUi,card_map_of_injective d.H.subtype_injective,Nat.card_congr eU.toEquiv,
      Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K:=ZMod 2),
      BinaryPermutation.finrank_core]
    norm_num
  obtain ⟨hPR,hRP⟩ := d.single_borel_core_placement hsingle
  let Q := P.subgroupOf R
  let eQ : Q ≃* P := subgroupOfEquivOfLe hPR
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer hPR).mpr hRP
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let hq := hp.map eQ.symm
  let : IsExtraspecial 2 Q := hq.extraspecial
  have hcQ : Nat.card Q=32 := (Nat.card_congr eQ.toEquiv).trans hp.card
  have hef : ((MonoidHom.fst SymmetricFourWreath.P Di).comp e.toMonoidHom).ker = D.subgroupOf R := by
    rw [he,d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA]
  have hd' : Disjoint (U.subgroupOf R)
      ((MonoidHom.fst SymmetricFourWreath.P Di).comp e.toMonoidHom).ker := by
    rw [hef]
    apply disjoint_def.mpr
    intro x hx hd
    exact Subtype.ext (disjoint_def.mp hUd hx hd)
  have hiU := SymmetricFourWreath.core_sup_factor_relIndex_normal_elementary e Q
    (U.subgroupOf R) hcQ inferInstance hcU hd'
  have hiJ := SymmetricFourWreath.core_sup_factor_relIndex_thompson e Q hcQ
  rw [hef,←subgroupOf_sup hPR hDR,relIndex_subgroupOf hUR] at hiU
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun A hA => hA.1
  have hjR : (elementaryAbelianMaxJ R).subgroupOf R =
      elementaryAbelianMaxJ (⊤:Subgroup R) := by
    apply map_injective (f:=R.subtype) R.subtype_injective
    rw [map_subgroupOf_eq_of_le hJR,
      ←elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
  rw [hef,←subgroupOf_sup hPR hDR,←hjR,
    relIndex_subgroupOf hJR] at hiJ
  exact ⟨hiU,hiJ⟩
end CFSG.Quasithin.Chapter2
