module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedSylowSource
public import Theory.GroupTheory.CentralFactorConjugateBound
/-!
# The order-two bound on the original block centralizer

The source C.5.6 conjugator moves C_T(L) to a disjoint conjugate and
normalizes its product with the Borel extraspecial core. The center-product
estimate bounds C_T(L) by the order-two center of that core. The original
natural quotient also proves the two factors disjoint and gives marked
multiplication coordinates on their direct product.

Source: Aschbacher–Smith 2.4.29, printed p.545.
-/
public section
namespace CFSG.Quasithin.Chapter2
open Subgroup ChapterC ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original Sylow centralizer of the alternating-five block has order at most two. -/
theorem MinimalBlockSetup.single_alternating_centralizer_card_le_two
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    Nat.card ((T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) : Subgroup G) ≤ 2 := by
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  have hDR : D ≤ R := by
    rw [show D = R ⊓ centralizer (d.block.map d.H.subtype : Set G) from
      d.single_block_sylow_centralizer T hST.le hsingle]
    exact inf_le_left
  have hDH : D ≤ d.H := hDR.trans (map_subtype_le _)
  have hPH : P ≤ d.H := (d.single_borel_core_placement hsingle).1.trans (map_subtype_le _)
  have hDc := (d.single_alternating_centralizer_source hG T hM hTM hu hST hsingle hA).1
  have hi := (d.single_alternating_sylow_index_source hG T hM hTM hu hST hsingle hA).1
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST.le hsingle hA
    (T : Subgroup G) hST.le le_rfl hi
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : d.H = d.block.map d.H.subtype ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : d.H ≤ normalizer (W : Set G))
      (hMW : (T : Subgroup G) ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hfull := ChapterC.Section06.original_core_eq_module_centralizer c h.block.2.1
  have hp := h.source_C56_single_block_7 hRK d.H (T : Subgroup G) R c.T_le c.R_normal hRK hH hno
    (hfull.trans (congrArg (fun A : Subgroup G => A.pCoreIn 2) hH)) x hx hi hnc
  have hd := hp.2.2.1
  rw [hp.2.2.2.1,←d.single_block_sylow_centralizer T hST.le hsingle] at hd
  have hn := (d.single_alternating_sylow_geometry hG T hM hTM hu hST hsingle hA).2.2
  have hb := card_central_factor_le_center_of_disjoint_conjugate P D
    (hDc.trans (centralizer_le hPH)) (hDc.trans (centralizer_le hDH)) x (hn hx) hd
  obtain ⟨hq⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  exact hb.trans_eq hq.center_card

/-- The original extraspecial core and block centralizer form a marked direct product. -/
theorem MinimalBlockSetup.single_alternating_core_centralizer_product
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    let B := M ⊓ d.block.map d.H.subtype
    let K := (pResidual 2 B).map B.subtype
    let P := K.pCoreIn 2
    let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
    ∃ e : P × D ≃* (P ⊔ D : Subgroup G),
      ∀ p c, (e (p,c) : G) = (p:G)*(c:G) := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let D := (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G)
  let Di := centralizer (d.block : Set d.H)
  let U := (blockU d.block).map d.block.subtype
  obtain ⟨q,e,hq,hker,hC,he⟩ := d.single_alternating_marked_action hsingle hA
  obtain ⟨_,hkL⟩ := d.single_alternating_residual_action hsingle q hq hker
  rw [d.single_block_core_intrinsic_source hG T hST hsingle] at hkL
  have hki : q.ker ⊓ d.block = U := by
    have hh := congrArg (map d.block.subtype) hkL
    change (q.ker.subgroupOf d.block).map d.block.subtype = U at hh
    rwa [subgroupOf_map_subtype] at hh
  have hDiq : Di ≤ q.ker := by
    rw [hC]
    exact centralizer_le (map_subtype_le _)
  have hUD := (d.single_alternating_centralizer_factor hG T hM hTM hu hST hsingle hA).1
  have hLd : Disjoint d.block Di := by
    apply disjoint_def.mpr
    intro a ha hd
    apply disjoint_def.mp hUD
    · change a ∈ U
      rw [←hki]
      exact ⟨hDiq hd,ha⟩
    · exact hd
  have hLD := disjoint_map d.H.subtype_injective hLd
  rw [d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA] at hLD
  have hPL : P ≤ d.block.map d.H.subtype :=
    (pCoreIn_le 2 K).trans ((map_subtype_le _).trans inf_le_right)
  exact exists_mulEquiv_prod_sup_of_disjoint_of_commuting P D (hLD.mono_left hPL)
    (le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hPL)))

end CFSG.Quasithin.Chapter2
