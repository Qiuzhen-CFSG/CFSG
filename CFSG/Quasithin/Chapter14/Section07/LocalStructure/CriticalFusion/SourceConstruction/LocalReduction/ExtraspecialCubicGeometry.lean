module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicLocalStructure
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# The action kernel of the original cubic completion

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the Sylow-central seed makes the
literal conjugation quotient D/C_D(W) two-reduced. In the normal-point
branch, the plane-span obstruction shows that Y's image does not normalize
L₂'s image under the actual quotient map.

Both local residuals act nontrivially on W. The Goldschmidt intersection
lemma then gives C_T(W) = O₂(D). The application constructs this geometry
from the original order-four chief interval, retaining its escaping cubic,
normalization of L₁, and exact star kernel.

These are the initial geometric and kernel steps of the containment
argument. Solvability of D and the later exclusions proving 14.5.3(2)
remain necessary; the small interval is not excluded here.

Source: Aschbacher–Smith, 14.5.6 and 14.5.7(2--3), printed p.1014,
B.2.14, printed p.78, and 14.7.20(2), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual point span has two-reduced conjugation action in the generated
local group, as required by source 14.5.7(3). -/
theorem cubic_generated_span_reduced
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Theory.GroupTheory.IsPReduced 2 ((conjugateSpanBy (F.Vi 1) D).subgroupOf D) := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  have hh := (cubic_generated_local_structure h hab structural previous Y hYH he).1
  apply Theory.GroupTheory.reduced_conjugateSpan_of_sylow_central T
  · exact le_sup_right.trans le_sup_right
  · exact (F.le_seed 1).trans h.chosen.le_sylow
  · exact le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  · exact (Theory.GroupTheory.inf_centralizer_pCoreIn_le_iff 2 _).mp hh

/-- In the literal action quotient D/C_D(W), the escaping cubic does not
normalize the original plane residual image. This is source 14.5.6 in the
normal-point branch, with the actual quotient map. -/
theorem cubic_generated_action_normalizer_obstruction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hWD : W ≤ D := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans le_sup_right)))
  have hC : C.map D.subtype = D ⊓ centralizer (W : Set G) := by
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWD]
  change ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _)
  intro him
  have hpre := map_le_iff_le_comap.mp him
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective C),
    comap_map_eq,QuotientGroup.ker_mk'] at hpre
  have hh := (map_mono (f := D.subtype) hpre).trans (le_normalizer_map D.subtype)
  rw [map_subgroupOf_eq_of_le hYD,Subgroup.map_sup,map_subgroupOf_eq_of_le hXD,hC] at hh
  exact cubic_plane_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout hh

/-- The original full point-normality interface. -/
theorem cubic_generated_action_normalizer_obstruction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  apply cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH _ hout
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The Sylow centralizer of the literal point span is the generated group's
own two-core. This is the kernel equality in source 14.5.7(2). -/
theorem cubic_generated_sylow_centralizer_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  let C := centralizer (W.subgroupOf D : Set D)
  have hPD : F.P L ≤ D := le_sup_left
  have hBD : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans hBD
  have hYD : Y ≤ D := le_sup_left.trans hBD
  have hXD : F.Li L 2 ≤ D := by
    apply le_trans _ hPD
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hC : C.map D.subtype = D ⊓ centralizer (W : Set G) := by
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWD]
  have hRA : ((pResidual 2 A).map A.subtype).map D.subtype = F.Li L 2 := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPD,
      plane_parabolic_residual h structural]
  have hRB : ((pResidual 2 B).map B.subtype).map D.subtype = Y := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBD]
    exact embedded_pResidual_join_pGroup Y _ hYp T.isPGroup' hYT
  have hXA : ¬ (pResidual 2 A).map A.subtype ≤ C := by
    intro hle
    have hXC : F.Li L 2 ≤ centralizer (W : Set G) := by
      have hh := map_mono (f := D.subtype) hle
      rw [hRA,hC] at hh
      exact hh.trans inf_le_right
    have hXpoint : F.Li L 2 ≤ normalizer (F.Vi 1 : Set G) :=
      (hXC.trans (centralizer_le (le_conjugateSpanBy _ _))).trans
        (Subgroup.centralizer_le_normalizer _)
    have heq : F.Vi 2 ≤ F.Vi 1 := by
      rw [←plane_eq_point_residual_span h structural]
      exact conjugateSpanBy_le le_rfl hXpoint
    have hc := card_le_of_le heq
    rw [F.card 2 (by decide),F.card 1 (by decide)] at hc
    norm_num at hc
  have hYB : ¬ (pResidual 2 B).map B.subtype ≤ C := by
    intro hle
    have hh := map_mono (f := D.subtype) hle
    rw [hRB,hC] at hh
    apply cubic_plane_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
    exact hh.trans (le_sup_right.trans (F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G))).le_normalizer)
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hAC : A ⊓ C ≤ (pCore 2 A).map A.subtype :=
    (ht.left_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr hXA
  have hBC : B ⊓ C ≤ (pCore 2 B).map B.subtype :=
    (ht.right_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr hYB
  have hinter : A ⊓ B = (T : Subgroup G).subgroupOf D := by
    have hle : A ⊓ B ≤ (T : Subgroup G).subgroupOf D := by
      intro x hx
      have hh : (x : G) ∈ F.P L ⊓ F.H := ⟨hx.1,(sup_le hYH (F.invariant 1)) hx.2⟩
      rwa [plane_parabolic_inf_point h structural] at hh
    apply le_antisymm hle
    intro x hx
    exact ⟨F.binary_sylow_le_P L hx,(le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hx⟩
  have hlow := ht.normal_intersection_le_twoCore C hAC hBC
  rw [hinter] at hlow
  have hQC := (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.2.2
  have hQT : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hh
  change (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2
  apply le_antisymm
  · intro x hx
    have hc : (⟨x,hTD hx.1⟩ : D) ∈ C := by
      intro w hw
      exact Subtype.ext (hx.2 w hw)
    exact mem_map_of_mem D.subtype (hlow ⟨hx.1,hc⟩)
  · exact le_inf hQT (le_centralizer_iff.mp hQC)

/-- The original full point-normality interface. -/
theorem cubic_generated_sylow_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2 := by
  apply cubic_generated_sylow_centralizer_of_normalizes_point h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement in
/-- The actual order-four interval supplies the source 14.5.5--7 geometry,
with the same escaping cubic, star kernel, quotient, and point span. -/
theorem extraspecial_four_interval_cubic_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D) ∧
      pCore 2 D ≠ ⊥ ∧ D ∈ Chapter1.He G ∧ IsSQTK KnownSimple.IsKnownSimple D ∧
      IsElementaryAbelian 2 W ∧ W ≤ D.pCoreIn 2 ∧
      W ≤ centralizer (D.pCoreIn 2 : Set G) ∧
      Theory.GroupTheory.IsPReduced 2 (W.subgroupOf D) ∧
      (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2 ∧
      ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) ∧
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
      ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hHe,hSQ,hW,hWQ,hWC⟩ := cubic_generated_local_structure h hab structural previous Y hYH he
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,
    cubic_goldschmidt_triple h structural Y hYH he,
    cubic_generated_core_ne_bot h hab structural previous Y hYH he,
    hHe,hSQ,hW,hWQ,hWC,
    cubic_generated_span_reduced h hab structural previous Y hYH he,
    cubic_generated_sylow_centralizer h hab structural previous hn Y hYH hYp hYT hout he,
    cubic_plane_normalizer_obstruction h structural hn Y hYH hout,
    cubic_generated_action_normalizer_obstruction h structural hn Y hYH hout⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
