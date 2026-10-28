module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicSolvableModels
public import Theory.GroupAction.MarkedCubicRecognition.PointPlane
public import Theory.GroupAction.QuotientConjugation

/-!
# Excluding the marked Heisenberg cubic completion

The original point is fixed by Y, and its L₂-orbit spans the literal
four-plane V₂. In marked Heisenberg coordinates, the binary cubic norm
identity forces the residual center to fix that point. The center is
normal in D/O₃′(D), so its preimage fixes the entire span W = ⟨V₁ᴰ⟩.
Consequently the faithful residual would be abelian, contradicting the
proved nonnormalization of the two original cubic images.

The remaining prime-to-three quotient has Sylow overlap of order two.
Both vertex cores therefore lie in O₃′(D) and hence C_D(W); the exact
vertex-kernel intersections identify them with O₂(D). The faithful
quotient also has Sylow image of order two. The final theorem applies
these deductions to the original order-four chief interval, preserving
Y, its actual star kernel, and the original S₃ quotient.

This bypasses the six-dimensional representation calculation in the
Heisenberg branch. The companion CubicContainment module excludes the
remaining common-core branch using the original normal-point geometry.
The full residual classification is a further source obligation.

Source: Aschbacher–Smith, 14.5.12–13 and the following proof of
14.5.3, printed pp.1016–1017; 14.7.20(2), p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The marked Heisenberg alternative contradicts the literal point-plane action. -/
theorem cubic_generated_no_heisenberg_model_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    let A := ((F.P L).subgroupOf D).map q
    let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
    ¬ Nonempty (ChapterF.Noncyclic.MarkedRecognition.MarkedModel A B
      (HeisenbergPrime 3) MarkedCubicRecognition.heisenbergAction
      MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let q := QuotientGroup.mk' (pPrimeCore 3 D)
  let E := D ⧸ pPrimeCore 3 D
  let R := pResidual 2 E
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  obtain ⟨_,hk,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_normalizes_point h hab structural previous
    faithful Y hYH hYL hYp hYT hout he
  let β := MulAut.quotientConjNormal U (pPrimeCore 3 D) hk
  dsimp only at ⊢
  rintro ⟨m⟩
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hPD : F.Vi 2 ≤ D := (F.le_seed 2).trans (h.chosen.le_sylow.trans hTD)
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hPW : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    exact conjugateSpanBy_mono le_rfl hXD
  have hX : MarkedCubicRecognition.leftAxis.range.map
      (R.subtype.comp m.residualEquiv.toMonoidHom) = ((F.Li L 2).subgroupOf D).map q := by
    rw [←map_map,m.left_line]
    dsimp only [ChapterF.Noncyclic.MarkedRecognition.residualLine]
    rw [map_subgroupOf_eq_of_le (map_pResidual_le 2 _),←map_embedded_pResidual]
    exact congrArg (map q) (cubic_action_residuals (F := F) h structural Y hYp hYT).1
  have hY : MarkedCubicRecognition.rightAxis.range.map
      (R.subtype.comp m.residualEquiv.toMonoidHom) = (Y.subgroupOf D).map q := by
    rw [←map_map,m.right_line]
    dsimp only [ChapterF.Noncyclic.MarkedRecognition.residualLine]
    rw [map_subgroupOf_eq_of_le (map_pResidual_le 2 _),←map_embedded_pResidual]
    exact congrArg (map q) (cubic_action_residuals (F := F) h structural Y hYp hYT).2
  have hXP : (F.Li L 2).subgroupOf D ≤ normalizer ((F.Vi 2).subgroupOf D : Set D) := by
    intro x hx
    apply le_normalizer_comap D.subtype
    exact (F.Li_le L 2 hx).2
  have hYZ : Y.subgroupOf D ≤ centralizer ((F.Vi 1).subgroupOf D : Set D) := by
    intro y hy
    apply mem_centralizer_iff.mpr
    intro z hz
    apply Subtype.ext
    exact mem_centralizer_iff.mp
      ((hYH.trans (normalizer_le_centralizer_of_card_two _
        (by simpa using F.card 1 (by decide)))) hy) z hz
  have hplane : conjugateSpanBy ((F.Vi 1).subgroupOf D) ((F.Li L 2).subgroupOf D) =
      (F.Vi 2).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hZD,map_subgroupOf_eq_of_le hXD,
      map_subgroupOf_eq_of_le hPD,plane_eq_point_residual_span h structural]
  have hspan : conjugateSpanBy ((F.Vi 1).subgroupOf D) ⊤ = U := by
    apply map_injective D.subtype_injective
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hZD,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZD)]
  have hc := MarkedCubicRecognition.center_kernel_of_point_plane U
    ((F.Vi 1).subgroupOf D) ((F.Vi 2).subgroupOf D) ((F.Li L 2).subgroupOf D)
    (Y.subgroupOf D) q (QuotientGroup.mk'_surjective _) β
    (MulAut.quotientConjNormal_comp_mk _ _ hk) R m.residualEquiv hX hY
    (subgroupOf_mono D (F.monotone (by decide : 1 ≤ 2))) (subgroupOf_mono D hPW)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv]; simpa using F.card 1 (by decide))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv]; simpa using F.card 2 (by decide))
    hXP hYZ hplane hspan
  have hcf : (center R).map R.subtype ≤ f.ker := by
    intro b hb
    obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 3 D) b
    have hh := hc hb
    have hd : d ∈ C := by
      change d ∈ centralizer (U : Set D)
      rw [←MulAut.conjNormal_ker_eq_centralizer]
      exact hh
    change f (q d) = 1
    exact (DFunLike.congr_fun hcomp d).trans ((QuotientGroup.eq_one_iff d).mpr hd)
  have habR : IsMulCommutative (R.map f) := by
    apply IsMulCommutative.of_comm
    intro a b
    obtain ⟨x,hx,hxa⟩ := a.property
    obtain ⟨y,hy,hyb⟩ := b.property
    let e := m.residualEquiv
    have hcxy : ⁅(⟨x,hx⟩ : R),(⟨y,hy⟩ : R)⁆ ∈ center R := by
      have hm : ⁅e.symm ⟨x,hx⟩,e.symm ⟨y,hy⟩⁆ ∈ center (HeisenbergPrime 3) :=
        HeisenbergPrime.commutator_le_center
          (commutator_mem_commutator (mem_top _) (mem_top _))
      apply mem_center_iff.mpr
      intro z
      apply e.symm.injective
      simpa only [map_mul,map_commutatorElement] using mem_center_iff.mp hm (e.symm z)
    have hh := hcf (mem_map_of_mem R.subtype hcxy)
    change f (R.subtype ⁅(⟨x,hx⟩ : R),(⟨y,hy⟩ : R)⁆) = 1 at hh
    simp only [map_commutatorElement,subtype_apply] at hh
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa only [hxa,hyb] using hh)
  rw [show R = pResidual 2 E from rfl,map_pResidual_of_surjective 2 f hf] at habR
  exact cubic_generated_action_residual_noncommutative_of_normalizes_point h structural Y hYH hYL hYp hYT hout habR

/-- The original full point-normality interface. -/
theorem cubic_generated_no_heisenberg_model
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    let A := ((F.P L).subgroupOf D).map q
    let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
    ¬ Nonempty (ChapterF.Noncyclic.MarkedRecognition.MarkedModel A B
      (HeisenbergPrime 3) MarkedCubicRecognition.heisenbergAction
      MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range) := by
  apply cubic_generated_no_heisenberg_model_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- After the Heisenberg exclusion, the prime-to-three overlap has order two and both image cores vanish. -/
theorem cubic_generated_primeToThree_overlap_two_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    let A := ((F.P L).subgroupOf D).map q
    let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
    Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2)) ∧
      (pCore 2 A).map A.subtype = ⊥ ∧ (pCore 2 B).map B.subtype = ⊥ := by
  exact (cubic_generated_solvable_models_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2.2.resolve_right
      (cubic_generated_no_heisenberg_model_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he)

/-- The original full point-normality interface. -/
theorem cubic_generated_primeToThree_overlap_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    let A := ((F.P L).subgroupOf D).map q
    let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
    Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2)) ∧
      (pCore 2 A).map A.subtype = ⊥ ∧ (pCore 2 B).map B.subtype = ⊥ := by
  apply cubic_generated_primeToThree_overlap_two_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

private theorem embedded_core_le_kernel_of_image_core_bot
    {D E : Type*} [Group D] [Group E]
    (q : D →* E) (A : Subgroup D)
    (hcore : (pCore 2 (A.map q)).map (A.map q).subtype = ⊥) :
    (pCore 2 A).map A.subtype ≤ q.ker := by
  have hp : (pCore 2 A).map (q.subgroupMap A) ≤ pCore 2 (A.map q) :=
    le_sSup ⟨Normal.map inferInstance _ (q.subgroupMap_surjective A),
      pCore_isPGroup.map _⟩
  rintro x ⟨a,ha,rfl⟩
  have hh := mem_map_of_mem (A.map q).subtype (hp (mem_map_of_mem (q.subgroupMap A) ha))
  rw [hcore] at hh
  exact hh

/-- Both original vertex two-cores coincide with the two-core of the generated group. -/
theorem cubic_generated_equal_two_cores_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    (F.P L).pCoreIn 2 = D.pCoreIn 2 ∧
      (Y ⊔ (T : Subgroup G)).pCoreIn 2 = D.pCoreIn 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  let W := conjugateSpanBy (F.Vi 1) D
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' (pPrimeCore 3 D)
  obtain ⟨_,hA,hB⟩ := cubic_generated_primeToThree_overlap_two_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  have hk : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact (cubic_generated_action_core_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2.1
  obtain ⟨hAC,hBC,_⟩ := cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hcore (J : Subgroup D) (hSJ : (S : Subgroup D) ≤ J)
      (hJC : J ⊓ C = pCore 2 D)
      (hj : (pCore 2 (J.map q)).map (J.map q).subtype = ⊥) :
      J.pCoreIn 2 = pCore 2 D := by
    apply le_antisymm
    · exact (le_inf (map_subtype_le _) ((embedded_core_le_kernel_of_image_core_bot q J hj).trans hk)).trans_eq hJC
    · exact pCore_le_map_of_sylow_le S J hSJ
  have hAeq := hcore A (hS.symm.le.trans inf_le_left) hAC hA
  have hBeq := hcore B (hS.symm.le.trans inf_le_right) hBC hB
  constructor
  · have hh := congrArg (map D.subtype) hAeq
    rw [map_pCoreIn_of_injective 2 A D.subtype D.subtype_injective] at hh
    dsimp only [A] at hh
    rw [map_subgroupOf_eq_of_le (show F.P L ≤ D from le_sup_left)] at hh
    exact hh
  · have hh := congrArg (map D.subtype) hBeq
    rw [map_pCoreIn_of_injective 2 B D.subtype D.subtype_injective] at hh
    dsimp only [B] at hh
    rw [map_subgroupOf_eq_of_le (show Y ⊔ (T : Subgroup G) ≤ D from le_sup_right)] at hh
    exact hh

/-- The original full point-normality interface. -/
theorem cubic_generated_equal_two_cores
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    (F.P L).pCoreIn 2 = D.pCoreIn 2 ∧
      (Y ⊔ (T : Subgroup G)).pCoreIn 2 = D.pCoreIn 2 := by
  apply cubic_generated_equal_two_cores_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The literal Sylow image in the faithful action quotient is cyclic of order two. -/
theorem cubic_generated_action_sylow_order_two_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    Nonempty ((((T : Subgroup G).subgroupOf D).map q) ≃* Multiplicative (ZMod 2)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let q₃ := QuotientGroup.mk' (pPrimeCore 3 D)
  let S₃ := ((T : Subgroup G).subgroupOf D).map q₃
  let S := ((T : Subgroup G).subgroupOf D).map q
  have hi := (cubic_generated_primeToThree_triple_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).1
  have hs₃ := (cubic_generated_primeToThree_overlap_two_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).1
  rw [hi] at hs₃
  have hc₃ : Nat.card S₃ = 2 := by
    rw [Nat.card_congr hs₃.some.toEquiv]
    simp
  obtain ⟨_,_,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_normalizes_point h hab structural previous
    faithful Y hYH hYL hYp hYT hout he
  have hSf : S₃.map f = S := by
    dsimp only [S₃,S,q₃,q]
    rw [map_map,hcomp]
  have hbound : Nat.card S ≤ 2 := by
    rw [←hSf]
    exact (Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective S₃)).trans_eq hc₃
  rcases (cubic_generated_action_three_core_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2.2.2 with hs | hs
  · exact hs
  · have hc : Nat.card S = 4 := by
      rw [Nat.card_congr hs.some.toEquiv]
      simp
    omega

/-- The original full point-normality interface. -/
theorem cubic_generated_action_sylow_order_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    Nonempty ((((T : Subgroup G).subgroupOf D).map q) ≃* Multiplicative (ZMod 2)) := by
  apply cubic_generated_action_sylow_order_two_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original order-four chief interval forces the two cubic vertices to have the same two-core as their generated group, retaining the actual star kernel and both quotient maps. -/
theorem extraspecial_four_interval_cubic_equal_cores
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
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
      ∃ _he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)),
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      (F.P L).pCoreIn 2 = D.pCoreIn 2 ∧
      (Y ⊔ (T : Subgroup G)).pCoreIn 2 = D.pCoreIn 2 ∧
      let q := QuotientGroup.mk' (pPrimeCore 3 D)
      let A := ((F.P L).subgroupOf D).map q
      let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
      A ⊓ B = ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple A B ∧
      pCore 2 (D ⧸ pPrimeCore 3 D) = ⊥ ∧
      IsPGroup 3 (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ¬ IsMulCommutative (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      (Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2)) ∧
        (pCore 2 A).map A.subtype = ⊥ ∧ (pCore 2 B).map B.subtype = ⊥) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let r := QuotientGroup.mk' C
      let X := ((F.Li L 2).subgroupOf D).map r
      let Y₀ := (Y.subgroupOf D).map r
      let S := ((T : Subgroup G).subgroupOf D).map r
      pResidual 2 (D ⧸ C) = pCore 3 (D ⧸ C) ∧
        X ⊔ Y₀ = pCore 3 (D ⧸ C) ∧
        ¬ IsMulCommutative (pCore 3 (D ⧸ C)) ∧
        Nonempty (S ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hi,ht,hcore⟩ := cubic_generated_primeToThree_triple h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  obtain ⟨h3,hna,hm⟩ := cubic_generated_solvable_models h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  obtain ⟨hCA,hCB⟩ := cubic_generated_equal_two_cores h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  have htwo := hm.resolve_right (cubic_generated_no_heisenberg_model h hab structural previous
    faithful hn Y hYH hYp hYT hout he)
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hCA,hCB,hi,ht,hcore,h3,hna,htwo,
    (cubic_generated_action_three_core h hab structural previous faithful hn Y hYH hYp hYT hout he).1,
    (cubic_generated_action_three_core h hab structural previous faithful hn Y hYH hYp hYT hout he).2.1,
    (cubic_generated_action_three_core h hab structural previous faithful hn Y hYH hYp hYT hout he).2.2.1,
    cubic_generated_action_sylow_order_two h hab structural previous faithful hn Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
