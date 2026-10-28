module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingPrimes
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicHeisenbergExclusion

/-!
# Solvable models for the moving cubic completion

The prime-to-three quotient retains the actual Goldschmidt triple. Its
solvable classification leaves a cyclic Sylow overlap or a marked
Heisenberg extension. In the latter case the two cubic axes act on the
original point and plane; the binary norm identity kills the Heisenberg
center on the full point span, contradicting its nonabelian residual.
Consequently the literal action Sylow has order two and both vertex
cores equal O₂(D). The final consumer obtains these conclusions for a
failed lift through the original proper invariant quotient.

The cyclic-overlap contradiction and full 14.7.2(3) lifting theorem
remain separate; the equal-core conclusion alone does not prove them.
Source: Aschbacher–Smith, 14.5.12–13 and the following norm argument,
printed pp.1016–1017; 14.7.2(3), p.1043, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem primeToThree_triple_of_factor
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    {A B : Subgroup D} (ht : ChapterF.IsGoldschmidtTriple A B)
    (r : D →* E) (ht' : ChapterF.IsGoldschmidtTriple (A.map r) (B.map r))
    (f : (D ⧸ pPrimeCore 3 D) →* E)
    (hf : f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = r) :
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    A.map q ⊓ B.map q = (A ⊓ B).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  have hi := ht.primeToThreeCore_image_intersection_or_eq
  rcases hi with hi | he
  · exact ⟨hi, ht.quotient_primeToThreeCore_of_intersection hi⟩
  · have he' := congrArg (map f) he
    rw [map_map,map_map,hf] at he'
    exact False.elim (ht'.embedded_twoResidual_ne (by rw [he']))

private theorem noncommutative_residual_of_obstruction
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (hout : ¬ (pResidual 2 B).map B.subtype ≤
      normalizer ((pResidual 2 A).map A.subtype : Set D)) :
    ¬ IsMulCommutative (pResidual 2 D) := by
  intro hc
  let := hc
  apply hout
  exact ((map_pResidual_le 2 B.subtype).trans
    (pResidual 2 D).le_centralizer).trans
      ((centralizer_le (map_pResidual_le 2 A.subtype)).trans
        (Subgroup.centralizer_le_normalizer _))

private theorem solvable_threeCore_not_cyclic
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (hs : Group.IsSolvable D) (hp : pPrimeCore 3 D = ⊥) :
    ¬ IsCyclic (pCore 3 D) := by
  let := hs
  intro hc
  obtain ⟨K,hK,_⟩ := ChapterF.Cyclic.exists_component_of_cyclic_three_core ht hp hc
  exact hK.isCComponent.not_isSolvable inferInstance

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

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem cubic_generated_primeToThree_triple_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      pCore 2 (D ⧸ pPrimeCore 3 D) = ⊥ := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  obtain ⟨_,_,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_moving_plane h hab structural previous
    faithful Y hYH hmovePlane hYp hYT hout he
  obtain ⟨hi,hplus⟩ := primeToThree_triple_of_factor ht (QuotientGroup.mk' C)
    (cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he).2.1
    f hcomp
  have hinter : (F.P L).subgroupOf D ⊓ (Y ⊔ (T : Subgroup G)).subgroupOf D =
      (T : Subgroup G).subgroupOf D := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ F.P L ⊓ F.H :=
        ⟨hx.1,(sup_le hYH (F.invariant 1)) hx.2⟩
      rwa [plane_parabolic_inf_point h structural] at hh
    · intro x hx
      exact ⟨F.binary_sylow_le_P L hx,
        (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hx⟩
  rw [hinter] at hi
  exact ⟨hi,hplus,ht.primeToThreeCore_quotient_twoCore_eq_bot⟩

theorem cubic_generated_action_residual_noncommutative_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    ¬ IsMulCommutative (pResidual 2 (D ⧸ C)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  apply noncommutative_residual_of_obstruction (A := ((F.P L).subgroupOf D).map q)
    (B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)
  rw [←map_embedded_pResidual,←map_embedded_pResidual]
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2]
  exact cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hmovePlane hYp

theorem cubic_generated_solvable_models_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    let A := ((F.P L).subgroupOf D).map q
    let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
    IsPGroup 3 (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ¬ IsMulCommutative (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ((Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2)) ∧
          (pCore 2 A).map A.subtype = ⊥ ∧ (pCore 2 B).map B.subtype = ⊥) ∨
        Nonempty (ChapterF.Noncyclic.MarkedRecognition.MarkedModel A B
          (HeisenbergPrime 3) MarkedCubicRecognition.heisenbergAction
          MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range)) := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let q := QuotientGroup.mk' (pPrimeCore 3 D)
  let A := ((F.P L).subgroupOf D).map q
  let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  have ht := (cubic_generated_primeToThree_triple_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2.1
  let : Group.IsSolvable D :=
    cubic_generated_solvable_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
  have hnc := solvable_threeCore_not_cyclic ht inferInstance
    (pPrimeCore_quotient_pPrimeCore_eq_bot (G := D) 3)
  have hsq := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  have h3 := ChapterF.SourceAssembly.residual_isThreeGroup_of_cover hsq (MulEquiv.refl _) ht hnc
  obtain ⟨_,_,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_moving_plane h hab structural previous
    faithful Y hYH hmovePlane hYp hYT hout he
  have hna : ¬ IsMulCommutative (pResidual 2 (D ⧸ pPrimeCore 3 D)) := by
    intro hc
    let := hc
    have hh : IsMulCommutative ((pResidual 2 (D ⧸ pPrimeCore 3 D)).map f) := inferInstance
    rw [map_pResidual_of_surjective 2 f hf] at hh
    exact cubic_generated_action_residual_noncommutative_of_moving_plane h structural Y hYH hmovePlane hYp hYT hh
  refine ⟨h3,hna,?_⟩
  by_cases htwo : Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2))
  · have hc : Nat.card (A ⊓ B : Subgroup _) = 2 := by
      rw [Nat.card_congr htwo.some.toEquiv]
      simp
    exact Or.inl ⟨htwo,ChapterF.Noncyclic.cores_eq_bot_of_intersection_card_two ht hc,
      ChapterF.Noncyclic.cores_eq_bot_of_intersection_card_two ht.symm (by simpa only [inf_comm] using hc)⟩
  · rcases ChapterF.SourceAssembly.source_marked_models hsq (MulEquiv.refl _) ht hnc htwo
      with hm | hm
    · obtain ⟨m⟩ := hm
      apply False.elim
      apply hna
      exact IsMulCommutative.of_comm fun x y => m.residualEquiv.symm.injective (by
        simp only [map_mul,mul_comm])
    · exact Or.inr hm

theorem cubic_generated_action_three_core_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
    let X := ((F.Li L 2).subgroupOf D).map q
    let Y₀ := (Y.subgroupOf D).map q
    let S := ((T : Subgroup G).subgroupOf D).map q
    pResidual 2 (D ⧸ C) = pCore 3 (D ⧸ C) ∧
      X ⊔ Y₀ = pCore 3 (D ⧸ C) ∧
      ¬ IsMulCommutative (pCore 3 (D ⧸ C)) ∧
      (Nonempty (S ≃* Multiplicative (ZMod 2)) ∨
        Nonempty (S ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  have h3plus := (cubic_generated_solvable_models_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).1
  obtain ⟨_,_,f,hf,_⟩ := cubic_generated_action_core_kernel_of_moving_plane h hab structural previous
    faithful Y hYH hmovePlane hYp hYT hout he
  have h3 : IsPGroup 3 (pResidual 2 (D ⧸ C)) := by
    have hh := h3plus.map f
    rwa [map_pResidual_of_surjective 2 f hf] at hh
  have heq : pResidual 2 (D ⧸ C) = pCore 3 (D ⧸ C) :=
    le_antisymm (le_sSup ⟨inferInstance,h3⟩) ChapterF.Noncyclic.threeCore_le_twoResidual
  obtain ⟨hi,ht,hcore⟩ := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he
  have hgen := ht.twoResidual_eq_sup
  rw [←map_embedded_pResidual,←map_embedded_pResidual] at hgen
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2] at hgen
  have hnc := cubic_generated_action_residual_noncommutative_of_moving_plane h structural Y hYH hmovePlane hYp hYT
  change ¬ IsMulCommutative (pResidual 2 (D ⧸ C)) at hnc
  rw [heq] at hnc
  refine ⟨heq,hgen.symm.trans heq,hnc,?_⟩
  have hs := ht.odd_residual_small_sylow hcore (ChapterF.Noncyclic.odd_residual_of_three h3)
  rw [hi] at hs
  exact hs.imp_right fun hh => hh.2.2

theorem cubic_generated_no_heisenberg_model_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  obtain ⟨_,hk,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_moving_plane h hab structural previous
    faithful Y hYH hmovePlane hYp hYT hout he
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
  exact cubic_generated_action_residual_noncommutative_of_moving_plane h structural Y hYH hmovePlane hYp hYT habR

theorem cubic_generated_primeToThree_overlap_two_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  exact (cubic_generated_solvable_models_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2.2.resolve_right
      (cubic_generated_no_heisenberg_model_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he)

theorem cubic_generated_equal_two_cores_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  obtain ⟨_,hA,hB⟩ := cubic_generated_primeToThree_overlap_two_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
  have hk : q.ker ≤ C := by
    rw [QuotientGroup.ker_mk']
    exact (cubic_generated_action_core_kernel_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2.1
  obtain ⟨hAC,hBC,_⟩ := cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he
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

theorem cubic_generated_action_sylow_order_two_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
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
  have hi := (cubic_generated_primeToThree_triple_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).1
  have hs₃ := (cubic_generated_primeToThree_overlap_two_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).1
  rw [hi] at hs₃
  have hc₃ : Nat.card S₃ = 2 := by
    rw [Nat.card_congr hs₃.some.toEquiv]
    simp
  obtain ⟨_,_,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_moving_plane h hab structural previous
    faithful Y hYH hmovePlane hYp hYT hout he
  have hSf : S₃.map f = S := by
    dsimp only [S₃,S,q₃,q]
    rw [map_map,hcomp]
  have hbound : Nat.card S ≤ 2 := by
    rw [←hSf]
    exact (Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective S₃)).trans_eq hc₃
  rcases (cubic_generated_action_three_core_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2.2.2 with hs | hs
  · exact hs
  · have hc : Nat.card S = 4 := by
      rw [Nat.card_congr hs.some.toEquiv]
      simp
    omega


/-- A failed plane lift has equal vertex cores, a nonabelian three-residual,
and a cyclic action Sylow, on the same original actor and quotient. -/
theorem original_quotient_plane_lifting_cyclic_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let E := conjugateSpanBy (F.Vi 1) D
    letI : (E.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (E.subgroupOf D : Set D))
    Group.IsSolvable D ∧
      ((F.P L).pCoreIn 2 = D.pCoreIn 2 ∧
        (Y ⊔ (T : Subgroup G)).pCoreIn 2 = D.pCoreIn 2) ∧
      pResidual 2 (D ⧸ centralizer (E.subgroupOf D : Set D)) =
        pCore 3 (D ⧸ centralizer (E.subgroupOf D : Set D)) ∧
      ¬ IsMulCommutative (pCore 3 (D ⧸ centralizer (E.subgroupOf D : Set D))) ∧
      Nonempty ((((T : Subgroup G).subgroupOf D).map q) ≃* Multiplicative (ZMod 2)) := by
  have hout := quotient_plane_moving_actor_escapes_at h (structural G T)
    c p hp Y hYH hYp hfix hm
  have hc := cubic_generated_action_three_core_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT hout he
  exact ⟨cubic_generated_solvable_of_moving_plane
      h hab structural previous faithful Y hYH hm hYp hYT hout he,
    cubic_generated_equal_two_cores_of_moving_plane
      h hab structural previous faithful Y hYH hm hYp hYT hout he,
    hc.1,hc.2.2.1,cubic_generated_action_sylow_order_two_of_moving_plane
      h hab structural previous faithful Y hYH hm hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
