module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicTwoThree
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent

/-!
# Solvable models of the original cubic completion

The factorization through D/O₃′(D) prevents collapse of its two vertex
images: collapse would also identify the vertices in D/C_D(W). Thus the
prime-to-three quotient retains the full Goldschmidt overlap. A cyclic
three-core would supply a nonsolvable component, contradicting the proved
solvability of D. The noncyclic F.6.16 classification therefore applies
with the original SQTK cover, without quotient prime-rank monotonicity.

The S₃ × S₃ model is excluded because the two original cubic images do
not normalize one another. The remaining alternatives are the order-two
Sylow overlap or the actual Heisenberg extension, with both cubic axes
and the entire four-group action marked. On the faithful action quotient,
the two cubic images generate the nonabelian three-core, which equals
the two-residual; its literal Sylow image has order two or four.

The last theorem applies all these deductions to the original order-four
chief interval, preserving Y, its star kernel and its S₃ quotient. The
exclusion of the remaining solvable alternatives, and hence 14.5.3(2),
is still required. No source Data or local classifier is assumed.

Source: Aschbacher–Smith, F.6.16–18, pp.308–310; the reduction in
14.5.12–13, pp.1016–1017; and 14.7.20(2), p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
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

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original prime-to-three quotient retains the full Sylow overlap and genuine Goldschmidt triple. -/
theorem cubic_generated_primeToThree_triple_of_normalizes_point
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
  obtain ⟨_,_,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_normalizes_point h hab structural previous
    faithful Y hYH hYL hYp hYT hout he
  obtain ⟨hi,hplus⟩ := primeToThree_triple_of_factor ht (QuotientGroup.mk' C)
    (cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.1
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

/-- The original full point-normality interface. -/
theorem cubic_generated_primeToThree_triple
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
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    let q := QuotientGroup.mk' (pPrimeCore 3 D)
    A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      pCore 2 (D ⧸ pPrimeCore 3 D) = ⊥ := by
  apply cubic_generated_primeToThree_triple_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The literal action two-residual is nonabelian: otherwise the cubic images would centralize each other. -/
theorem cubic_generated_action_residual_noncommutative_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G)) :
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
  exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout

/-- The original full point-normality interface. -/
theorem cubic_generated_action_residual_noncommutative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    ¬ IsMulCommutative (pResidual 2 (D ⧸ C)) := by
  apply cubic_generated_action_residual_noncommutative_of_normalizes_point
    (h := h) (structural := structural) (Y := Y) (hYH := hYH)
    (hYp := hYp) (hYT := hYT) (hout := hout)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Solvability and the original SQTK cover select the two remaining marked source alternatives. -/
theorem cubic_generated_solvable_models_of_normalizes_point
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
  have ht := (cubic_generated_primeToThree_triple_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2.1
  let : Group.IsSolvable D :=
    cubic_generated_solvable_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  have hnc := solvable_threeCore_not_cyclic ht inferInstance
    (pPrimeCore_quotient_pPrimeCore_eq_bot (G := D) 3)
  have hsq := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  have h3 := ChapterF.SourceAssembly.residual_isThreeGroup_of_cover hsq (MulEquiv.refl _) ht hnc
  obtain ⟨_,_,f,hf,hcomp⟩ := cubic_generated_action_core_kernel_of_normalizes_point h hab structural previous
    faithful Y hYH hYL hYp hYT hout he
  have hna : ¬ IsMulCommutative (pResidual 2 (D ⧸ pPrimeCore 3 D)) := by
    intro hc
    let := hc
    have hh : IsMulCommutative ((pResidual 2 (D ⧸ pPrimeCore 3 D)).map f) := inferInstance
    rw [map_pResidual_of_surjective 2 f hf] at hh
    exact cubic_generated_action_residual_noncommutative_of_normalizes_point h structural Y hYH hYL hYp hYT hout hh
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

/-- The original full point-normality interface. -/
theorem cubic_generated_solvable_models
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
    IsPGroup 3 (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ¬ IsMulCommutative (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ((Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2)) ∧
          (pCore 2 A).map A.subtype = ⊥ ∧ (pCore 2 B).map B.subtype = ⊥) ∨
        Nonempty (ChapterF.Noncyclic.MarkedRecognition.MarkedModel A B
          (HeisenbergPrime 3) MarkedCubicRecognition.heisenbergAction
          MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range)) := by
  apply cubic_generated_solvable_models_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The original cubic action has nonabelian normal three-residual, generated by the two marked cubic images. -/
theorem cubic_generated_action_three_core_of_normalizes_point
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
  have h3plus := (cubic_generated_solvable_models_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).1
  obtain ⟨_,_,f,hf,_⟩ := cubic_generated_action_core_kernel_of_normalizes_point h hab structural previous
    faithful Y hYH hYL hYp hYT hout he
  have h3 : IsPGroup 3 (pResidual 2 (D ⧸ C)) := by
    have hh := h3plus.map f
    rwa [map_pResidual_of_surjective 2 f hf] at hh
  have heq : pResidual 2 (D ⧸ C) = pCore 3 (D ⧸ C) :=
    le_antisymm (le_sSup ⟨inferInstance,h3⟩) ChapterF.Noncyclic.threeCore_le_twoResidual
  obtain ⟨hi,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hgen := ht.twoResidual_eq_sup
  rw [←map_embedded_pResidual,←map_embedded_pResidual] at hgen
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2] at hgen
  have hnc := cubic_generated_action_residual_noncommutative_of_normalizes_point h structural Y hYH hYL hYp hYT hout
  change ¬ IsMulCommutative (pResidual 2 (D ⧸ C)) at hnc
  rw [heq] at hnc
  refine ⟨heq,hgen.symm.trans heq,hnc,?_⟩
  have hs := ht.odd_residual_small_sylow hcore (ChapterF.Noncyclic.odd_residual_of_three h3)
  rw [hi] at hs
  exact hs.imp_right fun hh => hh.2.2

/-- The original full point-normality interface. -/
theorem cubic_generated_action_three_core
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
    let X := ((F.Li L 2).subgroupOf D).map q
    let Y₀ := (Y.subgroupOf D).map q
    let S := ((T : Subgroup G).subgroupOf D).map q
    pResidual 2 (D ⧸ C) = pCore 3 (D ⧸ C) ∧
      X ⊔ Y₀ = pCore 3 (D ⧸ C) ∧
      ¬ IsMulCommutative (pCore 3 (D ⧸ C)) ∧
      (Nonempty (S ≃* Multiplicative (ZMod 2)) ∨
        Nonempty (S ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) := by
  apply cubic_generated_action_three_core_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original order-four interval supplies every hypothesis of the solvable model reduction, with its exact kernels. -/
theorem extraspecial_four_interval_cubic_solvable_models
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
      let q := QuotientGroup.mk' (pPrimeCore 3 D)
      let A := ((F.P L).subgroupOf D).map q
      let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
      A ⊓ B = ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple A B ∧
      pCore 2 (D ⧸ pPrimeCore 3 D) = ⊥ ∧
      IsPGroup 3 (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ¬ IsMulCommutative (pResidual 2 (D ⧸ pPrimeCore 3 D)) ∧
      ((Nonempty ((A ⊓ B : Subgroup _) ≃* Multiplicative (ZMod 2)) ∧
          (pCore 2 A).map A.subtype = ⊥ ∧ (pCore 2 B).map B.subtype = ⊥) ∨
        Nonempty (ChapterF.Noncyclic.MarkedRecognition.MarkedModel A B
          (HeisenbergPrime 3) MarkedCubicRecognition.heisenbergAction
          MarkedCubicRecognition.leftAxis.range MarkedCubicRecognition.rightAxis.range)) ∧
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
        (Nonempty (S ≃* Multiplicative (ZMod 2)) ∨
          Nonempty (S ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hi,ht,hcore⟩ := cubic_generated_primeToThree_triple h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  obtain ⟨h3,hna,hm⟩ := cubic_generated_solvable_models h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hi,ht,hcore,h3,hna,hm,
    cubic_generated_action_three_core h hab structural previous faithful hn Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
