module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.ThompsonNormality
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicThompson
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.CubicComponents
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicSolvability
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonFactors
public import Theory.GroupTheory.SymmetricThreeResidualNormality
public import Theory.GroupTheory.ElementaryThompsonRelative
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Baumann
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicThompsonCommutator
public import CFSG.Quasithin.ChapterB.Section02.Thompson.LinearThreeImage
public import Theory.GroupTheory.MinimalParabolicResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeReduction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SolvableReduction
public import Theory.GroupTheory.Fitting.PrimeResidual
public import Theory.GroupAction.SupercriticalCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeActors
public import CFSG.Quasithin.ChapterB.Section02.Thompson.NearMaximumAction
public import CFSG.Quasithin.ChapterD.Section02.ThompsonGeneration
public import Theory.GroupTheory.OddPrimeSectionCentralizers.ElementaryAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeFixedSpace
public import CFSG.Quasithin.ChapterB.Section02.Thompson.FixedAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicPrimeFive
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.PrimeByTwo.SmallActor
public import Theory.GroupTheory.PrimeCommutatorPlane
public import Theory.ElementaryAbelian.PrimePlane
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicTwoThree
public import CFSG.Quasithin.ChapterB.Section02.Thompson.FixedSaturation
public import CFSG.Quasithin.ChapterD.Section02.QuinticPlaneExclusion
public import Theory.GroupTheory.TwoThreeCoreKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicSolvableModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CyclicComponent
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicHeisenbergExclusion
public import Theory.GroupAction.MarkedCubicRecognition.PointPlane
public import Theory.GroupAction.QuotientConjugation

/-!
# Guarded cubic solvable

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Thompson control in the original solvable cubic completion

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, solvable Thompson factorization
makes a nontrivial Thompson image a normal S₃ or S₃×S₃ subgroup of
D/C_D(W). A Sylow-invariant subgroup of its odd residual is normal.
Neither original cubic residual image can be normal: the first would
contradict the plane-normalizer obstruction, and the second centralizes
the point and hence its full D-span. Goldschmidt intersection control
therefore forces the original J(T) into C_T(W) = O₂(D).

Thompson heredity gives J(T) = J(O₂(D)) = J(O₂(L₂T)), so D normalizes
J(T). If J(T) lay in the original point core, the earlier 14.3.9(2)
would make it normal in LT; uniqueness over LT would contradict the
escape of Y. In particular J(T) leaves O₂(LT).

The last theorem applies these deductions to the original order-four
chief interval, retaining the selected Y, its exact star kernel and its
S₃ quotient. This proves 14.5.9 and the first two assertions of 14.5.10
in this branch. The J₁(T) commutator, subsequent solvable containment,
small-interval exclusions and classification through 14.7.52 remain open.
EarlierFaithfulClassification is the independent 14.3.4 input, retained
with its existing producer and final source-discharge owner.

Source: Aschbacher–Smith, 14.5.9–10, printed p.1015; B.2.16, p.79;
14.3.9(2), pp.992–993; and the interval use in 14.7.20(2), p.1049,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem CubicThompson_goldschmidt_thompson_centralizes
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (U : Subgroup D) (hr : IsPReduced 2 U)
    (hs : Group.IsSolvable D) (h3 : primeRank 3 D ≤ 2)
    (S : Sylow 2 D) (hS : A ⊓ B = (S : Subgroup D))
    (hnA : letI := hr.normal
      ¬ (((pResidual 2 A).map A.subtype).map
        (QuotientGroup.mk' (centralizer (U : Set D)))).Normal)
    (hnB : letI := hr.normal
      ¬ (((pResidual 2 B).map B.subtype).map
        (QuotientGroup.mk' (centralizer (U : Set D)))).Normal) :
    elementaryAbelianMaxJ (S : Subgroup D) ≤ centralizer (U : Set D) := by
  let := hr.normal
  let := hr.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set D))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set D))
  let J := conjugateSpanBy (elementaryAbelianMaxJ (S : Subgroup D)) ⊤
  let I := J.map q
  let : J.Normal := (normalizer_eq_top_iff.mp (top_unique (le_normalizer_conjugateSpanBy _ _)))
  let : I.Normal := Normal.map inferInstance q hq
  let N := I.comap q
  let : N.Normal := inferInstanceAs (I.comap q).Normal
  by_contra hJ
  have hm : Nonempty (I ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (I ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
    ChapterB.relative_thompson_span_models U (S : Subgroup D)
      (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
      q hq (QuotientGroup.ker_mk' _) (by simpa only [q,QuotientGroup.ker_mk'] using hJ) hs hr.quotient_pCore_eq_bot h3
  have hlocal (X : Subgroup D) (hp : IsPPerfect 2 X)
      (hn : (S : Subgroup D) ≤ normalizer (X : Set D))
      (hout : ¬ (X.map q).Normal) : ¬ X ≤ N := by
    intro hXN
    have hXI : X.map q ≤ I := map_le_iff_le_comap.mpr hXN
    have hp' : IsPPerfect 2 (X.map q) := hp.of_surjective
      (q.subgroupMap X) (q.subgroupMap_surjective X)
    have hR := embedded_pResidual_mono 2 hXI
    rw [(pResidual_eq_top_iff 2 (X.map q)).mpr hp',
      ←MonoidHom.range_eq_map,range_subtype] at hR
    exact hout (SymmetricThreeCubicNormality.residual_subgroup_normal_of_sylow_normalizes
      I (X.map q) hm (S.mapSurjective hq) hR
      ((map_mono hn).trans (X.le_normalizer_map q)))
  have hAN := hlocal _ (isPPerfect_embedded_pResidual 2 A)
    (hS ▸ ht.intersection_normalizes_left_residual) hnA
  have hBN := hlocal _ (isPPerfect_embedded_pResidual 2 B)
    (hS ▸ ht.intersection_normalizes_right_residual) hnB
  have hcore := ht.normal_intersection_le_twoCore N
    ((ht.left_subnormal_core_iff_not_residual_le N (Normal.isSubnormal inferInstance)).mpr hAN)
    ((ht.right_subnormal_core_iff_not_residual_le N (Normal.isSubnormal inferInstance)).mpr hBN)
  have hJN : elementaryAbelianMaxJ (S : Subgroup D) ≤ N :=
    (le_conjugateSpanBy _ _).trans (le_comap_map q J)
  have hJS : elementaryAbelianMaxJ (S : Subgroup D) ≤ (S : Subgroup D) :=
    sSup_le fun _ h => h.1
  apply hJ
  exact ((le_inf (hJS.trans hS.symm.le) hJN).trans hcore).trans
    (le_centralizer_iff.mp hr.le_centralizer_pCore)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The escaping cubic has nonnormal image under the literal point-span action. -/
theorem cubic_generated_right_action_not_normal_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ ((Y.subgroupOf D).map q).Normal := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans
    (h.chosen.le_sylow.trans (le_sup_right.trans le_sup_right))
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  change ¬ ((Y.subgroupOf D).map q).Normal
  intro hnY
  let := hnY
  let N := ((Y.subgroupOf D).map q).comap q
  let : N.Normal := inferInstanceAs (((Y.subgroupOf D).map q).comap q).Normal
  have hN : N.map D.subtype = Y ⊔ (D ⊓ centralizer (W : Set G)) := by
    change (((Y.subgroupOf D).map q).comap q).map D.subtype = _
    rw [comap_map_eq,QuotientGroup.ker_mk',Subgroup.map_sup,
      map_subgroupOf_eq_of_le hYD,map_centralizer_subtype,map_subgroupOf_eq_of_le hWD]
  have hDN : D ≤ normalizer (N.map D.subtype : Set G) :=
    (show D = (⊤ : Subgroup D).map D.subtype by rw [←MonoidHom.range_eq_map,range_subtype]).le.trans
      ((map_mono le_normalizer_of_normal).trans (N.le_normalizer_map D.subtype))
  have hNC : N.map D.subtype ≤ centralizer (F.Vi 1 : Set G) := by
    rw [hN]
    exact sup_le (hYH.trans (normalizer_le_centralizer_of_card_two _
      (by simpa using F.card 1 (by decide))))
      (inf_le_right.trans (centralizer_le (le_conjugateSpanBy _ _)))
  have hYC : Y ≤ centralizer (W : Set G) :=
    (hN ▸ le_sup_left).trans
      (le_centralizer_conjugateSpanBy_of_normalizes (N.map D.subtype) _ D hDN hNC)
  have hYker : Y.subgroupOf D ≤ C := by
    intro y hy w hw
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hYC hy) w hw
  have hbot : (Y.subgroupOf D).map q = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hYker)
  have ho := cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
  exact ho (hbot ▸ bot_le)

/-- The original full point-normality interface. -/
theorem cubic_generated_right_action_not_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ ((Y.subgroupOf D).map q).Normal := by
  apply cubic_generated_right_action_not_normal_of_normalizes_point
    (h := h) (structural := structural) (Y := Y) (hYH := hYH)
    (hout := hout)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Source 14.5.9: the original Thompson subgroup centralizes the actual
point span of the escaping cubic completion. -/
theorem cubic_generated_thompson_centralizes_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (conjugateSpanBy (F.Vi 1) (F.P L ⊔ (Y ⊔ (T : Subgroup G))) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hWD : W ≤ D := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans hTD))
  let S := T.subtype hTD
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hr := cubic_generated_span_reduced h hab structural previous Y hYH he
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  have hres := cubic_action_residuals (F := F) h structural Y hYp hYT
  have hnA : ¬ (((pResidual 2 A).map A.subtype).map q).Normal := by
    rw [hres.1]
    intro hN
    let := hN
    exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
      le_normalizer_of_normal
  have hnB : ¬ (((pResidual 2 B).map B.subtype).map q).Normal := by
    rw [hres.2]
    exact cubic_generated_right_action_not_normal_of_normalizes_point h structural Y hYH hYL hout
  have hS : A ⊓ B = (S : Subgroup D) := by
    have hi : F.P L ⊓ (Y ⊔ (T : Subgroup G)) = (T : Subgroup G) :=
      le_antisymm ((inf_le_inf_left _ (sup_le hYH (F.invariant 1))).trans_eq
        (plane_parabolic_inf_point h structural))
        (le_inf (F.binary_sylow_le_P L) le_sup_right)
    exact congrArg (fun X : Subgroup G => X.subgroupOf D) hi
  have hsol := cubic_generated_solvable_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  have h3 := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin
    3 Nat.prime_three (by decide)
  have hh := CubicThompson_goldschmidt_thompson_centralizes ht (W.subgroupOf D) hr hsol h3 S hS hnA hnB
  have hm := map_mono (f := D.subtype) hh
  rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD,
    map_centralizer_subtype,map_subgroupOf_eq_of_le hWD] at hm
  exact hm.trans inf_le_right

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (conjugateSpanBy (F.Vi 1) (F.P L ⊔ (Y ⊔ (T : Subgroup G))) : Set G) := by
  apply cubic_generated_thompson_centralizes_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Source 14.5.9: J(T) is the Thompson subgroup of the literal two-core,
and is normalized by the full cubic completion. -/
theorem cubic_generated_thompson_normalizer_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ D.pCoreIn 2 := by
    rw [←cubic_generated_sylow_centralizer_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he]
    exact le_inf hJT (cubic_generated_thompson_centralizes_of_normalizes_point
      h hab structural previous faithful Y hYH hYL hYp hYT hout he)
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hQT : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨a,ha,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTD) ha
  have hJ := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) (D.pCoreIn 2) hJQ hQT
  refine ⟨hJ,?_⟩
  rw [←hJ]
  have hnQ : D ≤ normalizer (D.pCoreIn 2 : Set G) := by
    have hh := (pCore 2 D).le_normalizer_map D.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  exact hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ _)

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_normalizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  apply cubic_generated_thompson_normalizer_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The Thompson subgroup escapes the original point core. If it were in R₁,
14.3.9(2) would make it normal in LT, and uniqueness over LT would contradict
its normalization by the escaping cubic completion. -/
theorem cubic_generated_thompson_escape_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ h => h.1
  have hJp : IsPGroup 2 J := T.isPGroup'.to_le hJT
  have hTne : (T : Subgroup G) ≠ ⊥ := fun hz =>
    h.chosen.ne_bot (eq_bot_iff.mpr (h.chosen.le_sylow.trans hz.le))
  have hJne : J ≠ ⊥ := elementaryAbelianMaxJ_ne_bot_of_finite_pGroup
    (T : Subgroup G) T.isPGroup' hTne
  intro hJR
  have hnJ := Chapter14.Section03.ThompsonSourceAt.thompson_normal h F structural hJR
  have hLJ : L ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hnJ
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hJM : normalizer (J : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from
          ⟨hM,hAM⟩)) hJp hJne hLJ
  have hDJ := (cubic_generated_thompson_normalizer_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2
  exact hout (((le_sup_left.trans le_sup_right : Y ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))).trans
    hDJ).trans hJM)

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 := by
  apply cubic_generated_thompson_escape_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The first two assertions of 14.5.10 on the literal groups: J(T) is the
Thompson subgroup of O₂(L₂T), but leaves O₂(LT). -/
theorem cubic_generated_thompson_parabolic_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ D.pCoreIn 2 := by
    rw [←cubic_generated_sylow_centralizer_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he]
    exact le_inf hJT (cubic_generated_thompson_centralizes_of_normalizes_point
      h hab structural previous faithful Y hYH hYL hYp hYT hout he)
  have hQP : D.pCoreIn 2 ≤ (F.P L).pCoreIn 2 := by
    have hh := pCore_le_map_of_sylow_le (T.subtype hTD) ((F.P L).subgroupOf D)
      (fun _ hx => F.binary_sylow_le_P L hx)
    have hm := map_mono (f := D.subtype) hh
    let e := subgroupOfEquivOfLe (show F.P L ≤ D from le_sup_left)
    have heq : D.subtype.comp ((F.P L).subgroupOf D).subtype =
        (F.P L).subtype.comp e.toMonoidHom := rfl
    rw [map_map,heq,←map_map,pCore_map_iso] at hm
    exact hm
  have hPT : (F.P L).pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨a,ha,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype (F.binary_sylow_le_P L)) ha
  refine ⟨elementaryAbelianMaxJ_eq_of_intermediate _ _ (hJQ.trans hQP) hPT,?_⟩
  intro hJQ₀
  have hQ₀R : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ F.Ri L 1 := by
    have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)
    exact (le_inf (hQT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_LT)
  exact cubic_generated_thompson_escape_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he (hJQ₀.trans hQ₀R)

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_parabolic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply cubic_generated_thompson_parabolic_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The literal order-four chief interval supplies all premises of the Thompson
step, with its selected Y, original star kernel and symmetric-three quotient. -/
theorem extraspecial_four_interval_cubic_thompson
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol⟩ :=
    extraspecial_four_interval_cubic_solvable h hab structural previous faithful hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hJQ,hJN⟩ := cubic_generated_thompson_normalizer h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  obtain ⟨hJP,hJout⟩ := cubic_generated_thompson_parabolic h hab structural previous faithful hn
    Y hYH hYp hYT hout he
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    cubic_generated_thompson_centralizes h hab structural previous faithful hn Y hYH hYp hYT hout he,
    hJQ,hJN,hJP,hJout,
    cubic_generated_thompson_escape h hab structural previous faithful hn Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original cubic residual is generated by its J₁ commutator

The natural action on the original V sends J₁(T) onto the entire marked
Sylow subgroup of SL₃(2), since the preceding Thompson escape excludes a
trivial J(T) image. Its kernel is a normal two-subgroup of LT and hence
lies in the two-core of the plane parabolic P. Thus J₁(T) escapes O₂(P).
Since P/O₂(P) is the actual S₃, the Sylow subgroup is maximal in P;
the residual commutator theorem gives [L₂,J₁(T)] = L₂.

The equality is transported through the literal D/C_D(W) action, where
D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩. Nonnormality of the L₂ image forces the
J₁(T) image to be nontrivial. The final application keeps the selected Y,
its exact star kernel and its S₃ quotient from the original order-four
chief interval. The subsequent solvable containment and interval
exclusions remain to be proved.

Source: Aschbacher–Smith, 14.3.9(3), pp.992–993; 14.5.10 and the
representation step after 14.5.13, pp.1015–1017; the application in
14.7.20(2), p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The near-maximal Thompson subgroup leaves the actual plane core as soon
as the maximal Thompson subgroup leaves O₂(LT). This is the needed i = 2
case of source 14.3.9(3). -/
theorem thompson_one_plane_core_escape
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ¬ thompsonJ (T : Subgroup G) 1 ≤ (F.P L).pCoreIn 2 := by
  obtain ⟨e,q,hq,hq2,ha,hker,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSourceAt.exists_marking h F structural
  let H := L ⊔ (T : Subgroup G)
  let S : Sylow 2 H := T.subtype le_sup_right
  have hTS : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hTS]
  have hk : q.ker ≤ pCore 2 H := le_sSup ⟨inferInstance,hq2⟩
  have hJk : ¬ elementaryAbelianMaxJ (S : Subgroup H) ≤ q.ker := by
    intro hle
    apply hJ
    rw [←hJmap]
    exact map_mono (hle.trans hk)
  have hrT : 1 < twoRank (T : Subgroup G) := by
    obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
    have hc := hA.2.2 V h.chosen.le_sylow h.chosen.elementary
    rw [h.seed_card,elementaryAbelianMaxSubgroups_card_eq _ _ hA,
      maxOrder_eq_two_pow_rank] at hc
    have hh : 3 ≤ twoRank (T : Subgroup G) :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    omega
  have hrS : 1 < twoRank (S : Subgroup H) := by
    rw [←twoRank_map_injective H.subtype H.subtype_injective,hTS]
    exact hrT
  have himage := linear_three_thompson_one_image S q hq hT hrS hJk
  have hfull : (S : Subgroup H) ≤ thompsonJ (S : Subgroup H) 1 ⊔ q.ker := by
    rw [←comap_map_eq]
    apply map_le_iff_le_comap.mp
    exact hT.trans himage.symm |>.le
  have hmap : (thompsonJ (S : Subgroup H) 1).map H.subtype =
      thompsonJ (T : Subgroup G) 1 := by
    rw [←thompsonJ_map_injective H.subtype H.subtype_injective,hTS]
  have hkp : q.ker.map H.subtype ≤ (F.P L).pCoreIn 2 := by
    have hkT : q.ker.map H.subtype ≤ (T : Subgroup G) :=
      (map_mono (hq2.le_sylow_of_normal S)).trans_eq hTS
    exact (le_inf (hkT.trans (F.binary_sylow_le_P L)) (map_mono hk)).trans
      (inf_pCoreIn_le_of_le 2 (show F.P L ≤ H from inf_le_left))
  intro hle
  have hTcore : (T : Subgroup G) ≤ (F.P L).pCoreIn 2 := by
    have hh := map_mono (f := H.subtype) hfull
    rw [hTS,Subgroup.map_sup,hmap] at hh
    exact hh.trans (sup_le hle hkp)
  let SP := T.subtype (F.binary_sylow_le_P L)
  have hcore : (SP : Subgroup (F.P L)) = pCore 2 (F.P L) := by
    apply le_antisymm ?_ (pCore_isPGroup.le_sylow_of_normal SP)
    intro t ht
    obtain ⟨a,ha,he⟩ := hTcore ht
    have he' : a = t := Subtype.ext he
    exact he' ▸ ha
  have hi := SymmetricThreeTwoCore.sylow_index_three (planeParabolicQuotientEquiv h structural) SP
  rw [hcore,SymmetricThreeTwoCore.core_index (planeParabolicQuotientEquiv h structural)] at hi
  omega

private theorem CubicThompsonCommutator_unique_maximal_of_prime_index {X : Type*} [Group X] [Finite X]
    (S : Subgroup X) (hi : S.index.Prime) : Order.HasUniqueMaximalOver S ⊤ := by
  have hm : IsCoatom S := by
    refine ⟨fun he => ?_,fun N hN => ?_⟩
    · exact hi.ne_one (he ▸ index_top)
    · have hd := index_dvd_of_le hN.le
      rcases (Nat.dvd_prime hi).mp hd with hh | hh
      · exact index_eq_one.mp hh
      · have he := relIndex_mul_index hN.le
        rw [hh] at he
        have hn : S.relIndex N = 1 := Nat.eq_of_mul_eq_mul_right hi.pos (by simpa using he)
        exact (hN.not_ge (relIndex_eq_one.mp hn)).elim
  refine ⟨hm.lt_top,S,⟨le_rfl,hm.covBy_top⟩,?_⟩
  intro M hM
  exact (hm.covBy_top.eq_or_eq hM.1 hM.2.le).resolve_right hM.2.ne

/-- Source 14.5.10's remaining equality on the original cubic residual. -/
theorem cubic_generated_thompson_one_commutator_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 := by
  have hescape := thompson_one_plane_core_escape (F := F) h structural
    (cubic_generated_thompson_parabolic_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2
  let S := T.subtype (F.binary_sylow_le_P L)
  let J := thompsonJ (S : Subgroup (F.P L)) 1
  have hmap : J.map (F.P L).subtype = thompsonJ (T : Subgroup G) 1 := by
    rw [←thompsonJ_map_injective (F.P L).subtype (F.P L).subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.binary_sylow_le_P L)]
  have hJ : ¬ J ≤ pCore 2 (F.P L) := by
    intro hh
    apply hescape
    rw [←hmap]
    exact map_mono hh
  have hi := SymmetricThreeTwoCore.sylow_index_three (planeParabolicQuotientEquiv h structural) S
  have hc := commutator_twoResidual_eq_of_normal_sylow_subgroup S
    (CubicThompsonCommutator_unique_maximal_of_prime_index _ (by simpa only [hi] using Nat.prime_three)) J
    (thompsonJ_le _ _) (le_normalizer_thompsonJ _ _) hJ
  have hm := congrArg (map (F.P L).subtype) hc
  rwa [map_commutator,plane_parabolic_residual h structural,hmap] at hm

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_one_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 := by
  apply cubic_generated_thompson_one_commutator_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The J₁(T) commutator survives in the literal point-span action quotient;
in particular the actor image needed in the solvable representation argument
is nontrivial. -/
theorem cubic_generated_thompson_one_action_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ⁅((F.Li L 2).subgroupOf D).map q,
      ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q⁆ =
        ((F.Li L 2).subgroupOf D).map q ∧
      ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q ≠ ⊥ := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
  have hXD : F.Li L 2 ≤ D := by
    dsimp only [D]
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hJD : thompsonJ (T : Subgroup G) 1 ≤ D :=
    (thompsonJ_le _ _).trans (le_sup_right.trans le_sup_right)
  have hc : ⁅(F.Li L 2).subgroupOf D,(thompsonJ (T : Subgroup G) 1).subgroupOf D⁆ =
      (F.Li L 2).subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hXD,map_subgroupOf_eq_of_le hJD]
    exact cubic_generated_thompson_one_commutator_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  have hm := congrArg (map q) hc
  rw [map_commutator] at hm
  refine ⟨hm,?_⟩
  intro hzero
  have hXzero : ((F.Li L 2).subgroupOf D).map q = ⊥ := by
    rw [hzero,commutator_bot_right] at hm
    exact hm.symm
  have ho := cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
  apply ho
  change (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _)
  rw [hXzero,normalizer_eq_top]
  exact le_top

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_one_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ⁅((F.Li L 2).subgroupOf D).map q,
      ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q⁆ =
        ((F.Li L 2).subgroupOf D).map q ∧
      ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q ≠ ⊥ := by
  apply cubic_generated_thompson_one_action_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- J₁(T) acts nontrivially on the original cubic point span. -/
theorem cubic_generated_thompson_one_not_central_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ thompsonJ (T : Subgroup G) 1 ≤
      centralizer (conjugateSpanBy (F.Vi 1) (F.P L ⊔ (Y ⊔ (T : Subgroup G))) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  intro hz
  have hnz := (cubic_generated_thompson_one_action_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2
  apply hnz
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  intro j hj w hw
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hz hj) w hw

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_one_not_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ¬ thompsonJ (T : Subgroup G) 1 ≤
      centralizer (conjugateSpanBy (F.Vi 1) (F.P L ⊔ (Y ⊔ (T : Subgroup G))) : Set G) := by
  apply cubic_generated_thompson_one_not_central_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original order-four chief interval supplies the J₁ commutator and
nontrivial point-span action, retaining Y and its exact quotient kernels. -/
theorem extraspecial_four_interval_cubic_thompson_one
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR⟩ :=
    extraspecial_four_interval_cubic_thompson h hab structural previous faithful hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,
    cubic_generated_thompson_one_commutator h hab structural previous faithful hn
      Y hYH hYp hYT hout he,
    cubic_generated_thompson_one_not_central h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The odd-prime reduction for the original solvable cubic action

For the original completion D = ⟨L₂,Y,T⟩, failure of its faithful action
quotient D/C_D(W) to be a {2,3}-group forces L₂ to move an odd prime core
with prime greater than three. This follows from F.6.9 and the decomposition
of the embedded Fitting residual into the complementary prime cores.
Coprime detection then selects an actual noncyclic supercritical subgroup
on which the L₂ image is nontrivial and still generated by its commutator
with the J₁(T) image.

The original order-four chief interval supplies every premise, retaining
its chosen Y, exact star kernel and S₃ quotient. The noncyclic supercritical
alternative still requires the rank and representation exclusion of
14.5.11; this module does not assert that exclusion or the later containment.

Source: Aschbacher–Smith, F.6.9, p.306; the initial reduction in 14.5.11,
pp.1015–1016; its application in 14.7.20(2), p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem CubicPrimeReduction_exists_moved_prime_core
    {D E : Type u} [Group D] [Finite D] [Group E] [Finite E] {C : GroupClass.{u}}
    (hE : IsSQTK C E) (f : E →* D) (hf : Function.Surjective f)
    (hs : Group.IsSolvable D) {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (hc : pCore 2 D = ⊥)
    (hout : ¬ IsPiGroup twoThreePrimes D) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ¬ (pResidual 2 A).map A.subtype ≤ centralizer (pCore p D : Set D) := by
  by_contra! hn
  apply hout
  apply ChapterF.SourceAssembly.isTwoThreeGroup_of_left_residual_centralizes_fitting_residual
    hE f hf hs ht
  apply le_centralizer_iff.mpr
  rw [fitting_pResidual_eq_sup_prime_cores]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp3
  by_cases hp2 : p.1.1 = 2
  · rw [hp2,hc]
    exact bot_le
  have hprime : p.1.1.Prime := Fact.out
  have hpgt : 3 < p.1.1 := by
    have h2 := hprime.two_le
    omega
  exact le_centralizer_iff.mp (hn p.1.1 hprime hpgt)

private theorem CubicPrimeReduction_coprime_card_of_twoThree {X : Type*} [Group X] [Finite X]
    (hX : IsPiGroup twoThreePrimes X) {p : ℕ} (hp : p.Prime) (hbig : 3 < p) :
    Nat.Coprime p (Nat.card X) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hh := (IsPiGroup_iff _ _).mp hX ⟨p,hp⟩ hd
  change p = 2 ∨ p = 3 at hh
  rcases hh with hh | hh <;> omega

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original faithful cubic quotient is a {2,3}-group unless a noncyclic
supercritical prime core carries the nontrivial residual commutator action. -/
theorem cubic_generated_action_prime_reduction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let X := ((F.Li L 2).subgroupOf D).map q
  let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
  change IsPiGroup twoThreePrimes (D ⧸ C) ∨ _
  by_cases h23 : IsPiGroup twoThreePrimes (D ⧸ C)
  · exact Or.inl h23
  apply Or.inr
  let A := ((F.P L).subgroupOf D).map q
  let B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q
  have ht := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hs := cubic_generated_solvable_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  let : Group.IsSolvable D := hs
  have hsq := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  have hres : (pResidual 2 A).map A.subtype = X := by
    rw [←map_embedded_pResidual]
    exact congrArg (map q) (cubic_action_residuals (F := F) h structural Y hYp hYT).1
  obtain ⟨p,hp,hbig,hm⟩ := CubicPrimeReduction_exists_moved_prime_core hsq q
    (QuotientGroup.mk'_surjective C) inferInstance ht.2.1 ht.2.2 h23
  rw [hres] at hm
  let : Fact p.Prime := ⟨hp⟩
  have hXA : X ≤ A := hres ▸ map_subtype_le (pResidual 2 A)
  have hX23 : IsPiGroup twoThreePrimes X :=
    (ChapterF.SourceAssembly.local_isTwoThreeGroup ht.2.1).of_injective
      (inclusion hXA) (inclusion_injective hXA)
  have hcomm : ⁅X,J⁆ = X := (cubic_generated_thompson_one_action_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he).1
  obtain ⟨R,hR,hnc,hr,heq⟩ := supercritical_commutator_movement X J (pCore p (D ⧸ C))
    (hp.odd_of_ne_two (by omega)) pCore_isPGroup
    (CubicPrimeReduction_coprime_card_of_twoThree hX23 hp hbig) hcomm hm
  let : R.Characteristic := hR.characteristic
  refine ⟨p,hp,R,hR,hbig,inferInstance,hnc,?_,hr,heq⟩
  intro hz
  apply hr
  apply (Subgroup.map_eq_bot_iff _).mpr
  intro x hx
  apply MulEquiv.ext
  intro r
  apply Subtype.ext
  apply Subtype.ext
  change x * (r.val : D ⧸ C) * x⁻¹ = (r.val : D ⧸ C)
  have hc := hz hx (r.val : D ⧸ C) (mem_map_of_mem (pCore p (D ⧸ C)).subtype r.property)
  rw [←hc,mul_inv_cancel_right]

/-- The original full point-normality interface. -/
theorem cubic_generated_action_prime_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a := by
  apply cubic_generated_action_prime_reduction_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original order-four chief interval reduces to a {2,3}-action quotient
or a moved noncyclic supercritical odd subgroup, with the same Y and exact
quotient kernels throughout. -/
theorem extraspecial_four_interval_cubic_prime_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      let X := ((F.Li L 2).subgroupOf D).map q
      let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
      IsPiGroup twoThreePrimes (D ⧸ C) ∨
        ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
          (hR : IsSupercriticalPSubgroup p R),
          3 < p ∧
          letI : R.Characteristic := hR.characteristic
          let a := (MulAut.characteristic R).comp
            (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
          (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
          ¬ IsCyclic R ∧
          ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
          X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_prime_reduction h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Actual elementary actors in the moved-prime cubic branch

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the identity [L₂,J₁(T)] = L₂
forces a near-maximum elementary subgroup A of the original T to move
every normal odd subgroup moved by L₂ in D/C_D(W). The literal action
of A on W has fixed codimension at most its image rank plus one.
A moving involution in that image has cyclic centralizer in the odd
subgroup and full p-centralizer rank at most one. The rank-two section
theorem is applied to the original SQTK cover D, retaining its quotient
map throughout. Coprime fixed-point generation then bounds the selected
actor's image on the actual supercritical subgroup by order four, using
the literal characteristic-restriction map from the preceding reduction.

The non-{2,3} alternative keeps the previously constructed supercritical
subgroup and its commutator identity. The order-four chief interval
supplies all the premises with the same Y, star kernel, and S₃ quotient.
The remaining representation exclusion of this alternative and the
subsequent solvable containment in 14.5.3(2) are not asserted here.

Source: Aschbacher–Smith 14.5.11, printed pp.1015–1016; its A.1.31(1)
and B.2.4(1) inputs; and the interval use in 14.7.20(2), printed p.1049,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every moved normal odd subgroup in the original cubic action has a
near-maximum elementary actor with controlled codimension and cyclic
involution centralizer. The prime rank is taken before quotienting. -/
theorem cubic_generated_moved_prime_actor_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let U := W.subgroupOf D
    letI : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 U :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (U : Set D)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (p : ℕ) (_ : p.Prime) (R : Subgroup (D ⧸ C)), R.Normal → Odd p →
      IsPGroup p R → ¬ ((F.Li L 2).subgroupOf D).map q ≤ centralizer (R : Set (D ⧸ C)) →
      ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
        let B := (A.subgroupOf D).map q
        IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
        ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧ t ∉ centralizer (R : Set (D ⧸ C)) ∧
          IsCyclic (R ⊓ centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
          primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  dsimp only
  intro p hp R hnR ho hR hm
  let : R.Normal := hnR
  let : Fact p.Prime := ⟨hp⟩
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hUS : U ≤ (T : Subgroup G).subgroupOf D := by
    have hr := (cubic_generated_span_reduced h hab structural previous Y hYH he).le_pCore
    exact hr.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hTD))
  have hrank : primeRank p D ≤ 2 :=
    (cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin p hp ho
  have hc := (cubic_generated_thompson_one_action_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).1
  rw [←thompsonJ_subgroupOf D (T : Subgroup G) hTD 1] at hc
  obtain ⟨A,hA,helem,hcod,t,ht,ht2,htR,hcyc,hcr⟩ := near_maximum_prime_movement ((T : Subgroup G).subgroupOf D) U hUS q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    (((F.Li L 2).subgroupOf D).map q) R ho hrank hR hc hm
  have hAf : A.map D.subtype ∈ thompsonFamily (T : Subgroup G) 1 := by
    have hh := (thompsonFamily_map_iff_of_injective D.subtype D.subtype_injective
      ((T : Subgroup G).subgroupOf D) A 1).mpr hA
    rwa [map_subgroupOf_eq_of_le hTD] at hh
  have hAr : (A.map D.subtype).subgroupOf D = A := by
    exact comap_map_eq_self_of_injective D.subtype_injective A
  refine ⟨A.map D.subtype,hAf,?_⟩
  rw [hAr]
  exact ⟨helem,hcod,t,ht,ht2,htR,hcyc,hcr⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_moved_prime_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let U := W.subgroupOf D
    letI : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
    letI : IsElementaryAbelian 2 U :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (U : Set D)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ∀ (p : ℕ) (_ : p.Prime) (R : Subgroup (D ⧸ C)), R.Normal → Odd p →
      IsPGroup p R → ¬ ((F.Li L 2).subgroupOf D).map q ≤ centralizer (R : Set (D ⧸ C)) →
      ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
        let B := (A.subgroupOf D).map q
        IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
        ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧ t ∉ centralizer (R : Set (D ⧸ C)) ∧
          IsCyclic (R ⊓ centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
          primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  apply cubic_generated_moved_prime_actor_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The non-{2,3} branch carries its actual near-maximum actor and the
rank-one involution centralizer, together with the original supercritical
subgroup and residual commutator identity. -/
theorem cubic_generated_action_prime_actors_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 (W.subgroupOf D) :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (W.subgroupOf D : Set D)
  rcases cubic_generated_action_prime_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 | ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let : (R.map (pCore p (D ⧸ C)).subtype).Characteristic := hchar
  refine Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,?_⟩
  obtain ⟨A,hA,hB,hcod,t,ht,ht2,htR,hcyc,hcr⟩ :=
    cubic_generated_moved_prime_actor_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he p hp (R.map (pCore p (D ⧸ C)).subtype) inferInstance
      (hp.odd_of_ne_two (by omega))
      ((pCore_isPGroup (p := p) (G := D ⧸ C)).to_subgroup R |>.map (pCore p (D ⧸ C)).subtype) hm
  let q := QuotientGroup.mk' C
  let B := (A.subgroupOf D).map q
  let : IsElementaryAbelian 2 B := hB.2
  refine ⟨A,hA,hB,hcod,?_,t,ht,ht2,htR,hcyc,hcr⟩
  exact characteristic_prime_core_action_card_le_four (hp.odd_of_ne_two (by omega)) q
    (QuotientGroup.mk'_surjective C)
    ((cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin
      p hp (hp.odd_of_ne_two (by omega))) R B

/-- The original full point-normality interface. -/
theorem cubic_generated_action_prime_actors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  apply cubic_generated_action_prime_actors_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The actual order-four interval supplies the moved-prime actors on its
literal cubic quotient, retaining Y, its exact star kernel, and the S₃ quotient. -/
theorem extraspecial_four_interval_cubic_prime_actors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      ∃ he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)),
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
        (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      let X := ((F.Li L 2).subgroupOf D).map q
      let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
      let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      IsPiGroup twoThreePrimes (D ⧸ C) ∨
        ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
          (hR : IsSupercriticalPSubgroup p R),
          3 < p ∧
          letI : R.Characteristic := hR.characteristic
          let a := (MulAut.characteristic R).comp
            (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
          (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
          ¬ IsCyclic R ∧
          ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
          X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
          ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
            let B := (A.subgroupOf D).map q
            IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
            ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
              t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
              IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
                centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
              primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_prime_actors h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Removing the elementary actor kernel in the original cubic reduction

In the moved-prime branch of 14.5.11, let B be the image of the selected
near-maximum elementary subgroup of the original T, and put
K₀ = C_B(R), U₀ = C_W(K₀). Thompson A×B keeps the actual odd subgroup R
faithful on U₀. Its normality identifies C_B(U₀) exactly with K₀.
Counting elementary replacements in the original T bounds the fixed
codimension of B/K₀ by its rank plus one. Its order is at most four,
so the action is cubic, has fixed codimension at most three, and has
cubic ratio at most two.

The original order-four interval supplies every input with the same Y,
star kernel and S₃ quotient. These are the actual representation and
kernel reductions; the further prime exclusion and solvable containment
are not asserted here.

Source: Aschbacher–Smith 14.5.11, pp.1015–1016, its A.1.18 and B.2.4
inputs, and the interval application in 14.7.20(2), p.1049,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The moved-prime alternative has a literal fixed-space action with its exact
kernel, a faithful odd subgroup, a cubic actor of order at most four, and
cubic ratio at most two. -/
theorem cubic_generated_action_prime_fixed_actors_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  rcases cubic_generated_action_prime_actors_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 |
    ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,t,ht,ht2,htR,hcyc,hcr⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let R₀ := R.map (pCore p (D ⧸ C)).subtype
  let : R₀.Characteristic := hchar
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hAD : A ≤ D := hA.1.trans hTD
  have hA₀ : A.subgroupOf D ∈ thompsonFamily ((T : Subgroup G).subgroupOf D) 1 := by
    apply (thompsonFamily_map_iff_of_injective D.subtype D.subtype_injective
      ((T : Subgroup G).subgroupOf D) (A.subgroupOf D) 1).mp
    rw [map_subgroupOf_eq_of_le hTD,map_subgroupOf_eq_of_le hAD]
    exact hA
  have hUS : U ≤ (T : Subgroup G).subgroupOf D := by
    have hr := (cubic_generated_span_reduced h hab structural previous Y hYH he).le_pCore
    exact hr.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hTD))
  have ho := hp.odd_of_ne_two (by omega)
  have hfixed := near_maximum_prime_fixed_action ((T : Subgroup G).subgroupOf D) U
    hUS q (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hA₀ ho
    ((cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin p hp ho)
    R₀ ((pCore_isPGroup (p := p) (G := D ⧸ C)).to_subgroup R |>.map (pCore p (D ⧸ C)).subtype)
    (fun hh => htR (hh ht))
  exact Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,
    t,ht,ht2,htR,hcyc,hcr,hfixed⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_action_prime_fixed_actors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 := by
  apply cubic_generated_action_prime_fixed_actors_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The actual order-four interval supplies the moved-prime actors on its
literal cubic quotient, retaining Y, its exact star kernel, and the S₃ quotient. -/
theorem extraspecial_four_interval_cubic_prime_fixed_actors
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      ∃ he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)),
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
        (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      let X := ((F.Li L 2).subgroupOf D).map q
      let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
      let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      IsPiGroup twoThreePrimes (D ⧸ C) ∨
        ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
          (hR : IsSupercriticalPSubgroup p R),
          3 < p ∧
          letI : R.Characteristic := hR.characteristic
          let a := (MulAut.characteristic R).comp
            (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
          (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
          ¬ IsCyclic R ∧
          ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
          X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
          ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
            let B := (A.subgroupOf D).map q
            IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
            ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
              t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
              IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
                centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
              primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_prime_fixed_actors h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The quintic plane in the original moved-prime cubic branch

Apply D.2.13 to the literal restricted odd-group-by-elementary-actor
join. Its two-core is trivial because the elementary image acts faithfully
on the odd subgroup. The prime is five; the near-maximum codimension
bound forces the elementary image to have order two and its odd
commutator to have order five, with a binary support of dimension four.

Coprime generation and the original moving involution's cyclic centralizer
then bound the noncyclic supercritical subgroup by 25. Its exponent gives
an actual elementary-plane equivalence. Every action and kernel here is
inherited from the original cubic quotient and original T.

This excludes all moved primes other than five and the nonabelian
supercritical branch. The remaining quintic plane exclusion and source
14.5.3 containment still require proofs.

Source: Aschbacher–Smith 14.5.11, printed pp.1015–1016, and its
14.7.20(2) interval application, p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The moved-prime alternative is an actual elementary quintic plane, with an
order-two restricted actor and a faithful four-dimensional moving support. -/
theorem cubic_generated_action_prime_five_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 ∧
            p = 5 ∧ Nat.card R = 25 ∧ IsElementaryAbelian 5 R ∧
            Nonempty (R ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
            rank I = 1 ∧ Nat.card I = 2 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I = 2 ∧
            Nat.card (⁅R₀,B⁆ : Subgroup (D ⧸ C)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator ρ U₀ ⁅R₀,B⁆) = 4 := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  rcases cubic_generated_action_prime_fixed_actors_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 |
    ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,t,ht,ht2,htR,hcyc,hcr,
      hkR,hkB,hI,hcardI,hcodI,hcod3,hcubI,hratio⟩
  · exact Or.inl h23
  let : Fact p.Prime := ⟨hp⟩
  let : R.Characteristic := hR.characteristic
  let R₀ := R.map (pCore p (D ⧸ C)).subtype
  let B := (A.subgroupOf D).map q
  let : R₀.Characteristic := hchar
  let : IsElementaryAbelian 2 B := hB.2
  have hRp : IsPGroup p R₀ :=
    (pCore_isPGroup (p := p) (G := D ⧸ C)).to_subgroup R |>.map (pCore p (D ⧸ C)).subtype
  obtain ⟨hp5,hrI,hcI,hdI,hcomm5,hdim⟩ := ChapterD.prime_fixed_small_actor ρ
    (NormalElementaryQuotient.representation_injective _ _ _ _) hbig R₀ B hRp hI hcubI hcodI
  let eR : R ≃* R₀ := R.equivMapOfInjective
    (pCore p (D ⧸ C)).subtype (pCore p (D ⧸ C)).subtype_injective
  have heR : Monoid.exponent R₀ ∣ p :=
    (Monoid.exponent_dvd_of_monoidHom eR.symm.toMonoidHom eR.symm.injective).trans hR.exponent_dvd_p
  have hnR : ¬ IsCyclic R₀ := by
    intro hc
    let : IsCyclic R₀ := hc
    exact hncyc (isCyclic_of_injective eR.toMonoidHom eR.injective)
  obtain ⟨hcR,helR⟩ := elementary_plane_of_prime_commutator_cyclic_fixed
    (by omega : p ≠ 2) R₀ B hRp (IsElementaryAbelian.isPGroup 2 B)
    heR hnR t ht hcyc (hcomm5.trans hp5.symm)
  have hcR' : Nat.card R = 25 := by
    rw [Nat.card_congr eR.toEquiv,hcR,hp5]
    rfl
  let : IsElementaryAbelian p R₀ := helR
  have heR' : IsElementaryAbelian 5 R := by
    rw [←hp5]
    exact IsElementaryAbelian.of_injective eR.toMonoidHom eR.injective
  let : IsElementaryAbelian 5 R := heR'
  have heqR := IsElementaryAbelian.nonempty_mulEquiv_plane_of_card
    (p := 5) (show Nat.card R = 5 ^ 2 from hcR')
  exact Or.inr ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,
    t,ht,ht2,htR,hcyc,hcr,hkR,hkB,hI,hcardI,hcodI,hcod3,hcubI,hratio,
    hp5,hcR',heR',heqR,hrI,hcI,hdI,hcomm5,hdim⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_action_prime_five
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    let X := ((F.Li L 2).subgroupOf D).map q
    let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
    let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    IsPiGroup twoThreePrimes (D ⧸ C) ∨
      ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
        (hR : IsSupercriticalPSubgroup p R),
        3 < p ∧
        letI : R.Characteristic := hR.characteristic
        let a := (MulAut.characteristic R).comp
          (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
        (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
        ¬ IsCyclic R ∧
        ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
        X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
        ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
          let B := (A.subgroupOf D).map q
          IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
          ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
            t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
            IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
              centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
            primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 ∧
            p = 5 ∧ Nat.card R = 25 ∧ IsElementaryAbelian 5 R ∧
            Nonempty (R ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
            rank I = 1 ∧ Nat.card I = 2 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I = 2 ∧
            Nat.card (⁅R₀,B⁆ : Subgroup (D ⧸ C)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator ρ U₀ ⁅R₀,B⁆) = 4 := by
  apply cubic_generated_action_prime_five_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The actual order-four interval supplies the moved-prime actors on its
literal cubic quotient, retaining Y, its exact star kernel, and the S₃ quotient. -/
theorem extraspecial_four_interval_cubic_prime_five
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      ∃ he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)),
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
        (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      let X := ((F.Li L 2).subgroupOf D).map q
      let J := ((thompsonJ (T : Subgroup G) 1).subgroupOf D).map q
      let ρ := NormalElementaryQuotient.representation (W.subgroupOf D) q
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
      IsPiGroup twoThreePrimes (D ⧸ C) ∨
        ∃ (p : ℕ) (_ : p.Prime) (R : Subgroup (pCore p (D ⧸ C)))
          (hR : IsSupercriticalPSubgroup p R),
          3 < p ∧
          letI : R.Characteristic := hR.characteristic
          let a := (MulAut.characteristic R).comp
            (MulAut.conjNormal : (D ⧸ C) →* MulAut (pCore p (D ⧸ C)))
          (R.map (pCore p (D ⧸ C)).subtype).Characteristic ∧
          ¬ IsCyclic R ∧
          ¬ X ≤ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
          X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a ∧
          ∃ A ∈ thompsonFamily (T : Subgroup G) 1,
            let B := (A.subgroupOf D).map q
            IsElementaryTwo B ∧ fixedCodim ρ B ≤ rank B + 1 ∧
          Nat.card (B.map a) ≤ 4 ∧
            ∃ t : D ⧸ C, t ∈ B ∧ orderOf t = 2 ∧
              t ∉ centralizer (R.map (pCore p (D ⧸ C)).subtype : Set (D ⧸ C)) ∧
              IsCyclic (R.map (pCore p (D ⧸ C)).subtype ⊓
                centralizer ({t} : Set (D ⧸ C)) : Subgroup (D ⧸ C)) ∧
              primeRank p (centralizer ({t} : Set (D ⧸ C))) ≤ 1 ∧
          let R₀ := R.map (pCore p (D ⧸ C)).subtype
          let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
          let U₀ := fixedSpace ρ K₀
          let I := restrictedSubgroup ρ U₀ B
          subspaceKernel ρ U₀ R₀ = ⊥ ∧ subspaceKernel ρ U₀ B = K₀ ∧
            IsElementaryTwo I ∧ Nat.card I ≤ 4 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ rank I + 1 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I ≤ 3 ∧
            IsCubic (subspaceImageRepresentation ρ U₀) I ∧
            cubicRatio (subspaceImageRepresentation ρ U₀) ≤ 2 ∧
            p = 5 ∧ Nat.card R = 25 ∧ IsElementaryAbelian 5 R ∧
            Nonempty (R ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) ∧
            rank I = 1 ∧ Nat.card I = 2 ∧
            fixedCodim (subspaceImageRepresentation ρ U₀) I = 2 ∧
            Nat.card (⁅R₀,B⁆ : Subgroup (D ⧸ C)) = 5 ∧
            Module.finrank (ZMod 2) (subspaceCommutator ρ U₀ ⁅R₀,B⁆) = 4 := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_prime_five h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original cubic action quotient is a {2,3}-group

The only remaining moved odd-prime branch is a quintic plane. Equality in
the near-maximum fixed-space bound, together with J(T)'s centralization
of the literal point span, kills the restricted actor kernel. The resulting
involution has fixed codimension two on the whole span. Its canonical
order-five support is normalized by the two-perfect cubic image, forcing
that image to centralize the quintic plane and contradicting its movement.

Thus the actual quotient D/C_D(W) is a {2,3}-group. Its trivial two-core
places O_{3′}(D) in C_D(W), giving the compatible surjection from the original
prime-to-three core quotient. The order-four chief interval supplies all
premises while retaining Y, its exact star kernel and its S₃ quotient.

These are the two clauses of 14.5.11 in the original normal-point branch.
The later solvable containment and residual classification remain separate.
Source: Aschbacher–Smith 14.5.11, printed pp.1015–1016, and the
14.7.20(2) interval application, p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open ChapterB Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- Exclusion of the last moved-prime branch for the literal cubic action. -/
theorem cubic_generated_action_twoThree_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    IsPiGroup twoThreePrimes (D ⧸ C) := by
  classical
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U :=
    (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
  let C := centralizer (U : Set D)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  rcases cubic_generated_action_prime_five_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he with h23 |
    ⟨p,hp,R,hR,hbig,hchar,hncyc,hm,hmove,hcomm,A,hA,hB,hcod,hcard,t,ht,ht2,htR,hcyc,hcr,
      hkR,hkB,hI,hcardI,hcodI,hcod3,hcubI,hratio,
      hp5,hcR,helR,heR,hrI,hcI,hdI,hcomm5,hdim⟩
  · exact h23
  subst p
  let : R.Characteristic := hR.characteristic
  let R₀ := R.map (pCore 5 (D ⧸ C)).subtype
  let : R₀.Characteristic := hchar
  let : IsElementaryAbelian 5 R := helR
  let : IsElementaryAbelian 5 R₀ := IsElementaryAbelian.map _
  let B := (A.subgroupOf D).map q
  let K₀ := B ⊓ centralizer (R₀ : Set (D ⧸ C))
  let U₀ := fixedSpace ρ K₀
  let I := restrictedSubgroup ρ U₀ B
  let : IsElementaryAbelian 2 B := hB.2
  change rank I = 1 at hrI
  change Nat.card I = 2 at hcI
  change fixedCodim (subspaceImageRepresentation ρ U₀) I = 2 at hdI
  change subspaceKernel ρ U₀ B = K₀ at hkB
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hAD : A ≤ D := hA.1.trans hTD
  have hA₀ : A.subgroupOf D ∈ thompsonFamily ((T : Subgroup G).subgroupOf D) 1 := by
    apply (thompsonFamily_map_iff_of_injective D.subtype D.subtype_injective
      ((T : Subgroup G).subgroupOf D) (A.subgroupOf D) 1).mp
    rw [map_subgroupOf_eq_of_le hTD,map_subgroupOf_eq_of_le hAD]
    exact hA
  have hUS : U ≤ (T : Subgroup G).subgroupOf D := by
    have hr := (cubic_generated_span_reduced h hab structural previous Y hYH he).le_pCore
    exact hr.trans (pCore_isPGroup.le_sylow_of_normal (T.subtype hTD))
  have hJC : elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf D) ≤ centralizer (U : Set D) := by
    have hh := cubic_generated_thompson_centralizes_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
    intro a ha w hw
    have ha' : (a : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) := by
      have hm := mem_map_of_mem D.subtype ha
      rwa [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
        map_subgroupOf_eq_of_le hTD] at hm
    exact Subtype.ext (hh ha' w hw)
  have hkzero : K₀ = ⊥ := near_maximum_fixed_saturated_kernel
    ((T : Subgroup G).subgroupOf D) U hUS hJC q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) hA₀
    K₀ inf_le_left hkB (by change fixedCodim (subspaceImageRepresentation ρ U₀) I = rank I + 1; omega)
  have hBs : B ≤ subspaceStabilizer ρ U₀ :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ B K₀
      (commutator_eq_bot_iff_le_centralizer.mpr
        (B.le_centralizer.trans (centralizer_le inf_le_left)))
  have hcardB : Nat.card B = 2 := by
    have hh := card_subspaceKernel_mul_image ρ U₀ B hBs
    rw [hkB,hkzero,card_bot,one_mul] at hh
    exact hh.symm.trans hcI
  have hdB : fixedCodim ρ B = 2 := by
    have hh := fixedCodim_restrictedSubgroup ρ U₀ B hBs
    have hu : U₀ = ⊤ := by dsimp only [U₀]; rw [hkzero,fixedSpace_bot]
    rw [hu,top_inf_eq,finrank_top] at hh
    change fixedCodim (subspaceImageRepresentation ρ U₀) (restrictedSubgroup ρ U₀ B) = 2 at hdI
    rw [hu] at hdI
    have hd := hh.symm.trans hdI
    have htotal := fixedCodim_add_finrank ρ B
    omega
  have hBt : zpowers t = B := eq_of_le_of_card_ge (zpowers_le.mpr ht) (by
    rw [hcardB,Nat.card_zpowers,ht2])
  let X := ((F.Li L 2).subgroupOf D).map q
  let P := ((F.P L).subgroupOf D).map q
  have htriple := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hres : (pResidual 2 P).map P.subtype = X := by
    rw [←map_embedded_pResidual]
    exact congrArg (map q) (cubic_action_residuals (F := F) h structural Y hYp hYT).1
  have hX23 : IsPiGroup twoThreePrimes X :=
    (ChapterF.SourceAssembly.local_isTwoThreeGroup htriple.2.1).of_injective
      (inclusion (hres ▸ map_subtype_le (pResidual 2 P))) (inclusion_injective _)
  have hXp : IsPPerfect 2 X := by
    rw [←hres]
    exact (isPPerfect_pResidual (G := P) 2).of_surjective _ (P.subtype.subgroupMap_surjective _)
  have hR0 : Nat.card R₀ = 25 := by rw [card_map_of_injective (pCore 5 (D ⧸ C)).subtype_injective,hcR]
  have hcop : Nat.Coprime (Nat.card X) (Nat.card R₀) := by
    rw [hR0]
    change Nat.Coprime (Nat.card X) (5 ^ 2)
    apply Nat.Coprime.pow_right (n := 2)
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hh
    have hh := (IsPiGroup_iff _ _).mp hX23 ⟨5,Nat.prime_five⟩ hh
    change 5 = 2 ∨ 5 = 3 at hh
    omega
  exact False.elim (hm (ChapterD.quintic_plane_small_actor_centralizes ρ
    (NormalElementaryQuotient.representation_injective _ _ _ _) q
    (QuotientGroup.mk'_surjective C)
    ((cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin
      5 Nat.prime_five (by decide)) R₀ B X hR0 hB hkzero t ht2 hBt hdB hXp hcop))

/-- The original full point-normality interface. -/
theorem cubic_generated_action_twoThree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    IsPiGroup twoThreePrimes (D ⧸ C) := by
  apply cubic_generated_action_twoThree_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Both clauses of original 14.5.11, with the literal surjection from the prime-to-three core quotient. -/
theorem cubic_generated_action_core_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    IsPiGroup twoThreePrimes (D ⧸ C) ∧ pPrimeCore 3 D ≤ C ∧
      ∃ f : (D ⧸ pPrimeCore 3 D) →* (D ⧸ C), Function.Surjective f ∧
        f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = QuotientGroup.mk' C := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let U := W.subgroupOf D
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (U : Set D)
  have h23 := cubic_generated_action_twoThree_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he
  have ht := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hk : pPrimeCore 3 D ≤ C := by
    have hh := pPrimeCore_three_le_kernel_of_twoThree (QuotientGroup.mk' C)
      (QuotientGroup.mk'_surjective C) h23 ht.2.2
    rwa [QuotientGroup.ker_mk'] at hh
  let f := QuotientGroup.map (pPrimeCore 3 D) C (MonoidHom.id D) hk
  refine ⟨h23,hk,f,?_,?_⟩
  · exact QuotientGroup.map_surjective_of_surjective (pPrimeCore 3 D) C
      (MonoidHom.id D) (QuotientGroup.mk'_surjective C) hk
  · ext x
    rfl

/-- The original full point-normality interface. -/
theorem cubic_generated_action_core_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
      (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
    let C := centralizer (W.subgroupOf D : Set D)
    IsPiGroup twoThreePrimes (D ⧸ C) ∧ pPrimeCore 3 D ≤ C ∧
      ∃ f : (D ⧸ pPrimeCore 3 D) →* (D ⧸ C), Function.Surjective f ∧
        f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = QuotientGroup.mk' C := by
  apply cubic_generated_action_core_kernel_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- Original order-four interval application of 14.5.11, preserving Y,
its actual star kernel and its S₃ quotient. -/
theorem extraspecial_four_interval_cubic_twoThree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      ∃ he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)),
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      Group.IsSolvable D ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1 ∧
      ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 ∧
      ¬ thompsonJ (T : Subgroup G) 1 ≤
        centralizer (conjugateSpanBy (F.Vi 1) D : Set G) ∧
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      letI : IsElementaryAbelian 2 (W.subgroupOf D) :=
        (cubic_generated_span_reduced h hab structural previous Y hYH he).elementary
      let C := centralizer (W.subgroupOf D : Set D)
      IsPiGroup twoThreePrimes (D ⧸ C) ∧ pPrimeCore 3 D ≤ C ∧
        ∃ f : (D ⧸ pPrimeCore 3 D) →* (D ⧸ C), Function.Surjective f ∧
          f.comp (QuotientGroup.mk' (pPrimeCore 3 D)) = QuotientGroup.mk' C := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
      hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove⟩ :=
    extraspecial_four_interval_cubic_thompson_one h hab structural previous faithful
      hex hcard hexp N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hsol,
    hJC,hJQ,hJN,hJP,hJout,hJR,hcomm,hmove,
    cubic_generated_action_core_kernel h hab structural previous faithful hn
      Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem CubicSolvableModels_primeToThree_triple_of_factor
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

private theorem CubicSolvableModels_noncommutative_residual_of_obstruction
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

private theorem CubicSolvableModels_solvable_threeCore_not_cyclic
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
  obtain ⟨hi,hplus⟩ := CubicSolvableModels_primeToThree_triple_of_factor ht (QuotientGroup.mk' C)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
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
  apply CubicSolvableModels_noncommutative_residual_of_obstruction (A := ((F.P L).subgroupOf D).map q)
    (B := ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)
  rw [←map_embedded_pResidual,←map_embedded_pResidual]
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2]
  exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout

/-- The original full point-normality interface. -/
theorem cubic_generated_action_residual_noncommutative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
  have hnc := CubicSolvableModels_solvable_threeCore_not_cyclic ht inferInstance
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The marked Heisenberg alternative contradicts the literal point-plane action. -/
theorem cubic_generated_no_heisenberg_model_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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

private theorem CubicHeisenbergExclusion_embedded_core_le_kernel_of_image_core_bot
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    · exact (le_inf (map_subtype_le _) ((CubicHeisenbergExclusion_embedded_core_le_kernel_of_image_core_bot q J hj).trans hk)).trans_eq hJC
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
