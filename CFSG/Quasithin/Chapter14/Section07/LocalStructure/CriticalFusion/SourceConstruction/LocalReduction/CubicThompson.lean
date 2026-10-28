module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicSolvability
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonFactors
public import Theory.GroupTheory.SymmetricThreeResidualNormality
public import Theory.GroupTheory.ElementaryThompsonRelative
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource

/-!
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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u

private theorem goldschmidt_thompson_centralizes
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  have hh := goldschmidt_thompson_centralizes ht (W.subgroupOf D) hr hsol h3 S hS hnA hnB
  have hm := map_mono (f := D.subtype) hh
  rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD,
    map_centralizer_subtype,map_subgroupOf_eq_of_le hWD] at hm
  exact hm.trans inf_le_right

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_centralizes
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  have hnJ := Chapter14.Section03.ThompsonSource.thompson_normal h F structural hJR
  have hLJ : L ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hnJ
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hJM : normalizer (J : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ L ⊔ (T : Subgroup G) ≤ M} from
          ⟨hM,hAM⟩)) hJp hJne hLJ
  have hDJ := (cubic_generated_thompson_normalizer_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he).2
  exact hout (((le_sup_left.trans le_sup_right : Y ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))).trans
    hDJ).trans hJM)

/-- The original full point-normality interface. -/
theorem cubic_generated_thompson_escape
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
