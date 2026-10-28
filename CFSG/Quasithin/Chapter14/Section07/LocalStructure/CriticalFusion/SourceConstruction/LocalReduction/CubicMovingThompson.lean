module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicMovingSolvability
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicThompsonCommutator

/-!
# Thompson centralization for a cubic actor moving the flag plane

In D = ⟨L₂,Y,T⟩ the moving-plane obstruction makes both residual
images nonnormal in D/C_D(⟨V₁^D⟩). Solvable Thompson factorization then
puts J(T) in the span centralizer. Normalizer control forces J(T) outside
O₂(LT), and the marked natural action gives [L₂,J₁(T)] = L₂.
No normalization of L₁ by Y is assumed. These conclusions supply the
literal action and Thompson actors used in CubicMovingPrimes.

Source: Aschbacher–Smith, 14.5.7(2), 14.5.9–10, printed pp.1014–1015,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open ChapterB Chapter12.Section08 CriticalFusion.Source
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

private theorem unique_maximal_of_prime_index {X : Type*} [Group X] [Finite X]
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

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem cubic_generated_sylow_centralizer_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
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
    apply cubic_plane_normalizer_obstruction_of_moving_plane h structural Y hYH hmovePlane hYp
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

theorem cubic_generated_right_action_not_normal_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hmovePlane : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y) :
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
  have ho := cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hmovePlane hYp
  exact ho (hbot ▸ bot_le)

theorem cubic_generated_thompson_centralizes_of_moving_plane
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
    exact cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hmovePlane hYp
      le_normalizer_of_normal
  have hnB : ¬ (((pResidual 2 B).map B.subtype).map q).Normal := by
    rw [hres.2]
    exact cubic_generated_right_action_not_normal_of_moving_plane h structural Y hYH hmovePlane hYp
  have hS : A ⊓ B = (S : Subgroup D) := by
    have hi : F.P L ⊓ (Y ⊔ (T : Subgroup G)) = (T : Subgroup G) :=
      le_antisymm ((inf_le_inf_left _ (sup_le hYH (F.invariant 1))).trans_eq
        (plane_parabolic_inf_point h structural))
        (le_inf (F.binary_sylow_le_P L) le_sup_right)
    exact congrArg (fun X : Subgroup G => X.subgroupOf D) hi
  have hsol := cubic_generated_solvable_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
  have h3 := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1.stronglyQuasithin
    3 Nat.prime_three (by decide)
  have hh := goldschmidt_thompson_centralizes ht (W.subgroupOf D) hr hsol h3 S hS hnA hnB
  have hm := map_mono (f := D.subtype) hh
  rw [←elementaryAbelianMaxJ_map_injective D.subtype D.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD,
    map_centralizer_subtype,map_subgroupOf_eq_of_le hWD] at hm
  exact hm.trans inf_le_right

theorem cubic_generated_thompson_normalizer_of_moving_plane
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
    elementaryAbelianMaxJ (D.pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ D.pCoreIn 2 := by
    rw [←cubic_generated_sylow_centralizer_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he]
    exact le_inf hJT (cubic_generated_thompson_centralizes_of_moving_plane
      h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he)
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

theorem cubic_generated_thompson_escape_of_moving_plane
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
  have hDJ := (cubic_generated_thompson_normalizer_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2
  exact hout (((le_sup_left.trans le_sup_right : Y ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))).trans
    hDJ).trans hJM)

theorem cubic_generated_thompson_parabolic_of_moving_plane
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
    elementaryAbelianMaxJ ((F.P L).pCoreIn 2) = elementaryAbelianMaxJ (T : Subgroup G) ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ h => h.1
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ D.pCoreIn 2 := by
    rw [←cubic_generated_sylow_centralizer_of_moving_plane h hab structural previous Y hYH hmovePlane hYp hYT he]
    exact le_inf hJT (cubic_generated_thompson_centralizes_of_moving_plane
      h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he)
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
  exact cubic_generated_thompson_escape_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he (hJQ₀.trans hQ₀R)

theorem cubic_generated_thompson_one_commutator_of_moving_plane
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
    ⁅F.Li L 2,thompsonJ (T : Subgroup G) 1⁆ = F.Li L 2 := by
  have hescape := thompson_one_plane_core_escape (F := F) h structural
    (cubic_generated_thompson_parabolic_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2
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
    (unique_maximal_of_prime_index _ (by simpa only [hi] using Nat.prime_three)) J
    (thompsonJ_le _ _) (le_normalizer_thompsonJ _ _) hJ
  have hm := congrArg (map (F.P L).subtype) hc
  rwa [map_commutator,plane_parabolic_residual h structural,hmap] at hm

theorem cubic_generated_thompson_one_action_of_moving_plane
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
    exact cubic_generated_thompson_one_commutator_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he
  have hm := congrArg (map q) hc
  rw [map_commutator] at hm
  refine ⟨hm,?_⟩
  intro hzero
  have hXzero : ((F.Li L 2).subgroupOf D).map q = ⊥ := by
    rw [hzero,commutator_bot_right] at hm
    exact hm.symm
  have ho := cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hmovePlane hYp
  apply ho
  change (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _)
  rw [hXzero,normalizer_eq_top]
  exact le_top

theorem cubic_generated_thompson_one_not_central_of_moving_plane
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
    ¬ thompsonJ (T : Subgroup G) 1 ≤
      centralizer (conjugateSpanBy (F.Vi 1) (F.P L ⊔ (Y ⊔ (T : Subgroup G))) : Set G) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  intro hz
  have hnz := (cubic_generated_thompson_one_action_of_moving_plane h hab structural previous faithful Y hYH hmovePlane hYp hYT hout he).2
  apply hnz
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  intro j hj w hw
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hz hj) w hw


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
