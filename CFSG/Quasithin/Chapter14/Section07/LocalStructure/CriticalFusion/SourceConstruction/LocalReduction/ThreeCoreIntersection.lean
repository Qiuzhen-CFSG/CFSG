module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreMinimal
public import Theory.GroupTheory.PResidual.CentralThreeLift

/-!
# Nontrivial action of the actual normalizer intersection

Let Y be a normal lift in an original local J, with three-group quotient
and O₂(Y) < Y ∩ M, where M = N_G(L). The two-residual R of this intersection
acts nontrivially on L/O₂(L). Otherwise ambient uniqueness puts N_G(R)
in M. A nontrivial normal lift Z of the center of the star image normalizes
R, hence lies in M and therefore in R. This contradicts the established
ambient obstruction for normal two-perfect subgroups.

The final theorem applies this to the original minimal solvable witness.
It retains both actual quotient models, the entire star-map kernels, and
the proper Heisenberg-center lift. It constructs a nontrivial actor in the
literal normalizer quotient action. The subsequent point containment,
terminal solvable exclusions, component reductions and four Data inputs
remain required.

Source: Aschbacher–Smith, 14.5.20 assertion (*), printed p.1019;
14.7.9 and 14.7.27–29, printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The intersection residual in the ambient restriction acts nontrivially
on L/O₂(L), using an actual normal central lift in Y. -/
private theorem local_three_lift_intersection_moves
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y Z : Subgroup J) [Y.Normal] [Z.Normal]
    (hZY : Z ≤ Y) (hZp : IsPPerfect 2 Z) (hZn : Z ≠ ⊥)
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hc : ⁅Z.map (QuotientGroup.mk' (pCore 2 J)),
      Y.map (QuotientGroup.mk' (pCore 2 J))⁆ = ⊥)
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    ¬ ⁅L,(pResidual 2 (Y.map J.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
      (Y.map J.subtype ⊓ normalizer (L : Set G)).subtype⁆ ≤ L.pCoreIn 2 := by
  let A := Y.map J.subtype
  let C := Z.map J.subtype
  let M := normalizer (L : Set G)
  let I := A ⊓ M
  let R := (pResidual 2 I).map I.subtype
  let e := equivMapOfInjective Y J.subtype J.subtype_injective
  have hA3 : IsPGroup 3 (A ⧸ pCore 2 A) := h3.of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hRn : R ≠ ⊥ := intersection_twoResidual_ne_bot A M hA3 hi
  have hJY : J ≤ normalizer (A : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Y.le_normalizer_map J.subtype
  have hTJ : (T : Subgroup G) ≤ J := F.sylow_le_of_mem_Hz hJ
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (((le_inf (hTJ.trans hJY) ((h.sylow_normalizes structural).trans M.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image I (pResidual 2 I)))
  intro hcomm
  have hbound : normalizer (R : Set G) ≤ M :=
    local_twoPerfect_core_commutator_normalizer h structural J hJ R
      ((map_subtype_le _).trans (inf_le_left.trans (map_subtype_le Y)))
      (isPPerfect_embedded_pResidual 2 I) hRn hTR hcomm
  have hCA : ⁅C,A⁆ ≤ A.pCoreIn 2 := by
    have hh := map_mono (f := J.subtype) (commutator_le_core_of_quotient_centralizes Y Z hc)
    rwa [map_commutator,map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective] at hh
  have hCM : C ≤ M :=
    (normalizes_intersection_twoResidual A M C (hi.le.trans inf_le_right) hCA).trans hbound
  have hCI : C ≤ I := le_inf (map_mono hZY) hCM
  have hCp : IsPPerfect 2 C := hZp.of_surjective (J.subtype.subgroupMap Z)
    (J.subtype.subgroupMap_surjective Z)
  have hCR : C ≤ R := by
    have hm := embedded_pResidual_mono 2 hCI
    rwa [(pResidual_eq_top_iff 2 C).mpr hCp,←MonoidHom.range_eq_map,range_subtype] at hm
  exact local_normal_twoPerfect_not_core_commutator h structural J hJ Z hZp hZn
    ((commutator_mono le_rfl hCR).trans hcomm)

/-- Source 14.5.20's strict-action assertion for the actual intersection
in 14.7.9. No central lift or local recognition is assumed. -/
theorem local_three_intersection_residual_moves
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    ¬ ⁅L,(pResidual 2 (Y.map J.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
      (Y.map J.subtype ⊓ normalizer (L : Set G)).subtype⁆ ≤ L.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hn : Y.map q ≠ ⊥ := by
    intro he
    have hYQ : Y ≤ pCore 2 J := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff Y).mp he
    have hYY : Y ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
      (pCore_isPGroup.to_le hYQ) le_rfl Y.le_normalizer
    have hm := map_mono (f := J.subtype) hYY
    rw [map_pCoreIn_of_injective 2 Y J.subtype J.subtype_injective] at hm
    exact hi.not_ge (inf_le_left.trans hm)
  obtain ⟨Z,hZY,hZn,hZp,hZne,_,_,_,hc⟩ := exists_normal_central_three_lift q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    Y (h3.of_equiv (coreQuotientEquivImage 2 Y)) hn
  let := hZn
  exact local_three_lift_intersection_moves h structural J hJ Y Z hZY hZp hZne h3 hc hi

/-- The intersection residual has a nontrivial literal quotient action;
this is (*) in 14.5.20 on the original ambient normalizer. -/
theorem local_three_intersection_quotient_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (h3 : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    ∃ x : (pResidual 2 (Y.map J.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
      (Y.map J.subtype ⊓ normalizer (L : Set G)).subtype,
      normalizerQuotientAction L (pCore 2 L)
        (inclusion ((map_subtype_le _).trans inf_le_right) x) ≠ 1 := by
  by_contra hn
  push Not at hn
  exact local_three_intersection_residual_moves h structural J hJ Y h3 hi
    (commutator_le_of_normalizerQuotientAction_eq_one L _ (pCore 2 L)
      ((map_subtype_le _).trans inf_le_right) hn)

open Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- Apply the ambient strict-action restriction to the selected lifts on the
original minimal solvable witness. Both model alternatives, all normalities,
and the exact star kernels are retained. -/
theorem local_minimal_solvable_threeCore_intersection_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (¬ ⁅L,Y.map I.subtype⁆ ≤ L.pCoreIn 2) ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      (∃ x : (pResidual 2 (Y.map I.subtype ⊓ normalizer (L : Set G) : Subgroup G)).map
          (Y.map I.subtype ⊓ normalizer (L : Set G)).subtype,
        normalizerQuotientAction L (pCore 2 L)
          (inclusion ((map_subtype_le _).trans inf_le_right) x) ≠ 1) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          (F.Li L 1).subgroupOf I ≤ Y ∧
          ∃ Z : Subgroup I, Z < Y ∧ Z.Normal ∧ IsPPerfect 2 Z ∧
            Z.map (QuotientGroup.mk' (pCore 2 I)) =
              ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype ∧
            ((QuotientGroup.mk' (pCore 2 I)).comp Z.subtype).ker = pCore 2 Z ∧
            Nat.card (Z ⧸ pCore 2 Z) = 3 ∧ Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
            pCore 2 Z ≠ ⊥ ∧ ¬ ⁅L,Z.map I.subtype⁆ ≤ L.pCoreIn 2)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hmove,hi,he⟩ :=
    local_minimal_solvable_threeCore_reduction h hab structural previous faithful J hJ hs
  let := hYn
  let eX : (Y ⧸ pCore 2 Y) ≃* X := (coreQuotientEquivImage 2 Y).trans
    ((MulEquiv.subgroupCongr hm).trans
      (equivMapOfInjective X (pCore 3 (HStar I)).subtype
        (pCore 3 (HStar I)).subtype_injective).symm)
  have h3 : IsPGroup 3 (Y ⧸ pCore 2 Y) :=
    ((pCore_isPGroup (p := 3) (G := HStar I)).to_subgroup X).of_equiv eX.symm
  exact ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hmove,hi,
    local_three_intersection_quotient_action h structural I hI Y h3 hi,he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
