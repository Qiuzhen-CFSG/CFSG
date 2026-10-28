module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineEnlargement
public import Theory.GroupTheory.PResidual.HeisenbergActionKernel

/-!
# The residual of the minimal solvable Heisenberg local

A normal lift Y of the order-27 Heisenberg group in an escaping local J
cannot lie in M = N_G(L). Otherwise its literal action on L/O₂(L), whose
automorphism group has order 336, kills O²(Y′). This is a nontrivial normal
two-perfect subgroup of J, contradicting ambient normalizer control.

For the original minimal solvable local I, adjoining T to Y now gives I:
a proper join would lie in M by minimality. Thus Y = O²(I). The application
retains point normality, the supercritical center marking, and the full
two-core kernel of the original quotient map. At the original point
normalizer, the earlier extraspecial exclusion forces this I to be proper.
The required exclusion for proper I and the later component reductions
remain to be proved; I has not been identified with the original H.

Source: Aschbacher–Smith, 14.5.20, printed pp.1018–1019, and
14.7.9, 14.7.27–29, printed pp.1045,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal Heisenberg lift in an escaping original local itself escapes M. -/
theorem local_normal_heisenberg_lift_escapes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (Y : Subgroup J) [Y.Normal]
    (e : (Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) :
    ¬ Y.map J.subtype ≤ normalizer (L : Set G) := by
  intro hYM
  let C₀ := (pResidual 2 (_root_.commutator Y)).map (_root_.commutator Y).subtype
  let C := C₀.map Y.subtype
  let : C.Normal := inferInstance
  let : IsExtraspecial 3 (Y ⧸ pCore 2 Y) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hCne : C ≠ ⊥ := fun hz => extraspecial_derived_twoResidual_ne_bot
    ((C₀.map_eq_bot_iff_of_injective Y.subtype_injective).mp hz)
  have hp : IsPPerfect 2 C := (isPPerfect_embedded_pResidual 2 (_root_.commutator Y)).of_surjective
    (Y.subtype.subgroupMap C₀) (Y.subtype.subgroupMap_surjective C₀)
  let f : Y →* MulAut (L ⧸ pCore 2 L) := (pCoreNormalizerAction 2 L).comp
    ((inclusion hYM).comp (J.subtype.subgroupMap Y))
  have h27 : Nat.card (Y ⧸ pCore 2 Y) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  let := h.chosen.elementary
  let eL := h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  have hcAut : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    rw [Nat.card_congr (MulAut.congr (eL.trans Matrix.PSL3Two.equiv)).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  have hk : C₀ ≤ f.ker := f.derived_twoResidual_le_kernel h27 (by rw [hcAut]; decide)
  apply local_normal_twoPerfect_not_core_commutator h structural J hJ C hp hCne
  have hCM : C.map J.subtype ≤ normalizer (L : Set G) :=
    (map_mono (map_subtype_le C₀)).trans hYM
  apply commutator_le_of_normalizerQuotientAction_eq_one L _ (pCore 2 L) hCM
  rintro ⟨_,c,hc,rfl⟩
  obtain ⟨a,ha,rfl⟩ := hc
  exact hk ha

/-- Minimality identifies the selected lift with the entire residual of that same local. -/
theorem local_minimal_heisenberg_lift_eq_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hmin : ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
      D ≤ normalizer (L : Set G))
    (Y : Subgroup I) [Y.Normal] (hp : IsPPerfect 2 Y)
    (hAY : (F.Li L 1).subgroupOf I ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) :
    Y.map I.subtype ⊔ (T : Subgroup G) = I ∧ Y = pResidual 2 I := by
  let D := Y.map I.subtype ⊔ (T : Subgroup G)
  have hDI : D ≤ I := sup_le (map_subtype_le Y) (F.sylow_le_of_mem_Hz hI)
  have hAYG : F.Li L 1 ≤ Y.map I.subtype := by
    have hm := map_mono (f := I.subtype) hAY
    rwa [map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hI)] at hm
  have he : D = I := by
    by_contra hn
    have hAD : F.Li L 1 ⊔ (T : Subgroup G) ≤ D :=
      sup_le (hAYG.trans le_sup_left) le_sup_right
    have hDM := hmin D hAD (lt_of_le_of_ne hDI hn)
    exact local_normal_heisenberg_lift_escapes h structural I hI Y e (le_sup_left.trans hDM)
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hgen : Y ⊔ (S : Subgroup I) = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI),
      ←MonoidHom.range_eq_map,range_subtype]
    exact he
  exact ⟨he,(pResidual_eq_of_isPPerfect_sup Y (S : Subgroup I) hp S.isPGroup' hgen).symm⟩

/-- The original solvability assumption produces a minimal escaping local whose
full two-residual has the marked Heisenberg quotient. All kernels and the
point-center marking belong to that same local subgroup. -/
theorem local_solvable_minimal_heisenberg_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      (pResidual 2 I).map I.subtype ⊔ (T : Subgroup G) = I ∧
      ¬ (pResidual 2 I).map I.subtype ≤ normalizer (L : Set G) ∧
      Nonempty (((pResidual 2 I) ⧸ pCore 2 (pResidual 2 I)) ≃* HeisenbergPrime 3) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp (pResidual 2 I).subtype).ker =
        pCore 2 (pResidual 2 I) ∧
      (F.Li L 1).subgroupOf I ≤ pResidual 2 I ∧
      ∃ (X : Subgroup (pCore 3 (HStar I))), IsSupercriticalPSubgroup 3 X ∧
        (pResidual 2 I).map (QuotientGroup.mk' (pCore 2 I)) =
          X.map (pCore 3 (HStar I)).subtype ∧
        ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
          ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,_,hm,hk,hAY,_,he,hn,hcenter⟩ :=
    local_minimal_solvable_threeCore_heisenberg h hab structural previous faithful J hJ hs
  let := hYn
  obtain ⟨hgen,hr⟩ := local_minimal_heisenberg_lift_eq_residual
    h structural I hI hmin Y hYp hAY he.some
  have hout := local_normal_heisenberg_lift_escapes h structural I hI Y he.some
  subst Y
  exact ⟨I,hIJ,hI,hIs,hmin,hn,hgen,hout,he,hk,hAY,X,hX,hm,hcenter⟩

/-- Under the original solvability assumption, the minimal Heisenberg local
is proper in the original point normalizer. Its star residual is marked by
the actual quotient map, not identified with the original full residual. -/
theorem original_solvable_proper_heisenberg_residual
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) := by
  obtain ⟨I,hIH,hI,hIs,hmin,hn,_,_,he,_⟩ :=
    local_solvable_minimal_heisenberg_residual h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hs
  let e := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  have heStar : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) :=
    ⟨e.symm.trans he.some⟩
  refine ⟨I,lt_of_le_of_ne hIH ?_,hI,hIs,hmin,hn,heStar⟩
  intro heq
  subst I
  exact extraspecial_star_residual_impossible d h hab structural previous faithful earlier heStar

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
