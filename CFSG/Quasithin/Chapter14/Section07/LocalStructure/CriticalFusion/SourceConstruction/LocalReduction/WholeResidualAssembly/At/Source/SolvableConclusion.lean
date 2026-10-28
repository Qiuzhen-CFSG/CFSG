module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ThreeCoreLifts
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineEnlargement
public import Theory.GroupTheory.PResidual.HeisenbergActionKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergPoint
public import Theory.GroupTheory.PResidual.ExtraspecialCubicCharacteristic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergFullStar
public import Theory.GroupTheory.HeisenbergCentralizer
public import Theory.GroupTheory.PResidual.NormalThreeLift
public import Theory.GroupTheory.DetectedNormalCubic
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.SylowThreeCubic
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergThreeCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergComparison
public import Theory.GroupTheory.HeisenbergIrreducibleCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableHeisenbergExclusion
public import Theory.Representation.ExtraspecialBinarySixCubicRank
public import Theory.SpecificGroups.SL2.ThreeResidualCore
public import Theory.GroupTheory.PResidual.AutomorphismCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeComponent
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.LargePrimeExclusion
public import Theory.GroupTheory.CComponent.PrimeComplement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceModels
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscape
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeRecognition
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableLocalExclusion
public import Theory.SpecificGroups.GL2.ThreeSolvable
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentQuotients
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFitting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNormalized
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CoreContainment
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreConclusion
public import Theory.GroupTheory.Fitting.SmallOddCore

/-!
# Guarded solvable conclusion

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

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
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal Heisenberg lift in an escaping original local itself escapes M. -/
theorem local_normal_heisenberg_lift_escapes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
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
      (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) hs
  let e := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  have heStar : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) :=
    ⟨e.symm.trans he.some⟩
  refine ⟨I,lt_of_le_of_ne hIH ?_,hI,hIs,hmin,hn,heStar⟩
  intro heq
  subst I
  exact extraspecial_star_residual_impossible d h hab structural previous faithful earlier heStar

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Normality of a solvable local Heisenberg residual in its overgroups

Let I be an actual solvable member of the original H_z, with normal point
residual L₁ and Heisenberg star residual. A proper invariant Frattini line
would supply two T-normalized cubic lifts generating O²(I). The established
solvable cubic containment places both in N_G(L), contradicting I's escape.
Thus the actual T-action is irreducible, and its literal quotient transport
puts the embedded O²(I) in Ξ(G,T).

The complete intrinsic embedding theorem makes this residual normal in every
two-local overgroup of I: each nonnormal alternative, including Held, has an
odd complement of order nine rather than 27. Hence its normalizer is the
unique maximal two-local containing I. The application supplies these facts
for the original minimal solvable witness, in particular normality in the
full original point normalizer. It does not identify I with that normalizer
or assert the terminal solvable exclusion.

Source: Aschbacher–Smith, 14.7.15(2–4) and its application in 14.7.27,
printed pp.1047,1054–1055, refs/quasithin.pdf. The actual earlier structural,
faithful classification and Baumann inputs retain their existing producers.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual Sylow action on the local residual Frattini quotient is irreducible. -/
theorem local_solvable_heisenberg_frattini_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3))
    (J : Subgroup ((pResidual 2 (HStar I)) ⧸ frattini (pResidual 2 (HStar I))))
    (hJ : ∀ a : ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)),
      ∀ x ∈ J, quotientAut (frattini (pResidual 2 (HStar I)))
        (MulAut.conjNormal (a : HStar I)) x ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  by_contra! hne
  obtain ⟨e⟩ := he
  let P := pResidual 2 (HStar I)
  let q := QuotientGroup.mk' (pCore 2 I)
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hP : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have heP : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨A,B,hAB,hA,hB⟩ := IsExtraspecial.exists_cubic_lifts_of_stable_frattini_line
    q (QuotientGroup.mk'_surjective _) hk hP heP
    (S : Subgroup I) S.isPGroup' J hne.1 hne.2 hJ
  have hIL : I ≤ normalizer (F.Li L 1 : Set G) := by
    rw [←normal_subgroupOf_iff_le_normalizer (F.Li_one_le_of_mem_Hz hI)]
    exact hn
  have contained (A : Subgroup I) (hp : IsPPerfect 2 A)
      (hAT : (S : Subgroup I) ≤ normalizer (A : Set I))
      (hc : Nat.card (A ⧸ pCore 2 A) = 3) :
      A.map I.subtype ≤ normalizer (L : Set G) := by
    let eA := equivMapOfInjective A I.subtype I.subtype_injective
    apply local_solvable_cubic_containment h hab structural previous faithful I hI hs
      (A.map I.subtype) (map_subtype_le A) ((map_subtype_le A).trans hIL)
      (hp.of_surjective eA.toMonoidHom eA.surjective)
    · have hh := (map_mono hAT).trans (le_normalizer_map I.subtype)
      simpa only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)] using hh
    · exact (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).symm.trans hc
  have hAM := contained A hA.1 hA.2.1 hA.2.2.2.2.2
  have hBM := contained B hB.1 hB.2.1 hB.2.2.2.2.2
  apply hI.2.2
  have hgen := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)] at hgen
  rw [←hgen,←hAB,Subgroup.map_sup]
  exact sup_le (sup_le hAM hBM) (h.sylow_normalizes_at structural)

private def SolvableHeisenbergNormalizer_localResidualStarEquiv (I : Subgroup G) :
    ((pResidual 2 I) ⧸ pCore 2 (pResidual 2 I)) ≃* pResidual 2 (HStar I) :=
  (QuotientGroup.quotientMulEquivOfEq
    (pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 I).Normal).isSubnormal)).trans
    (pResidualQuotientEquiv 2 (pCore 2 I))

private theorem SolvableHeisenbergNormalizer_localResidualStarEquiv_mk (I : Subgroup G) (x : pResidual 2 I) :
    (SolvableHeisenbergNormalizer_localResidualStarEquiv I (QuotientGroup.mk' (pCore 2 (pResidual 2 I)) x) : HStar I) =
      QuotientGroup.mk' (pCore 2 I) (x : I) := by
  dsimp only [SolvableHeisenbergNormalizer_localResidualStarEquiv,MulEquiv.trans_apply]
  change (pResidualQuotientEquiv 2 (pCore 2 I)
    (QuotientGroup.mk' ((pCore 2 I).subgroupOf (pResidual 2 I)) x) : HStar I) = _
  rw [pResidualQuotientEquiv_mk]

private def SolvableHeisenbergNormalizer_localResidualFrattiniEquiv (I : Subgroup G) :
    XiFrattiniQuotient (pResidual 2 I) ≃*
      ((pResidual 2 (HStar I)) ⧸ frattini (pResidual 2 (HStar I))) :=
  QuotientGroup.congr _ _ (SolvableHeisenbergNormalizer_localResidualStarEquiv I)
    (frattini_map_mulEquiv _)

private theorem SolvableHeisenbergNormalizer_localResidualFrattiniEquiv_action (I : Subgroup G)
    (S : Subgroup I) (hn : S ≤ normalizer (pResidual 2 I : Set I))
    (s : S) (x : XiFrattiniQuotient (pResidual 2 I)) :
    SolvableHeisenbergNormalizer_localResidualFrattiniEquiv I (xiFrattiniAction S (pResidual 2 I) hn s x) =
      quotientAut (frattini (pResidual 2 (HStar I)))
        (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 I) (s : I)))
        (SolvableHeisenbergNormalizer_localResidualFrattiniEquiv I x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H k =>
      change SolvableHeisenbergNormalizer_localResidualFrattiniEquiv I (xiFrattiniAction S (pResidual 2 I) hn s
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ k))) =
          quotientAut (frattini (pResidual 2 (HStar I)))
            (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 I) (s : I)))
            (SolvableHeisenbergNormalizer_localResidualFrattiniEquiv I (QuotientGroup.mk' _ (QuotientGroup.mk' _ k)))
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,
        SolvableHeisenbergNormalizer_localResidualFrattiniEquiv,QuotientGroup.congr_mk']
      apply congrArg (QuotientGroup.mk' _)
      apply Subtype.ext
      rw [SolvableHeisenbergNormalizer_localResidualStarEquiv_mk]
      change QuotientGroup.mk' (pCore 2 I) _ =
        QuotientGroup.mk' (pCore 2 I) (s : I) * (SolvableHeisenbergNormalizer_localResidualStarEquiv I _) *
          (QuotientGroup.mk' (pCore 2 I) (s : I))⁻¹
      rw [SolvableHeisenbergNormalizer_localResidualStarEquiv_mk,←map_inv,←map_mul,←map_mul]
      rfl

/-- The minimal local's residual belongs to the ambient solvable uniqueness family. -/
theorem local_solvable_heisenberg_residual_mem_Xi
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    (pResidual 2 I).map I.subtype ∈ Xi G (T : Subgroup G) := by
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hmapS : (S : Subgroup I).map I.subtype = (T : Subgroup G) := by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
  rw [←hmapS,mem_Xi_map_iff I.subtype I.subtype_injective]
  have hgen := pResidual_sup_sylow_eq_top S
  have hmap : (pResidual 2 I ⊔ (S : Subgroup I)).map I.subtype = I := by
    rw [hgen,←MonoidHom.range_eq_map,range_subtype]
  have hj : pResidual 2 I ⊔ (S : Subgroup I) ∈ Chapter1.H I := by
    change (pResidual 2 I ⊔ (S : Subgroup I)).pCoreIn 2 ≠ ⊥
    intro hz
    apply hI.1.1
    rw [←hmap,←map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,hz,Subgroup.map_bot]
  let e := (SolvableHeisenbergNormalizer_localResidualStarEquiv I).trans he.some
  have hRn : (S : Subgroup I) ≤ normalizer (pResidual 2 I : Set I) := le_normalizer_of_normal
  refine ⟨isPPerfect_pResidual 2,hRn,hj,⟨3,by decide,by decide,Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans
        (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩⟩,?_⟩
  intro A hA
  let eF := SolvableHeisenbergNormalizer_localResidualFrattiniEquiv I
  have hinv : ∀ a : ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)),
      ∀ x ∈ A.map eF.toMonoidHom,
      quotientAut (frattini (pResidual 2 (HStar I)))
        (MulAut.conjNormal (a : HStar I)) x ∈ A.map eF.toMonoidHom := by
    intro a x hx
    obtain ⟨s,hs,heq⟩ := a.property
    obtain ⟨y,hy,rfl⟩ := hx
    rw [←heq]
    change quotientAut (frattini (pResidual 2 (HStar I)))
      (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 I) s))
      (SolvableHeisenbergNormalizer_localResidualFrattiniEquiv I y) ∈ A.map eF.toMonoidHom
    rw [←SolvableHeisenbergNormalizer_localResidualFrattiniEquiv_action I (S : Subgroup I) hRn ⟨s,hs⟩]
    exact mem_map_of_mem eF.toMonoidHom (hA ⟨s,hs⟩ y hy)
  rcases local_solvable_heisenberg_frattini_irreducible h hab structural previous faithful
      I hI hs hn he (A.map eF.toMonoidHom) hinv with hb | ht
  · exact Or.inl ((map_eq_bot_iff_of_injective A eF.injective).mp hb)
  · right
    have hh := congrArg (Subgroup.comap eF.toMonoidHom) ht
    simpa only [comap_map_eq_self_of_injective (f := eF.toMonoidHom) eF.injective,comap_top] using hh

/-- The local residual is normal in every two-local overgroup, including the
full original point normalizer. The nonnormal catalogue has the wrong odd order. -/
theorem local_solvable_heisenberg_normal_in_twoLocal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3))
    (M : Subgroup G) (hM : IsTwoLocal M) (hIM : I ≤ M) :
    (((pResidual 2 I).map I.subtype).subgroupOf M).Normal := by
  let R := (pResidual 2 I).map I.subtype
  have hX := local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hs hn he
  have hTM := (F.sylow_le_of_mem_Hz hI).trans hIM
  have hT : IsSylowIn 2 (T : Subgroup G) M := by
    refine ⟨T.subtype hTM,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let e := (QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans
    ((SolvableHeisenbergNormalizer_localResidualStarEquiv I).trans he.some)
  have hq : XiOddQuotient 3 (XiQuotient R) := Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩
  let b := XiEmbedding.localInput_of_mem_Xi hX hT
    (sup_le ((map_subtype_le _).trans hIM) hTM) (by decide : Odd 3) hq
    (default : Sylow 3 R)
  rcases b.adequate_knownSimple (h.source.simpleQTKE.twoLocal_sqtk hM) hT with hn | ⟨J,_,_,_,ha⟩
  · exact hn
  · have hplane : Nonempty (((default : Sylow 3 R) : Subgroup R).map R.subtype ≃*
        XiEmbedding.Plane 3) := by
      rcases ha with ha | ha
      · exact ha.1
      · exact ha.2.1
    obtain ⟨ep⟩ := hplane
    have h27 : Nat.card (((default : Sylow 3 R) : Subgroup R).map R.subtype) = 27 :=
      (Nat.card_congr b.complementQuotientEquiv.toEquiv).trans
        ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    have h9 := (Nat.card_congr ep.toEquiv).trans (XiEmbedding.plane_card 3)
    omega

/-- The actual local residual has a unique maximal two-local normalizer. -/
theorem local_solvable_heisenberg_normalizer_unique
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    IsMaximalTwoLocal (normalizer ((pResidual 2 I).map I.subtype : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ I ≤ M} =
        {normalizer ((pResidual 2 I).map I.subtype : Set G)} := by
  let R := (pResidual 2 I).map I.subtype
  have hX := local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hs hn he
  have hcore : R.pCoreIn 2 ≠ ⊥ := hX.pCoreIn_ne_bot
    (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T (h.source.simpleQTKE.evenCharacteristic T))
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  have hgen : R ⊔ (T : Subgroup G) = I := by
    have hh := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
    simpa only [Subgroup.map_sup,S,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI),
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hh := Chapter1.Section03.normalizer_unique_of_normal_in_maximalTwoLocals
    R (T : Subgroup G) hX.invariant
    (fun he => hcore (by change (pCore 2 R).map R.subtype = ⊥; rw [he,Subgroup.map_bot]))
    (fun M hM hRM => local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
      I hI hs hn he M hM.1 (hgen ▸ hRM))
  simpa only [hgen] using hh

/-- Apply the genuine local irreducibility and complete embedding theorem to
an original minimal solvable witness. Its residual is normal in the full H,
while the original quotient and proper-local distinction are retained. -/
theorem original_solvable_proper_heisenberg_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) ∧
      (pResidual 2 I).map I.subtype ∈ Xi G (T : Subgroup G) ∧
      (((pResidual 2 I).map I.subtype).subgroupOf F.H).Normal ∧
      IsMaximalTwoLocal (normalizer ((pResidual 2 I).map I.subtype : Set G)) ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ I ≤ M} =
        {normalizer ((pResidual 2 I).map I.subtype : Set G)} := by
  obtain ⟨I,hIH,hI,hIs,hmin,hn,he⟩ := original_solvable_proper_heisenberg_residual
    d h hab structural previous faithful earlier hs
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact ⟨I,hIH,hI,hIs,hmin,hn,he,
    local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hIs hn he,
    local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful I hI hIs hn he
      F.H hH hIH.le,
    local_solvable_heisenberg_normalizer_unique h hab structural previous faithful I hI hIs hn he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Point normality from the proper local Heisenberg residual

The actual L₁ is a normal two-perfect subgroup of the selected local
residual R, with cubic intrinsic two-core quotient. Its image in R/O₂(R)
is therefore the center, and L₁ is characteristic in R. The complete
intrinsic embedding theorem already makes R normal in every two-local
overgroup of the selected local. Hence these overgroups normalize L₁.

The original solvability hypothesis produces such a local witness and
therefore proves relative normality of L₁ in the full point normalizer.
The literal quotient maps and the potentially proper local R are retained;
this does not identify R with O²(H) or complete the solvable exclusion.

Source: Aschbacher–Smith, 14.7.15(1,3), and 14.7.27–29,
printed pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original point residual is characteristic in the proper local residual,
so its relative normality extends to every actual two-local overgroup. -/
theorem local_solvable_heisenberg_point_normal_in_twoLocal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3))
    (M : Subgroup G) (hM : IsTwoLocal M) (hIM : I ≤ M) :
    ((F.Li L 1).subgroupOf M).Normal := by
  let R := (pResidual 2 I).map I.subtype
  let A := (F.Li L 1).subgroupOf R
  have hp : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
  have hAR : F.Li L 1 ≤ R := by
    have hh := embedded_pResidual_mono 2 (F.Li_one_le_of_mem_Hz hI)
    rwa [(pResidual_eq_top_iff 2 (F.Li L 1)).mpr hp,
      ←MonoidHom.range_eq_map,range_subtype] at hh
  let := hn
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    ((map_subtype_le _).trans (F.normalizes_Li_one_of_relative_normal hI))
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let eStar := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  let e := (QuotientGroup.congr _ _ eR.symm (pCore_map_iso 2 eR.symm)).trans
    (eStar.trans he.some)
  let : IsExtraspecial 3 (R ⧸ pCore 2 R) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  let eA : A ≃* F.Li L 1 := subgroupOfEquivOfLe hAR
  let : A.Characteristic := characteristic_of_normal_twoPerfect_cubic A
    (hp.of_surjective eA.symm.toMonoidHom eA.symm.surjective)
    ((Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).trans
      (pointResidual_core_quotient_card h structural))
  have hRn := local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
    I hI hs hn he M hM hIM
  have hMR : M ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans hIM)).mp hRn
  apply (normal_subgroupOf_iff_le_normalizer ((F.Li_one_le_of_mem_Hz hI).trans hIM)).mpr
  have hnorm := hMR.trans (normalizer_le_normalizer_characteristic_image R A)
  simpa only [A,map_subgroupOf_eq_of_le hAR] using hnorm

/-- Under the original solvability assumption, L₁ is normal in the full point
normalizer. The proof uses the actual proper local lift and discharges its
irreducibility and intrinsic embedding premises. -/
theorem original_solvable_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  obtain ⟨I,hIH,hI,hIs,_,hn,_,_,he,_⟩ :=
    local_solvable_minimal_heisenberg_residual h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) hs
  let e := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  have heStar : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3) :=
    ⟨e.symm.trans he.some⟩
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hc := F.card 1 (by decide)
    rw [hz,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn heStar F.H hH hIH

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The proper local Heisenberg residual in the full point quotient

The selected local residual embeds normally in the original full point
quotient, with the same marked central cubic L₁*. The ambient three-rank
bound and vanishing three-prime core make its centralizer a cyclic
three-group. Lifting that group and using its actual action on L/O₂(L)
then makes its order exactly three; the centralizer is precisely L₁*.

The applications retain the original group, flag, quotient kernels and
potentially proper local witness. They do not identify the local residual
with O²(H). Source: Aschbacher–Smith 14.7.15(3) and 14.7.27–29,
printed pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem SolvableHeisenbergFullStar_fullStar_image
    (I : Subgroup G) (hIH : I ≤ F.H)
    (hn : (((pResidual 2 I).map I.subtype).subgroupOf F.H).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    (star F ((pResidual 2 I).map I.subtype)).Normal ∧
      Nonempty (star F ((pResidual 2 I).map I.subtype) ≃* HeisenbergPrime 3) := by
  let R := (pResidual 2 I).map I.subtype
  let A := R.subgroupOf F.H
  let := hn
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let eA : A ≃* pResidual 2 I :=
    (subgroupOfEquivOfLe ((map_subtype_le _).trans hIH)).trans eR.symm
  let eLocal := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  let e := (coreQuotientEquivImage 2 A).symm.trans
    ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans (eLocal.trans he.some))
  exact ⟨hn.map (starMap F) (QuotientGroup.mk'_surjective _),⟨e⟩⟩

private theorem SolvableHeisenbergFullStar_fullStar_three_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    primeRank 3 (HStar F.H) ≤ 2 := by
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 F.H) pCore_isPGroup).trans
    ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))

theorem local_solvable_heisenberg_full_star
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      IsPGroup 3 (centralizer (R : Set (HStar F.H))) ∧
      IsCyclic (centralizer (R : Set (HStar F.H))) := by
  let R₀ := (pResidual 2 I).map I.subtype
  let R := star F R₀
  have hIH : I ≤ F.H := hI.2.1
  let := hs
  have hIs : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective (inclusion_injective hIH)
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  obtain ⟨hRn,⟨e⟩⟩ := SolvableHeisenbergFullStar_fullStar_image I hIH
    (local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
      I hI hIs hn he F.H hH hIH) he
  let : R.Normal := hRn
  have hR3 : IsPGroup 3 R :=
    (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
  have hRres : R ≤ pResidual 2 (HStar F.H) := by
    have hh : R₀ ≤ K F := embedded_pResidual_mono 2 hIH
    have hh' : R₀.subgroupOf F.H ≤ pResidual 2 F.H := by
      rw [←residual_subgroupOf F]
      exact subgroupOf_mono F.H hh
    exact (map_mono hh').trans (map_pResidual_le 2 (starMap F))
  have hnH := local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hIH
  let Z := star F (F.Li L 1)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hnH
  let : Z.Normal := hnH.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZR₀ : F.Li L 1 ≤ R₀ := by
    have hh := embedded_pResidual_mono 2 (F.Li_one_le_of_mem_Hz hI)
    rw [(pResidual_eq_top_iff 2 (F.Li L 1)).mpr (isPPerfect_embedded_pResidual 2 _),
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hZR : Z ≤ R := map_mono (subgroupOf_mono F.H hZR₀)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hnH
  have hZRc : Nat.card (Z.subgroupOf R) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv).trans hZcard
  have hcenter : Z = (center R).map R.subtype := by
    have hh : Z.subgroupOf R = center R := eq_of_le_of_card_ge
      (hR3.normal_le_center_of_card_dvd_prime _ (by rw [hZRc]))
      (by rw [hZRc,Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center])
    simpa only [map_subgroupOf_eq_of_le hZR] using congrArg (map R.subtype) hh
  have hcore : pPrimeCore 3 (HStar F.H) = ⊥ :=
    pPrimeCore_eq_bot_of_fitting_isPGroup inferInstance 3
      (local_fitting_isThreeGroup h hab structural previous faithful F.H
        (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)))
  exact ⟨hRn,⟨e⟩,le_sSup ⟨hRn,hR3⟩,hRres,hcenter,
    heisenberg_centralizer_isCyclic_threeGroup R e (SolvableHeisenbergFullStar_fullStar_three_rank h) hcore⟩

/-- Apply the full-star centralizer argument to the actual proper local
provided by the original solvable hypothesis. -/
theorem original_solvable_full_star_heisenberg
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
        R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        IsPGroup 3 (centralizer (R : Set (HStar F.H))) ∧
        IsCyclic (centralizer (R : Set (HStar F.H))) := by
  obtain ⟨I,hIH,hI,_,_,hn,he,_⟩ := original_solvable_proper_heisenberg_normal
    d h hab structural previous faithful earlier hs
  exact ⟨I,hIH,hI,local_solvable_heisenberg_full_star
    h hab structural previous faithful hs I hI hn he⟩

private theorem SolvableHeisenbergFullStar_full_quotient_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

private theorem SolvableHeisenbergFullStar_full_quotient_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    center (L ⧸ pCore 2 L) = ⊥ := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  apply bot_unique
  intro x hx
  have hz : e x ∈ center Matrix.PSL3Two.SL := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  rw [Matrix.PSL3Two.center_eq_bot] at hz
  exact e.injective (hz.trans e.map_one.symm)

private theorem SolvableHeisenbergFullStar_cyclic_three_lift_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (E : Subgroup G) (hAE : F.Li L 1 ≤ E)
    (hEA : E ≤ normalizer (F.Li L 1 : Set G))
    (hEM : E ≤ normalizer (L : Set G))
    (hcyc : IsCyclic (E ⧸ pCore 2 E))
    (h3 : IsPGroup 3 (E ⧸ pCore 2 E)) :
    Nat.card (E ⧸ pCore 2 E) = 3 := by
  let S : Sylow 3 E := default
  let q := QuotientGroup.mk' (pCore 2 E)
  have hk : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := E)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : IsCyclic (E ⧸ pCore 2 E) := hcyc
  let : IsCyclic S := isCyclic_of_injective (q.comp (S : Subgroup E).subtype)
    (injective_comp_subtype_of_coprime_ker q hk _ S.isPGroup')
  let B := (S : Subgroup E).map E.subtype
  let : IsCyclic B := isCyclic_of_surjective (E.subtype.subgroupMap (S : Subgroup E))
    (E.subtype.subgroupMap_surjective _)
  have hB : IsPGroup 3 B := S.isPGroup'.map E.subtype
  obtain ⟨A₀,hA₀⟩ := S.exists_map_subtype_eq_inf_of_normalizes hAE hEA
  have hAc : Nat.card (B ⊓ F.Li L 1 : Subgroup G) = 3 := by
    rw [←hA₀,card_map_of_injective (F.Li L 1).subtype_injective]
    exact card_sylow_three_of_two_group_index_three (pCore 2 (F.Li L 1)) pCore_isPGroup
      (pointResidual_core_quotient_card h structural) A₀
  let A := (B ⊓ F.Li L 1).subgroupOf B
  have hAc' : Nat.card A = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv).trans hAc
  have hBM : B ≤ normalizer (L : Set G) := (map_subtype_le _).trans hEM
  let f := (pCoreNormalizerAction 2 L).comp (inclusion hBM)
  have hi : Function.Injective (f.comp A.subtype) := by
    have hd : Disjoint B (L.pCoreIn 2) :=
      hB.disjoint_of_coprime (isPGroup_pCoreIn 2 L) (by decide)
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hm : ((x : B) : G) ∈ pCoreActionKernelIn 2 L (normalizer (L : Set G)) ⊓ L := by
      exact ⟨⟨hBM x.val.property,inclusion hBM x.val,hx,rfl⟩,
        (inf_le_right.trans ((F.Li_le L 1).trans inf_le_left)) x.property⟩
    rw [pCoreActionKernelIn_inf_eq_core L (normalizer (L : Set G)) L.le_normalizer
      (SolvableHeisenbergFullStar_full_quotient_center h)] at hm
    exact Subtype.ext (Subtype.ext (hd.le_bot ⟨x.val.property,hm⟩))
  have hr : Nat.card f.range ≤ 3 := by
    obtain ⟨P,hP⟩ := (hB.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
    have hc : Nat.card P = 3 := by
      rw [P.card_eq_multiplicity,SolvableHeisenbergFullStar_full_quotient_aut_card h]
      decide +kernel
    exact (Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)).trans_eq hc
  have heq : (⊤ : Subgroup B) = A :=
    cyclic_eq_detected_cubic hB A hAc' f hi hr ⊤ le_top
  have hcB : Nat.card B = 3 := by
    rw [←card_top (G := B),heq]
    exact hAc'
  have hStop : (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 E)) :
      Subgroup (E ⧸ pCore 2 E)) = ⊤ := by
    apply top_unique
    exact (h3.to_subgroup ⊤).le_sylow_of_normal _
  let e := Sylow.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective _) hk S
    (S.mapSurjective (QuotientGroup.mk'_surjective _))
  calc
    Nat.card (E ⧸ pCore 2 E) = Nat.card S := by
      rw [Nat.card_congr e.toEquiv,hStop,card_top]
    _ = Nat.card B := (card_map_of_injective E.subtype_injective).symm
    _ = 3 := hcB

/-- Every normal cyclic three-subgroup containing the marked point cubic
is precisely that cubic, using the original quotient action on L/O₂(L). -/
theorem full_star_normal_cyclic_three_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (X : Subgroup (HStar F.H)) [X.Normal]
    (hX : IsPGroup 3 X) (hcyc : IsCyclic X)
    (hZX : star F (F.Li L 1) ≤ X) :
    X = star F (F.Li L 1) := by
  let q := starMap F
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨W,hWn,hWp,_,hWm,_,⟨eW⟩⟩ :=
    exists_normal_three_residual_lift q hq hk X hX
  let : W.Normal := hWn
  let A := (F.Li L 1).subgroupOf F.H
  have hAH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hAp : IsPPerfect 2 A :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hAW : A ≤ W := isPPerfect_le_of_map_le_of_kernel_normalizes q A W hAp hk
    le_normalizer_of_normal (by rw [hWm]; exact hZX)
  have hEpoint : F.Li L 1 ≤ W.map F.H.subtype := by
    have hh := map_mono (f := F.H.subtype) hAW
    rwa [map_subgroupOf_eq_of_le hAH] at hh
  let := hn
  have hEA : W.map F.H.subtype ≤ normalizer (F.Li L 1 : Set G) := by
    rintro _ ⟨w,hw,rfl⟩
    exact (normal_subgroupOf_iff_le_normalizer hAH).mp hn w.property
  have hTW : (T : Subgroup G) ≤ normalizer (W.map F.H.subtype : Set G) := by
    have hh := W.le_normalizer_map F.H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact (F.invariant 1).trans hh
  let := hcyc
  have hWcyc : IsCyclic (W ⧸ pCore 2 W) := eW.isCyclic.mpr hcyc
  have hW3 : IsPGroup 3 (W ⧸ pCore 2 W) := hX.of_equiv eW.symm
  have hWM : W.map F.H.subtype ≤ normalizer (L : Set G) :=
    local_cyclic_three_lift_containment h hab structural F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) W hWp hTW hAW hWcyc hW3
  let eE := (equivMapOfInjective W F.H.subtype F.H.subtype_injective).symm
  let eQ := (QuotientGroup.congr _ _ eE (pCore_map_iso 2 eE)).trans eW
  have hc : Nat.card X = 3 := by
    rw [←Nat.card_congr eQ.toEquiv]
    exact SolvableHeisenbergFullStar_cyclic_three_lift_card h structural (W.map F.H.subtype) hEpoint hEA hWM
      (eQ.isCyclic.mpr hcyc) (hX.of_equiv eQ.symm)
  have hcZ : Nat.card (star F (F.Li L 1)) = 3 := pointResidual_star_card_of_normal h structural hn
  exact (eq_of_le_of_card_ge hZX (by rw [hc,hcZ])).symm

/-- In the full original quotient, the local Heisenberg residual has precisely
its marked central cubic as centralizer. -/
theorem local_solvable_heisenberg_full_star_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) := by
  obtain ⟨hRn,heR,hR3,hRres,hZ,hC3,hCc⟩ :=
    local_solvable_heisenberg_full_star h hab structural previous faithful hs I hI hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hZC : star F (F.Li L 1) ≤ centralizer (R : Set (HStar F.H)) := by
    rw [hZ,map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  exact ⟨hRn,heR,hR3,hRres,hZ,full_star_normal_cyclic_three_eq_point
    h hab structural previous (original_solvable_point_normal h hab structural previous faithful hs)
    (centralizer (R : Set (HStar F.H))) hC3 hCc hZC⟩

/-- The proper local selected under original solvability has a normal
Heisenberg image in the full quotient whose centralizer is exactly L₁*. -/
theorem original_solvable_full_star_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
        R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) := by
  obtain ⟨I,hIH,hI,_,_,hn,he,_⟩ := original_solvable_proper_heisenberg_normal
    d h hab structural previous faithful earlier hs
  exact ⟨I,hIH,hI,local_solvable_heisenberg_full_star_centralizer
    h hab structural previous faithful hs I hI hn he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource


end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The full three-core and the remaining SL₂(3) extension

The actual local residual belongs to Ξ(G,T). Restrict it to the full point
normalizer and transport its two-core/Frattini action along the literal
quotient map. Its image is irreducible under the full quotient action,
and hence is exactly the full three-core.

Apply this to the proper local supplied by original solvability. The
full-residual exclusion rules out equality; a cubic quotient would make
the full two-residual a three-group, contradicting the identified core.
Thus the remaining quotient is literally SL₂(3). The extension is retained
without an assumed splitting or a rank-three conclusion.

Source: Aschbacher–Smith 14.7.15(2–3), 14.7.27–29, printed
pp.1047,1054–1055, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private def SolvableHeisenbergThreeCore_imageFrattiniEquiv {D : Type*} [Group D]
    (N : Subgroup D) [N.Normal] :
    XiFrattiniQuotient N ≃*
      ((N.map (QuotientGroup.mk' (pCore 2 D))) ⧸
        frattini (N.map (QuotientGroup.mk' (pCore 2 D)))) :=
  QuotientGroup.congr _ _ (coreQuotientEquivImage 2 N) (frattini_map_mulEquiv _)

private theorem SolvableHeisenbergThreeCore_imageFrattiniEquiv_mk {D : Type*} [Group D]
    (N : Subgroup D) [N.Normal] (x : N) :
    SolvableHeisenbergThreeCore_imageFrattiniEquiv N (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)) =
      QuotientGroup.mk' _ (coreQuotientEquivImage 2 N (QuotientGroup.mk' _ x)) := rfl

private theorem SolvableHeisenbergThreeCore_imageFrattiniEquiv_action {D : Type*} [Group D]
    (N S : Subgroup D) [N.Normal] (hn : S ≤ normalizer (N : Set D))
    (s : S) (x : XiFrattiniQuotient N) :
    SolvableHeisenbergThreeCore_imageFrattiniEquiv N (xiFrattiniAction S N hn s x) =
      quotientAut (frattini (N.map (QuotientGroup.mk' (pCore 2 D))))
        (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 D) (s : D)))
        (SolvableHeisenbergThreeCore_imageFrattiniEquiv N x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H x =>
      change SolvableHeisenbergThreeCore_imageFrattiniEquiv N (xiFrattiniAction S N hn s
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ x))) =
          quotientAut (frattini (N.map (QuotientGroup.mk' (pCore 2 D))))
            (MulAut.conjNormal (QuotientGroup.mk' (pCore 2 D) (s : D)))
            (SolvableHeisenbergThreeCore_imageFrattiniEquiv N (QuotientGroup.mk' _ (QuotientGroup.mk' _ x)))
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk,
        SolvableHeisenbergThreeCore_imageFrattiniEquiv_mk]
      apply congrArg (QuotientGroup.mk' _)
      apply Subtype.ext
      simp only [coreQuotientEquivImage_apply_mk]
      change QuotientGroup.mk' (pCore 2 D) _ =
        QuotientGroup.mk' (pCore 2 D) (s : D) *
          (coreQuotientEquivImage 2 N _) *
          (QuotientGroup.mk' (pCore 2 D) (s : D))⁻¹
      rw [coreQuotientEquivImage_apply_mk,←map_inv,←map_mul,←map_mul]
      rfl

private theorem SolvableHeisenbergThreeCore_xi_image_frattini_irreducible {D : Type*} [Group D]
    (N S : Subgroup D) [N.Normal] (hXi : N ∈ Xi D S)
    (J : Subgroup ((N.map (QuotientGroup.mk' (pCore 2 D))) ⧸
        frattini (N.map (QuotientGroup.mk' (pCore 2 D)))))
    (hJ : ∀ a : D ⧸ pCore 2 D, ∀ x ∈ J,
      quotientAut (frattini (N.map (QuotientGroup.mk' (pCore 2 D))))
        (MulAut.conjNormal a) x ∈ J) : J = ⊥ ∨ J = ⊤ := by
  let e := SolvableHeisenbergThreeCore_imageFrattiniEquiv N
  have hinv : ∀ s : S, ∀ x ∈ J.comap e.toMonoidHom,
      xiFrattiniAction S N hXi.invariant s x ∈ J.comap e.toMonoidHom := by
    intro s x hx
    change e (xiFrattiniAction S N hXi.invariant s x) ∈ J
    rw [SolvableHeisenbergThreeCore_imageFrattiniEquiv_action]
    exact hJ _ _ hx
  rcases hXi.irreducible _ hinv with he | he
  · left
    have hh := congrArg (map e.toMonoidHom) he
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,Subgroup.map_bot] using hh
  · right
    have hh := congrArg (map e.toMonoidHom) he
    simpa only [map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
      map_top_of_surjective e.toMonoidHom e.surjective] using hh


/-- The proper local Heisenberg image is the full three-core of the original
point quotient, using the actual transported Ξ action. -/
theorem local_solvable_full_three_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    pCore 3 (HStar F.H) = star F ((pResidual 2 I).map I.subtype) := by
  let R₀ := (pResidual 2 I).map I.subtype
  let A := R₀.subgroupOf F.H
  let R := star F R₀
  have hIH : I ≤ F.H := hI.2.1
  let := hs
  have hIs : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective (inclusion_injective hIH)
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  let : A.Normal := local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hIH
  have hX := local_solvable_heisenberg_residual_mem_Xi h hab structural previous faithful I hI hIs hn he
  have hXi : A ∈ Xi F.H ((T : Subgroup G).subgroupOf F.H) :=
    (mem_XiIn_iff_subgroupOf ((F.sylow_le_of_mem_Hz hI).trans hIH)
      ((map_subtype_le _).trans hIH)).mp ⟨(map_subtype_le _).trans hIH,hX⟩
  obtain ⟨hRn,heR,_,_,hZ,hC⟩ := local_solvable_heisenberg_full_star_centralizer
    h hab structural previous faithful hs I hI hn he
  let : R.Normal := hRn
  have hc : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  apply heisenberg_pCore_eq_of_irreducible R heR.some hc
  exact SolvableHeisenbergThreeCore_xi_image_frattini_irreducible A ((T : Subgroup G).subgroupOf F.H) hXi

/-- Under original solvability the only surviving residual comparison is a
proper Heisenberg three-core with literal SL₂(3) quotient. This does not assert
that the extension splits. -/
theorem original_solvable_full_residual_sl23
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I < F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      let R := star F ((pResidual 2 I).map I.subtype)
      ∃ hRn : R.Normal, letI := hRn
        Nonempty (R ≃* HeisenbergPrime 3) ∧
        pCore 3 (HStar F.H) = R ∧ R < pResidual 2 (HStar F.H) ∧
        star F (F.Li L 1) = (center R).map R.subtype ∧
        centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) ∧
        Nonempty (((pResidual 2 (HStar F.H)) ⧸
          R.subgroupOf (pResidual 2 (HStar F.H))) ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  obtain ⟨I,hIH,hI,_,_,hn,he,_⟩ := original_solvable_proper_heisenberg_normal
    d h hab structural previous faithful earlier hs
  obtain ⟨hRn,heR,_,hRres,hZ,hC⟩ := local_solvable_heisenberg_full_star_centralizer
    h hab structural previous faithful hs I hI hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  change Nonempty (R ≃* HeisenbergPrime 3) at heR
  have hcore := local_solvable_full_three_core h hab structural previous faithful hs I hI hn he
  have hc : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  have hne : R ≠ pResidual 2 (HStar F.H) := by
    intro heq
    apply extraspecial_star_residual_impossible d h hab structural previous faithful earlier
    exact ⟨(MulEquiv.subgroupCongr heq).symm.trans heR.some⟩
  exact ⟨I,hIH,hI,hRn,heR,hcore,lt_of_le_of_ne hRres hne,hZ,hC,
    heisenberg_twoResidual_sl23_of_pCore_eq R heR.some hc hcore hRres hne⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Nonsolvability of the original point normalizer

Retain the proper local Heisenberg residual inside the full point quotient.
Its literal center is the original point cubic and its centralizer is that
cubic. The critical involution argument therefore gives a faithful binary
six-space without identifying the local residual with the full residual.

Under original solvability the full residual has order 648 and centralizes
the point cubic. Its faithful image in GL₃(4) forces three-rank at least
three, contradicting strong quasithinness. This excludes solvability of the
full original point normalizer; it does not assert nonsolvability of all
members of the local family.

Source: Aschbacher–Smith 14.7.15(3), 14.7.16(1), printed pp.1047–1048,
refs/quasithin.pdf, used in the solvable reduction 14.7.27–29.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Theory.GroupTheory
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem SolvableHeisenbergExclusion_heisenberg_actor_faithful
    {D : Type*} [Group D] [Finite D]
    (R : Subgroup D) [R.Normal] (hodd : Odd (Nat.card R))
    (hcR : centralizer (R : Set D) ≤ R)
    (A : Subgroup D) (hA : IsPGroup 2 A) :
    Function.Injective ((MulAut.conjNormal : D →* MulAut (R)).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : D) ∈ centralizer (R : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact ha
  have hp := hcR hc
  have hdis : Disjoint A (R) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_left.pow_left n
  have hz := hdis.le_bot ⟨a.property,hp⟩
  exact Subtype.ext (mem_bot.mp hz)

private theorem SolvableHeisenbergExclusion_point_core_rank_one_of_normal_heisenberg_subgroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (P : Subgroup (HStar F.H)) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (hZ : star F (F.Li L 1) = (center P).map P.subtype)
    (hcP : centralizer (P : Set (HStar F.H)) ≤ P) :
    primeRank 2 (star F (F.Ri L 1)) ≤ 1 := by
  let R := star F (F.Ri L 1)
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hP : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  apply (primeRank_le_iff_elementary_card_le R).mpr
  intro E hE
  let := hE
  let A := E.map R.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map R.subtype
  let f : A →* MulAut P := (MulAut.conjNormal : HStar F.H →* MulAut P).comp A.subtype
  have hf : Function.Injective f := SolvableHeisenbergExclusion_heisenberg_actor_faithful P (by rw [hP]; decide) hcP A (IsElementaryAbelian.isPGroup 2 A)
  have hcenter : ∀ a : A, ∀ z ∈ center P, f a z = z := by
    intro a z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [hZ]
      exact mem_map_of_mem P.subtype hz
    have hc := point_core_star_centralizes_of_normal h structural hn
      (map_subtype_le E a.property)
    change (a : HStar F.H) * (z : HStar F.H) * (a : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  have hb := MulAut.elementary_two_center_preserving_card_le_two hP f hf hcenter
  simpa only [A,card_map_of_injective R.subtype_injective,pow_one] using hb

variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- A normal, self-centralizing Heisenberg subgroup with the original point
center makes every literal section a faithful star action of binary degree
six, irreducible on that Heisenberg subgroup. -/
theorem normal_heisenberg_subgroup_section
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (P : Subgroup (HStar F.H)) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (hZ : star F (F.Li L 1) = (center P).map P.subtype)
    (hcP : centralizer (P : Set (HStar F.H)) ≤ P)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ σ : Representation (ZMod 2) (HStar F.H) W,
      σ.comp (starMap F) = ρ ∧ Function.Injective σ ∧
      Module.finrank (ZMod 2) W = 6 ∧
      IsIrreducible (σ.comp P.subtype) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  let : IsExtraspecial 3 P :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hP : Nat.card P = 27 := (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hescape := h.flag_escape_at F previous
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 F.H) x
    have hk : a ∈ ρ.ker := by
      rw [←hσ]
      exact hx
    rw [section_action_kernel_eq_core_of_escape h structural hescape s] at hk
    exact (QuotientGroup.eq_one_iff _).mpr hk
  have hfix : invariants ((σ.comp P.subtype).comp (center P).subtype) = ⊥ := by
    obtain ⟨z,hz,hgen,hfree⟩ := exists_fixedFree_cubic_of_point_normal h structural hn s σ hσ
    rw [Submodule.eq_bot_iff]
    intro w hw
    apply hfree w
    have hzm : z ∈ (center P).map P.subtype := by
      rw [←hZ,←hgen]
      exact mem_zpowers z
    obtain ⟨z,hzc,rfl⟩ := hzm
    exact hw ⟨z,hzc⟩
  obtain ⟨c,hs,_,_,_⟩ := exists_selected_critical_geometry_of_point_normal h hab structural previous hn
  have hA := critical_card_two_of_point_core_rank_one h hab structural c hs
    (SolvableHeisenbergExclusion_point_core_rank_one_of_normal_heisenberg_subgroup h structural hn P e hZ hcP)
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  have hx2 : (x : HStar F.H) ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := x)
    rw [hA] at he
    exact congrArg Subtype.val he
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hfaith := SolvableHeisenbergExclusion_heisenberg_actor_faithful P (by rw [hP]; decide) hcP A hA2
  have hne : (MulAut.conjNormal (x : HStar F.H) : MulAut P) ≠ 1 := by
    intro he
    exact hx (hfaith (he.trans (map_one _).symm))
  have hcenter : ∀ z ∈ center P, (MulAut.conjNormal (x : HStar F.H) : MulAut P) z = z := by
    intro z hz
    apply Subtype.ext
    have hz' : (z : HStar F.H) ∈ star F (F.Li L 1) := by
      rw [hZ]
      exact mem_map_of_mem P.subtype hz
    have hc := critical_actor_star_centralizes_of_point_normal h structural hn c x.property
    change (x : HStar F.H) * (z : HStar F.H) * (x : HStar F.H)⁻¹ = z
    rw [←hc z hz',mul_assoc,mul_inv_cancel,mul_one]
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hdisp := critical_displacement_two_of_normal_card_two
    h hab structural hescape hn s c hs hA a haA haQ
  have hsmall : fixedCodim σ (zpowers (x : HStar F.H)) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank,←he]
    change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range ≤ 2
    rw [hσ,hdisp]
  exact ⟨σ,hσ,hf,ExtraspecialBinarySix.six_and_irreducible_of_small_involution σ hf P hP hfix x hx2 hne hcenter hsmall⟩

/-- The full original point normalizer is nonsolvable. The proper local
Heisenberg subgroup is retained literally throughout the argument. -/
theorem original_point_not_solvable
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ¬ Group.IsSolvable F.H := by
  intro hs
  obtain ⟨I,hIH,hI,hRn,he,hcore,hlt,hZ,hC,⟨eQ⟩⟩ :=
    original_solvable_full_residual_sl23 d h hab structural previous faithful earlier hs
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hn := original_solvable_point_normal h hab structural previous faithful hs
  have hcR : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  obtain ⟨σ,hσ,hf,hd,hirr⟩ := normal_heisenberg_subgroup_section
    h hab structural previous hn R he.some hZ hcR s
  let K := pResidual 2 (HStar F.H)
  let A := R.subgroupOf K
  let eA : A ≃* R := subgroupOfEquivOfLe hlt.le
  let : IsExtraspecial 3 A :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv (eA.trans he.some).symm
  have hA : Nat.card A = 27 :=
    (Nat.card_congr (eA.trans he.some).toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hQ : Nat.card (K ⧸ A) = 24 :=
    (Nat.card_congr eQ.toEquiv).trans GLS3.Chapter5.SchurPresentation.sl23_card_eq
  have hK : Nat.card K = 648 := by
    rw [card_eq_card_quotient_mul_card_subgroup A,hQ,hA]
  let Z := star F (F.Li L 1)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hn
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hn
  let : IsCyclic Z := isCyclic_of_prime_card hZcard
  have hAut : IsPGroup 2 (MulAut Z) := IsPGroup.of_card (n := 1) (by
    rw [IsCyclic.card_mulAut,hZcard]; decide)
  have hcentral : K ≤ centralizer (Z : Set (HStar F.H)) := by
    have hh := pResidual_le_ker_of_isPGroup 2
      (MulAut.conjNormal : HStar F.H →* MulAut Z) hAut
    rwa [MulAut.conjNormal_ker_eq_centralizer] at hh
  have hcenter : (center A).map A.subtype ≤ center K := by
    rintro a ⟨x,hx,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hxR : eA x ∈ center R := by
      apply mem_center_iff.mpr
      intro r
      obtain ⟨w,rfl⟩ := eA.surjective r
      exact congrArg eA (mem_center_iff.mp hx w)
    have hxZ : (((x : A) : K) : HStar F.H) ∈ Z := by
      rw [show Z = (center R).map R.subtype from hZ]
      exact mem_map_of_mem R.subtype hxR
    exact (hcentral y.property _ hxZ).symm
  have hthree := Representation.ExtraspecialBinarySixCubicRank.three_le_primeRank
    (σ.comp K.subtype) A (hf.comp K.subtype_injective) hA hd hcenter hK
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hz
    have hh := F.card 1 (by decide)
    rw [hz,card_bot] at hh
    norm_num at hh
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hrD : primeRank 3 (HStar F.H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 F.H) pCore_isPGroup).trans
      ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))
  have hrK : primeRank 3 K ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 K.subtype K.subtype_injective).trans hrD
  omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# A three-free component in the original local quotient

If O₃′(I/O₂(I)) is nontrivial, the already proved Fitting equality
extracts a genuine C-component there. The full known-simple A.3.6
classification identifies its actual carrier as a Suzuki group. Lift it
through the original quotient, retaining the intrinsic two-core kernel.
The normal-or-index-two component theorem also gives normality of its
Sylow conjugate span.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, refs/quasithin.pdf;
1.2.1(3) and A.3.6 supply the component classification.
-/

public section
open Subgroup Theory.GroupTheory



namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

theorem local_star_sqtk
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    IsSQTK KnownSimple.IsKnownSimple (HStar I) := by
  have hne : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H :=
    ⟨F.Vi 1,hne,IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hIs := (IsSQTK.equiv (subgroupOfEquivOfLe hI.2.1)).mp
    ((h.source.simpleQTKE.twoLocal_sqtk hH).subgroup (I.subgroupOf F.H))
  exact ChapterE.Structure.sqtk_two_quotient hIs (pCore 2 I) pCore_isPGroup

theorem local_threePrime_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pPrimeCore 3 (HStar I) ≠ ⊥) :
    ∃ K : Subgroup I, K.IsCComponent ∧
      K.map (QuotientGroup.mk' (pCore 2 I)) ≤ pPrimeCore 3 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp K.subtype).ker = pCore 2 K ∧
      ∃ m, 1 ≤ m ∧ Nonempty ((K ⧸ pCore 2 K) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  obtain ⟨B,hB,hBcore⟩ := exists_cComponent_le_primeComplement_of_fitting_isPGroup 3
    (local_fitting_isThreeGroup h hab structural previous faithful I hI) hne
  have h3 : ¬ 3 ∣ Nat.card B := by
    intro hd
    exact (Nat.prime_three.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)
      (hd.trans (card_dvd_of_le hBcore))
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (HStar I) (local_star_sqtk h I hI) (pCore_quotient_pCore_eq_bot 2) B hB
  obtain ⟨m,hm,⟨e⟩⟩ := hc.suzuki_of_three_free h3
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  obtain ⟨K,hK,hKB⟩ := hB.exists_map_quotient_eq (pCore 2 I)
  refine ⟨K,hK,hKB.symm ▸ hBcore,?_,m,hm,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hK.subnormal).symm
  · exact ⟨(cComponentTwoCoreQuotientEquiv hK).trans
      ((MulEquiv.subgroupCongr hKB).trans e)⟩

theorem local_component_sylow_span_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    (conjugateSpanBy K ((T : Subgroup G).subgroupOf I)).Normal := by
  have hi := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (local_star_sqtk h I hI) hK
  have ho : K.Normal ∨ (normalizer (K : Set I)).index = 2 :=
    hi.imp_right And.left
  exact conjugateSpanBy_sylow_normal K (T.subtype (F.sylow_le_of_mem_Hz hI)) ho

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The actual quadratic actor after the three-prime reduction

Reduce an original local to J = ⟨Kᵀ⟩L₁T using component escape. The
same Suzuki component keeps its intrinsic two-core quotient. Its orbit
image is normal, three-free, and supplements the point-parabolic image.
The normal point cubic retains order three, full movement, and commutation
with that entire orbit. The existing source edge then constructs a
faithful quadratic actor on the literal U_J/V₁ section. The theorem records
the exact orbit identity, so faithfulness is used on the whole orbit.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, using 14.5.18–19,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ThreePrimeActor_three_free_of_twoCore_image {D : Type*} [Group D] [Finite D]
    (N : Subgroup D) (hN : N.map (QuotientGroup.mk' (pCore 2 D)) ≤ pPrimeCore 3 (D ⧸ pCore 2 D)) :
    Nat.Coprime 3 (Nat.card N) := by
  let f := (QuotientGroup.mk' (pCore 2 D)).comp N.subtype
  have hp : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hq : Nat.Coprime 3 (Nat.card f.range) := by
    rw [MonoidHom.range_comp,range_subtype]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le hN)
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hn]
  exact hq.mul_right ((by decide : Nat.Coprime 3 2).pow_right n)

/-- The source reduction of a nonzero three-prime core produces the actual
Suzuki component, its Sylow orbit and a quadratic actor on the literal reduced
local section. The normal point cubic retains full movement and commutes with
the whole orbit image. No natural-module recognition is assumed. -/
theorem local_threePrime_reduced_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).Normal)
    (hne : pPrimeCore 3 (HStar I) ≠ ⊥) :
    ∃ (K : Subgroup I) (m : ℕ), K.IsCComponent ∧ 1 ≤ m ∧
      K.map (QuotientGroup.mk' (pCore 2 I)) ≤ pPrimeCore 3 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp K.subtype).ker = pCore 2 K ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
      let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
      let KJ := (K.map I.subtype).subgroupOf J
      let X := (N.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
      let Z := ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))
      J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧ KJ.IsCComponent ∧
      Nonempty ((KJ ⧸ pCore 2 KJ) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp KJ.subtype).ker = pCore 2 KJ ∧
      X = conjugateSpanBy (KJ.map (QuotientGroup.mk' (pCore 2 J)))
        (((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) ∧
      X.Normal ∧ Nat.Coprime 3 (Nat.card X) ∧
      X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map
        (QuotientGroup.mk' (pCore 2 J)) = ⊤ ∧
      ((F.Li L 1).subgroupOf J).Normal ∧ Z.Normal ∧ Nat.card Z = 3 ∧
      X ≤ centralizer (Z : Set (HStar J)) ∧ ⁅F.UH J,F.Li L 1⁆ = F.UH J ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J),
        let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          fixedSpace a.representation Z = ⊥ ∧ quadraticRatio a.representation ≤ 2 ∧
          ∃ A : Subgroup J,
            A ≤ (F.Ri L 1).subgroupOf J ∧
            IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 J))) ∧
            IsQuadratic a.representation (A.map (QuotientGroup.mk' (pCore 2 J))) ∧
            fixedCodim a.representation (A.map (QuotientGroup.mk' (pCore 2 J))) ≤
              2 * rank (A.map (QuotientGroup.mk' (pCore 2 J))) ∧
            A.map (QuotientGroup.mk' (pCore 2 J)) ⊓ centralizer (X : Set (HStar J)) = ⊥ := by
  obtain ⟨K,hK,hK3,hker,m,hm,⟨eK⟩⟩ :=
    local_threePrime_component h hab structural previous faithful I hI hne
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let X := (N.subgroupOf J).map q
  let Z := ((F.Li L 1).subgroupOf J).map q
  obtain ⟨hNI,hJI,hJ⟩ := local_component_reduced_mem_Hz_at h structural I hI K hK
  have hNJ : N ≤ J := le_sup_left
  have hKI : ((K.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hK
  have hKJle : K.map I.subtype ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hKJ : KJ.IsCComponent := hKI.subgroupOf_of_le hKJle hJI
  let e : KJ ≃* K := (subgroupOfEquivOfLe hKJle).trans
    (equivMapOfInjective K I.subtype I.subtype_injective).symm
  have hNJn : (N.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNJ).mpr
      (hJI.trans ((normal_subgroupOf_iff_le_normalizer (hNJ.trans hJI)).mp hNI))
  let : X.Normal := hNJn.map q (QuotientGroup.mk'_surjective _)
  have horbit : X = conjugateSpanBy (KJ.map q) (((T : Subgroup G).subgroupOf J).map q) := by
    rw [←map_conjugateSpanBy]
    apply congrArg (map q)
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hNJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hKJle,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)]
  have hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ := by
    rw [←Subgroup.map_sup,←subgroupOf_sup hNJ (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right)]
    change (J.subgroupOf J).map q = ⊤
    rw [subgroupOf_self,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I :=
    sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  have hLI : F.Li L 1 ≤ I := F.Li_one_le_of_mem_Hz hI
  have hLJ : F.Li L 1 ≤ J := F.Li_one_le_of_mem_Hz hJ
  have hnI := local_point_normal_of_star_normal h structural I hBI hn
  have hnJ : ((F.Li L 1).subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLJ).mpr
      (hJI.trans ((normal_subgroupOf_iff_le_normalizer hLI).mp hnI))
  let : Z.Normal := hnJ.map q (QuotientGroup.mk'_surjective _)
  have hcZ : Nat.card Z = 3 := local_point_star_card_of_normal h structural J hLJ hnJ
  have hcN : Nat.Coprime 3 (Nat.card N) := by
    let N₀ := conjugateSpanBy K ((T : Subgroup G).subgroupOf I)
    have heN : N₀.map I.subtype = N := by
      rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI)]
    have hN₀ : N₀.map (QuotientGroup.mk' (pCore 2 I)) ≤ pPrimeCore 3 (HStar I) := by
      rw [map_conjugateSpanBy]
      exact conjugateSpanBy_le hK3 le_normalizer_of_normal
    rw [←heN,card_map_of_injective I.subtype_injective]
    exact ThreePrimeActor_three_free_of_twoCore_image N₀ hN₀
  have hcX : Nat.Coprime 3 (Nat.card X) := by
    apply Nat.Coprime.of_dvd_right (card_map_dvd (N.subgroupOf J) q)
    rw [Nat.card_congr (subgroupOfEquivOfLe hNJ).toEquiv]
    exact hcN
  have hcXZ : X ≤ centralizer (Z : Set (HStar J)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    apply (commutator_le_inf (H₁ := X) (H₂ := Z)).trans
    apply (disjoint_of_coprime_natCard (show Nat.Coprime (Nat.card X) (Nat.card Z) from ?_)).eq_bot.le
    rw [hcZ]
    exact hcX.symm
  have hmoved : ⁅F.UH J,F.Li L 1⁆ = F.UH J :=
    (conjugateSpanBy_eq_commutator_of_seed V J (F.Li L 1) (F.Li L 1)
      hLJ ((normal_subgroupOf_iff_le_normalizer hLJ).mp hnJ) le_rfl
      (seed_commutator h F)).symm
  refine ⟨K,m,hK,hm,hK3,hker,⟨eK⟩,hJI,hJ,hKJ,
    ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eK⟩,?_,
    horbit,inferInstance,hcX,hgen,hnJ,inferInstance,hcZ,hcXZ,hmoved,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hKJ.subnormal).symm
  · obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod,hfaith⟩ :=
      local_prime_supplement_quadratic_actor h hab structural previous J hJ X hgen
    let := hU
    exact ⟨hU,a,local_point_fixedSpace_eq_bot h structural J hLJ hnJ a,hq,A,
      hAR,hA,hquad,hcod,hfaith⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Source 14.7.7 for the original local family

Normality of the actual point cubic in I/O₂(I) forces its full
three-prime core to vanish. A nonzero core supplies a genuine Suzuki
component and the literal reduced local with its quadratic actor. Apply
the normal-or-exchanged full-movement contradiction on that same quotient.
No solvability or natural-recognition premise is added.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Source 14.7.7 on the original local family: normality of the actual point
cubic eliminates the full three-prime core, without a solvability hypothesis. -/
theorem local_threePrimeCore_eq_bot_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).Normal) :
    pPrimeCore 3 (HStar I) = ⊥ := by
  by_contra hne
  obtain ⟨K,m,hK,hm,hK3,hker,⟨eK⟩,hJI,hJ,hKJ,⟨eJ⟩,hkJ,horbit,hnX,hcX,hgen,
    hnJ,hnZ,hcZ,hcomm,hmoved,hU,a,hfree,hq,A,hAR,hA,hquad,hcod,hfaith⟩ :=
    local_threePrime_reduced_actor h hab structural previous faithful I hI hn hne
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := KJ.map q
  let X := (N.subgroupOf J).map q
  let Z := ((F.Li L 1).subgroupOf J).map q
  let := hU
  let S : Sylow 2 (HStar J) :=
    (T.subtype (F.sylow_le_of_mem_Hz hJ)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have hB : B.IsCComponent := hKJ.map_quotient (pCore 2 J)
  let eB := (cComponentTwoCoreQuotientEquiv hKJ).symm.trans eJ
  let : Group.IsPerfect B := hB.perfect
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hz := Chapter13.Section08.Components.Suzuki.NaturalSections.SectionRecognition.center_eq_bot_of_equiv_suzuki eB
  let : IsQuasisimple B := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hidx := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (ChapterE.Structure.sqtk_two_quotient (local_star_sqtk h J hJ) (pCore 2 (HStar J)) pCore_isPGroup) hB
  have hi : B.Normal ∨ (normalizer (B : Set (HStar J))).index = 2 := hidx.imp_right And.left
  have hXS : X = componentOrbit B (S : Subgroup (HStar J)) := by
    change X = conjugateSpanBy B (S : Subgroup (HStar J)) at horbit
    exact horbit.trans (conjugateSpanBy_eq_iSup_conj _ _)
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) := by
    let E := F.Li L 1 ⊔ (T : Subgroup G)
    have hh := pCoreIn_le_sylow E (T.subtype (show (T : Subgroup G) ≤ E from le_sup_right))
    change E.pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ E from le_sup_right)] using hh
  have hAS : A.map q ≤ (S : Subgroup (HStar J)) :=
    map_mono (hAR.trans (subgroupOf_mono J hRT))
  change X ≤ centralizer (Z : Set (HStar J)) at hcomm
  change A.map q ⊓ centralizer (X : Set (HStar J)) = ⊥ at hfaith
  rw [hXS] at hcomm hfaith
  exact suzuki_orbit_impossible_of_fixedFree_cubic a.representation a.faithful
    (local_star_sqtk h J hJ) B ⟨hB.subnormal,inferInstance⟩ S hi (by omega) eB
    Z (A.map q) hcZ hfree hcomm hAS hA hquad hcod hfaith

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding every original solvable local

The minimal solvable local supplies a Heisenberg residual normal in the
full point normalizer. Its characteristic point cubic is normal there.
Source 14.7.7 now gives the missing three-prime-core vanishing without
assuming that the full point normalizer is solvable. Consequently the
Heisenberg image is self-centralizing, and its outer action in GL₂(3)
forces full-point solvability, contradicting the previously proved
full-point exclusion. The final application gives the literal 14.7.29
containment for every solvable point-parabolic overgroup.

Source: Aschbacher–Smith, 14.7.7, 14.7.14 and 14.7.29, printed
pp.1045,1047–1055, refs/quasithin.pdf. This does not yet prove the
component and module classification through 14.7.52.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem SolvableLocalExclusion_fullStar_image
    (I : Subgroup G) (hIH : I ≤ F.H)
    (hn : (((pResidual 2 I).map I.subtype).subgroupOf F.H).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    (star F ((pResidual 2 I).map I.subtype)).Normal ∧
      Nonempty (star F ((pResidual 2 I).map I.subtype) ≃* HeisenbergPrime 3) := by
  let R := (pResidual 2 I).map I.subtype
  let A := R.subgroupOf F.H
  let := hn
  let eR := (pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective
  let eA : A ≃* pResidual 2 I :=
    (subgroupOfEquivOfLe ((map_subtype_le _).trans hIH)).trans eR.symm
  let eLocal := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  let e := (coreQuotientEquivImage 2 A).symm.trans
    ((QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).trans (eLocal.trans he.some))
  exact ⟨hn.map (starMap F) (QuotientGroup.mk'_surjective _),⟨e⟩⟩

private theorem SolvableLocalExclusion_fullStar_three_rank
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    primeRank 3 (HStar F.H) ≤ 2 := by
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 F.H) pCore_isPGroup).trans
    ((h.source.simpleQTKE.twoLocal_sqtk hH).stronglyQuasithin 3 (by decide) (by decide))

theorem local_solvable_heisenberg_full_star_of_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hIs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      IsPGroup 3 (centralizer (R : Set (HStar F.H))) ∧
      IsCyclic (centralizer (R : Set (HStar F.H))) := by
  let R₀ := (pResidual 2 I).map I.subtype
  let R := star F R₀
  have hIH : I ≤ F.H := hI.2.1
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  obtain ⟨hRn,⟨e⟩⟩ := SolvableLocalExclusion_fullStar_image I hIH
    (local_solvable_heisenberg_normal_in_twoLocal h hab structural previous faithful
      I hI hIs hn he F.H hH hIH) he
  let : R.Normal := hRn
  have hR3 : IsPGroup 3 R :=
    (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
  have hRres : R ≤ pResidual 2 (HStar F.H) := by
    have hh : R₀ ≤ K F := embedded_pResidual_mono 2 hIH
    have hh' : R₀.subgroupOf F.H ≤ pResidual 2 F.H := by
      rw [←residual_subgroupOf F]
      exact subgroupOf_mono F.H hh
    exact (map_mono hh').trans (map_pResidual_le 2 (starMap F))
  have hnH := local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hIH
  let Z := star F (F.Li L 1)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hnH
  let : Z.Normal := hnH.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZR₀ : F.Li L 1 ≤ R₀ := by
    have hh := embedded_pResidual_mono 2 (F.Li_one_le_of_mem_Hz hI)
    rw [(pResidual_eq_top_iff 2 (F.Li L 1)).mpr (isPPerfect_embedded_pResidual 2 _),
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hZR : Z ≤ R := map_mono (subgroupOf_mono F.H hZR₀)
  have hZcard : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hnH
  have hZRc : Nat.card (Z.subgroupOf R) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv).trans hZcard
  have hcenter : Z = (center R).map R.subtype := by
    have hh : Z.subgroupOf R = center R := eq_of_le_of_card_ge
      (hR3.normal_le_center_of_card_dvd_prime _ (by rw [hZRc]))
      (by rw [hZRc,Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center])
    simpa only [map_subgroupOf_eq_of_le hZR] using congrArg (map R.subtype) hh
  have hcore : pPrimeCore 3 (HStar F.H) = ⊥ :=
    local_threePrimeCore_eq_bot_of_point_normal h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)) inferInstance
  exact ⟨hRn,⟨e⟩,le_sSup ⟨hRn,hR3⟩,hRres,hcenter,
    heisenberg_centralizer_isCyclic_threeGroup R e (SolvableLocalExclusion_fullStar_three_rank h) hcore⟩

/-- The original proper-local Heisenberg centralizer argument, using only
solvability of that local subgroup, not of the full point normalizer. -/
theorem local_solvable_heisenberg_full_star_centralizer_of_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hIs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) :
    let R := star F ((pResidual 2 I).map I.subtype)
    R.Normal ∧ Nonempty (R ≃* HeisenbergPrime 3) ∧
      R ≤ pCore 3 (HStar F.H) ∧ R ≤ pResidual 2 (HStar F.H) ∧
      star F (F.Li L 1) = (center R).map R.subtype ∧
      centralizer (R : Set (HStar F.H)) = star F (F.Li L 1) := by
  obtain ⟨hRn,heR,hR3,hRres,hZ,hC3,hCc⟩ :=
    local_solvable_heisenberg_full_star_of_local h hab structural previous faithful I hI hIs hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hZC : star F (F.Li L 1) ≤ centralizer (R : Set (HStar F.H)) := by
    rw [hZ,map_center_subtype_eq_inf_centralizer]
    exact inf_le_right
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro hb
    have hc := F.card 1 (by decide)
    rw [hb,card_bot] at hc
    norm_num at hc
  have hH : IsTwoLocal F.H := ⟨F.Vi 1,hpoint,
    IsPGroup.of_card (p := 2) (n := 1) (F.card 1 (by decide)),rfl⟩
  have hnH := local_solvable_heisenberg_point_normal_in_twoLocal h hab structural previous faithful
    I hI hIs hn he F.H hH hI.2.1
  exact ⟨hRn,heR,hR3,hRres,hZ,full_star_normal_cyclic_three_eq_point
    h hab structural previous hnH (centralizer (R : Set (HStar F.H))) hC3 hCc hZC⟩

/-- Source 14.7.14: the normal Heisenberg residual of a solvable local
would make the full point normalizer solvable through its GL₂(3) outer action. -/
theorem local_solvable_heisenberg_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hIs : Group.IsSolvable I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    (he : Nonempty (pResidual 2 (HStar I) ≃* HeisenbergPrime 3)) : False := by
  obtain ⟨hRn,⟨e⟩,_,_,hZ,hC⟩ := local_solvable_heisenberg_full_star_centralizer_of_local
    h hab structural previous faithful I hI hIs hn he
  let R := star F ((pResidual 2 I).map I.subtype)
  let : R.Normal := hRn
  have hc : centralizer (R : Set (HStar F.H)) ≤ R := by
    rw [hC,hZ]
    exact map_subtype_le _
  have hR3 : IsPGroup 3 R :=
    (IsPGroup.of_card (HeisenbergPrime.card (p := 3))).of_equiv e.symm
  let : Group.IsNilpotent R := hR3.isNilpotent
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp
    (MulAut.conjNormal : HStar F.H →* MulAut R)
  let : Group.IsSolvable (HStar F.H) := Group.isSolvable_of_ker_le_range R.subtype f (by
    rw [range_subtype,heisenberg_outerAction_ker R e hc])
  let : Group.IsNilpotent (pCore 2 F.H) := pCore_isPGroup.isNilpotent
  have hs : Group.IsSolvable F.H :=
    Group.isSolvable_of_ker_le_range (pCore 2 F.H).subtype (starMap F) (by
      rw [range_subtype]
      change (QuotientGroup.mk' (pCore 2 F.H)).ker ≤ pCore 2 F.H
      rw [QuotientGroup.ker_mk'])
  exact original_point_not_solvable d h hab structural previous faithful earlier hs

/-- Source 14.7.29: every member of the original H_z is nonsolvable.
The selected minimal Heisenberg residual is lifted to the full point
normalizer using 14.7.7, with no full-point solvability assumption. -/
theorem local_not_solvable
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ Group.IsSolvable J := by
  intro hs
  obtain ⟨I,_,hI,hIs,_,hn,_,_,⟨e⟩,_⟩ :=
    local_solvable_minimal_heisenberg_residual h hab structural previous faithful J hJ hs
  let eLocal := (coreQuotientEquivImage 2 (pResidual 2 I)).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2
      (QuotientGroup.mk' (pCore 2 I)) (QuotientGroup.mk'_surjective _)))
  exact local_solvable_heisenberg_impossible d h hab structural previous faithful earlier
    I hI hIs hn ⟨eLocal.symm.trans e⟩

/-- Source 14.7.29 in its literal overgroup form: every solvable subgroup
of the point normalizer containing the point parabolic lies in N_G(L). -/
theorem solvable_point_overgroup_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hIH : I ≤ F.H)
    (hBI : F.Li L 1 ⊔ (T : Subgroup G) ≤ I)
    (hs : Group.IsSolvable I) : I ≤ normalizer (L : Set G) := by
  by_contra hout
  have hI : I ∈ F.Hz L (normalizer (L : Set G)) := by
    refine ⟨⟨?_,fun _ hx => hBI (hx.elim mem_sup_left mem_sup_right)⟩,hIH,hout⟩
    have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hp : F.Vi 1 ≤ I.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc))
        ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hBI))) hIH
    intro he
    have hb := le_bot_iff.mp (he ▸ hp)
    simp [hb] at hc
  exact local_not_solvable d h hab structural previous faithful earlier I hI hs

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Quasisimple component quotients in the original local family

The Fitting subgroup of the image of a C-component embeds in the ambient
Fitting subgroup by subnormality. Source 14.7.6 makes it a three-group.
The genuine A.3.6 classification then excludes the two nonquasisimple
alternatives. Transport through the component's exact two-core quotient
proves quasisimplicity of K/O₂(K), without an odd-core assumption.

Nonsolvability from 14.7.29 supplies an actual component in every original
local, and the proved 14.5.19 argument makes that component escape N_G(L).
The subsequent component-orbit module reduction uses these conclusions.

Source: Aschbacher–Smith, 14.7.6, 14.7.29–30, printed pp.1044,1055;
A.3.6, printed pp.43–45, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The literal image of every local C-component is an ordinary component
in the local two-core quotient. Source 14.7.6 already excludes both
nonquasisimple A.3.6 alternatives. -/
theorem local_component_star_isComponent
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    IsComponent (HStar I) (K.map (QuotientGroup.mk' (pCore 2 I))) := by
  let B := K.map (QuotientGroup.mk' (pCore 2 I))
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  have hB : B.IsCComponent := hK.map_quotient (pCore 2 I)
  have hfit : IsPGroup 3 (fittingSubgroup B) := by
    have hp := (local_fitting_isThreeGroup h hab structural previous faithful I hI).to_le
      (fittingSubgroup_map_subtype_le_of_isSubnormal B hB.subnormal)
    exact hp.of_equiv (equivMapOfInjective (fittingSubgroup B) B.subtype B.subtype_injective).symm
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (HStar I) (local_star_sqtk h I hI) (pCore_quotient_pCore_eq_bot 2) B hB
  exact ⟨hB.subnormal,hc.isQuasisimple_of_fitting_isThreeGroup hB hfit⟩

/-- The quasisimplicity clause of source 14.7.30, for the intrinsic
K/O₂(K), transported through the exact component quotient map. -/
theorem local_component_twoCore_isQuasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := (local_component_star_isComponent h hab structural previous faithful I hI K hK).2
  exact IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm

/-- Every original local has a genuine C-component with its actual
quasisimple two-core quotient. The component escapes the original normalizer. -/
theorem local_exists_quasisimple_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ K : Subgroup I, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K.map I.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable
    (local_not_solvable d h hab structural previous faithful earlier I hI)
  exact ⟨K,hK,local_component_twoCore_isQuasisimple h hab structural previous faithful I hI K hK,
    local_component_not_le_normalizer_at h structural I hI K hK⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Solvable subgroups normalized by the point parabolic

The literal point parabolic L₁T is solvable, since its two-core quotient
is S₃. A solvable subgroup N of the point normalizer normalized by L₁T
therefore generates a solvable overgroup with L₁T. Source 14.7.29 places
that overgroup in M = N_G(L), and characteristic two-residual transport
shows that N normalizes the original L₁.

Apply this to normal solvable subgroups of any original local, including
its full solvable radical. The normalization formulation is also the
containment used for component Borels in 14.7.32–33. It does not assert
the odd-core equality or identify any component model.

Source: Aschbacher–Smith, 14.7.29 and the Borel reduction in 14.7.32,
printed pp.1055–1056, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem SolvableNormalized_point_parabolic_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Group.IsSolvable (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (pointQuotientEquiv_at (F := F) h structural).toMonoidHom)
      (pointQuotientEquiv_at (F := F) h structural).injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩

/-- Every solvable subgroup of the point normalizer normalized by L₁T
lies in M. This is the source containment used for component Borels. -/
theorem point_normalized_solvable_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (N : Subgroup G) (hNH : N ≤ F.H) (hs : Group.IsSolvable N)
    (hn : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (N : Set G)) :
    N ≤ normalizer (L : Set G) := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  let := hs
  let : Group.IsSolvable B := SolvableNormalized_point_parabolic_solvable h structural
  have hBH : B ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  exact le_sup_left.trans (solvable_point_overgroup_le_normalizer d h hab structural previous
    faithful earlier (N ⊔ B) (sup_le hNH hBH) le_sup_right
      (Group.isSolvable_sup_of_normalizes N B hn))

/-- The same actual subgroup normalizes the original point residual.
The normality statement concerns the literal L₁, before any quotient. -/
theorem point_normalized_solvable_normalizes_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (N : Subgroup G) (hNH : N ≤ F.H) (hs : Group.IsSolvable N)
    (hn : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (N : Set G)) :
    N ≤ normalizer (F.Li L 1 : Set G) := by
  have hNM := point_normalized_solvable_le_normalizer d h hab structural previous faithful earlier
    N hNH hs hn
  have hh := ((le_inf hNM (hNH.trans F.H.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.H)
        (pResidual 2 (L ⊓ F.H : Subgroup G)))
  have he : F.Li L 1 = (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype := by
    simp only [InvariantFlag.Li,show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,if_false]
    rfl
  rwa [he]

/-- Solvable normal subgroups of arbitrary original locals lie in M. -/
theorem local_normal_solvable_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (N : Subgroup I) [N.Normal] (hs : Group.IsSolvable N) :
    N.map I.subtype ≤ normalizer (L : Set G) := by
  have hIN : I ≤ normalizer (N.map I.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      N.le_normalizer_map I.subtype
  let := hs
  exact point_normalized_solvable_le_normalizer d h hab structural previous faithful earlier
    (N.map I.subtype) ((map_subtype_le N).trans hI.2.1)
    (Group.isSolvable_of_surjective (f := I.subtype.subgroupMap N)
      (I.subtype.subgroupMap_surjective N))
    ((sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)).trans hIN)

/-- The actual solvable radical, including every normal three-core lift,
is contained in the original normalizer. -/
theorem local_solvableRadical_le_normalizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    (solvableRadical I).map I.subtype ≤ normalizer (L : Set G) :=
  local_normal_solvable_le_normalizer d h hab structural previous faithful earlier I hI
    (solvableRadical I) inferInstance

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The three-core preimage in the original normalizer

A normal solvable subgroup of I/O₂(I) has solvable full preimage, since
the quotient kernel is a two-group. Source 14.7.29 therefore puts that
preimage in M and shows that it normalizes the literal point residual.
Apply this to O₃(I/O₂(I)) and transport normalization through the same
quotient map. No cyclicity, point normality in I, or odd-core equality
is assumed or concluded here.

Source: Aschbacher–Smith, 14.7.27–29, printed pp.1054–1055,
refs/quasithin.pdf. These are preparatory containments for the three-core
bound, using the already proved 14.7.29 by an independent route.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Pull a normal solvable subgroup of the literal star quotient back through
its full two-core. Its ambient lift lies in M and normalizes the actual L₁. -/
theorem local_normal_solvable_star_preimage_control
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (N : Subgroup (HStar I)) [N.Normal] (hs : Group.IsSolvable N) :
    let W := (N.comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    W ≤ normalizer (L : Set G) ∧ W ≤ normalizer (F.Li L 1 : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := N.comap q
  let := hs
  let : Group.IsNilpotent q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.isNilpotent
  have hBs : Group.IsSolvable B := isSolvable_comap_of_solvable_ker q N
  have hIN : I ≤ normalizer (B.map I.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      B.le_normalizer_map I.subtype
  have hBsn : Group.IsSolvable (B.map I.subtype) := by
    let := hBs
    exact Group.isSolvable_of_surjective (f := I.subtype.subgroupMap B)
      (I.subtype.subgroupMap_surjective B)
  refine ⟨local_normal_solvable_le_normalizer d h hab structural previous faithful earlier
    I hI B hBs, ?_⟩
  exact point_normalized_solvable_normalizes_point d h hab structural previous faithful earlier
    (B.map I.subtype) ((map_subtype_le B).trans hI.2.1) hBsn
    ((sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)).trans hIN)

/-- In every original local, the full preimage of O₃(I*) is contained
in M and normalizes L₁. This keeps the actual quotient map and its entire
kernel, rather than replacing the preimage by a chosen Sylow subgroup. -/
theorem local_threeCore_preimage_control
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    let W := ((pCore 3 (HStar I)).comap (QuotientGroup.mk' (pCore 2 I))).map I.subtype
    W ≤ normalizer (L : Set G) ∧ W ≤ normalizer (F.Li L 1 : Set G) := by
  let : Group.IsNilpotent (pCore 3 (HStar I)) := pCore_isPGroup.isNilpotent
  exact local_normal_solvable_star_preimage_control d h hab structural previous faithful earlier
    I hI (pCore 3 (HStar I)) inferInstance

/-- The same three-core normalizes the literal point image in I/O₂(I).
This does not assert that the point is normal in the whole local. -/
theorem local_threeCore_normalizes_point_star
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pCore 3 (HStar I) ≤ normalizer
      (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) : Set (HStar I)) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := (pCore 3 (HStar I)).comap q
  have hn := (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).2
  have hnI : B ≤ normalizer ((F.Li L 1).subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hI)]
    intro b hb
    exact hn (mem_map_of_mem I.subtype hb)
  have hm := (map_mono (f := q) hnI).trans (le_normalizer_map q)
  rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The three-core's action on the original component quotient

The full three-core preimage B lies in M = N_G(L). Let X be the
two-residual of its kernel on L/O₂(L). The original Sylow subgroup
normalizes X. An escaping C-component centralizes the three-core in the
star quotient; two-perfect normalizer lifting through O₂(I) shows that
it normalizes X. If X were nontrivial, ambient normalizer control would
put that component in M, a contradiction. Thus the action kernel is a
two-group. Since |Aut(L₃(2))| = 336 is not divisible by nine, the actual
three-core has order at most three.

The component used here is obtained from the already proved nonsolvability
of every original local. Its ordinary quasisimple star image is supplied
by ComponentQuotients, independently of the odd-core equality.

Source: Aschbacher–Smith, 14.7.27, printed pp.1054–1055, using the
normalizer control of 14.5.20 and the independent 14.7.29 route,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual three-core preimage acts on L/O₂(L) with a two-group kernel.
An escaping component rules out a nontrivial kernel two-residual. -/
theorem local_threeCore_action_kernel_two
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    let hBM := (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
    IsPGroup 2 (((normalizerQuotientAction L (pCore 2 L)).comp (inclusion hBM)).ker) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let N := (pCore 3 (HStar I)).comap q
  let B := N.map I.subtype
  let M := normalizer (L : Set G)
  let a := normalizerQuotientAction L (pCore 2 L)
  let C := a.ker.map M.subtype
  let E := B ⊓ C
  let X := (pResidual 2 E).map E.subtype
  have hBI : B ≤ I := map_subtype_le N
  have hBM : B ≤ M :=
    (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
  have hIB : I ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      N.le_normalizer_map I.subtype
  have hMC : M ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      a.ker.le_normalizer_map M.subtype
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf ((F.sylow_le_of_mem_Hz hI).trans hIB)
      ((h.sylow_normalizes_at structural).trans hMC)).trans inf_normalizer_le_normalizer_inf
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    hTE.trans (normalizer_le_normalizer_characteristic_image E (pResidual 2 E))
  have hXB : X ≤ B := (map_subtype_le _).trans inf_le_left
  have hXC : X ≤ C := (map_subtype_le _).trans inf_le_right
  have hXI : X ≤ I := hXB.trans hBI
  have hXM : X ≤ M := hXB.trans hBM
  have hcomm : ⁅L,X⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le_of_normalizerQuotientAction_eq_one L X (pCore 2 L) hXM
    intro x
    obtain ⟨c,hc,he⟩ := hXC x.property
    have hh : c = inclusion hXM x := Subtype.ext he
    exact hh ▸ hc
  obtain ⟨K,hK,_,hout⟩ := local_exists_quasisimple_component d h hab structural previous
    faithful earlier I hI
  have hcK := local_component_star_isComponent h hab structural previous faithful I hI K hK
  let : IsQuasisimple (K.map q) := hcK.2
  let : IsSimpleGroup ((K.map q) ⧸ center (K.map q)) := IsQuasisimple.simple
  let : Nontrivial (K.map q) := (QuotientGroup.mk'_surjective (center (K.map q))).nontrivial
  have hKP : ⁅K.map q,pCore 3 (HStar I)⁆ = ⊥ := by
    rcases hcK.normal_dichotomy (pCore 3 (HStar I)) with hp | hc
    · exact (Group.IsPerfect.not_isNilpotent (K.map q) (pCore_isPGroup.to_le hp).isNilpotent).elim
    · exact hc
  have hXsub : (X.subgroupOf I).map q ≤ pCore 3 (HStar I) := by
    have hXN : X.subgroupOf I ≤ N := by
      simpa only [B,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
        subgroupOf_mono I hXB
    exact (map_mono hXN).trans (by rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)])
  have hKcent : K.map q ≤ centralizer ((X.subgroupOf I).map q : Set (HStar I)) := by
    intro k hk x hx
    exact (commutator_eq_bot_iff_le_centralizer.mp hKP) hk x (hXsub hx)
  have hKX : K.map q ≤ normalizer ((X.subgroupOf I).map q : Set (HStar I)) :=
    hKcent.trans (Subgroup.centralizer_le_normalizer _)
  have hXperfect : IsPPerfect 2 (X.subgroupOf I) :=
    (isPPerfect_embedded_pResidual 2 E).of_surjective
      (subgroupOfEquivOfLe hXI).symm.toMonoidHom (subgroupOfEquivOfLe hXI).symm.surjective
  have hQX : q.ker ≤ normalizer (X.subgroupOf I : Set I) := by
    rw [QuotientGroup.ker_mk']
    apply (pCore_isPGroup.le_sylow_of_normal (T.subtype (F.sylow_le_of_mem_Hz hI))).trans
    rw [←subgroupOf_normalizer_eq hXI]
    exact fun x hx => hTX hx
  have hKX' : K ≤ normalizer (X.subgroupOf I : Set I) := by
    rw [←comap_normalizer_map_of_pPerfect q (X.subgroupOf I) hXperfect
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hQX]
    exact map_le_iff_le_comap.mp hKX
  have hKXG : K.map I.subtype ≤ normalizer (X : Set G) := by
    rw [←subgroupOf_normalizer_eq hXI] at hKX'
    rintro _ ⟨k,hk,rfl⟩
    exact hKX' hk
  have hXbot : X = ⊥ := by
    by_contra hn
    exact hout (hKXG.trans (local_twoPerfect_core_commutator_normalizer h structural I hI
      X hXI (isPPerfect_embedded_pResidual 2 E) hn hTX hcomm))
  have hRbot : pResidual 2 E = ⊥ :=
    (map_eq_bot_iff_of_injective _ E.subtype_injective).mp hXbot
  have hE2 : IsPGroup 2 E := (isPGroup_quotient_pResidual 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hRbot).trans QuotientGroup.quotientBot)
  let f := a.comp (inclusion hBM)
  have he : f.ker.map B.subtype = E := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property,⟨inclusion hBM b,hb,rfl⟩⟩
    · rintro ⟨hx,⟨c,hc,he⟩⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      change a (inclusion hBM ⟨x,hx⟩) = 1
      have hh : inclusion hBM ⟨x,hx⟩ = c := Subtype.ext he.symm
      exact hh.symm ▸ hc
  have hk : IsPGroup 2 (f.ker.map B.subtype) := he.symm ▸ hE2
  exact hk.of_equiv (equivMapOfInjective f.ker B.subtype B.subtype_injective).symm

private theorem ThreeCoreKernel_point_quotient_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

/-- The actual three-core has order at most three. Its full preimage's
quotient action has a two-group kernel, and 9 does not divide |Aut(L₃(2))|. -/
theorem local_threeCore_card_le_three
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    Nat.card (pCore 3 (HStar I)) ≤ 3 := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let N := (pCore 3 (HStar I)).comap q
  let B := N.map I.subtype
  have hBM : B ≤ normalizer (L : Set G) :=
    (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
  let f := (normalizerQuotientAction L (pCore 2 L)).comp (inclusion hBM)
  have hk : IsPGroup 2 f.ker :=
    local_threeCore_action_kernel_two d h hab structural previous faithful earlier I hI
  have hdiv : Nat.card (pCore 3 (HStar I)) ∣ Nat.card B := by
    rw [card_map_of_injective I.subtype_injective]
    have hh := card_map_dvd N q
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hh
  have hnine : ¬ 9 ∣ Nat.card B := by
    intro hh
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hh
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn] at hh
    have hcop : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
    have h9 : 9 ∣ Nat.card f.range := hcop.dvd_of_dvd_mul_right hh
    have ha := h9.trans f.range.card_subgroup_dvd_card
    rw [ThreeCoreKernel_point_quotient_aut_card h] at ha
    norm_num at ha
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := HStar I)).exists_card_eq
  have hlt : n < 2 := by
    by_contra hh
    have hp : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    exact hnine ((hn.symm ▸ hp).trans hdiv)
  rw [hn]
  interval_cases n <;> norm_num

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original three-core and odd-core alternatives

The action-kernel argument bounds O₃(I/O₂(I)) by three. If it is
nontrivial, lift it as an actual normal two-perfect cubic. The full
preimage lies in M, so the strict-intersection argument forces L₁ into
this lift. Its nonzero star image exhausts the three-core, proving
14.7.27 with the literal original quotient map.

The odd core is solvable by the odd-order theorem. Its Fitting subgroup
lies in the same three-core. The small-Fitting lemma makes the entire
odd core a three-group, hence it equals the three-core. This proves
14.7.28 without assuming the point normal in I or I solvable.

The proof uses the independently established 14.7.29 and the A.3.6
quasisimplicity reduction; neither depends on these new alternatives.
The component and module classification through 14.7.52 remains.

Source: Aschbacher–Smith, 14.7.27–28, printed pp.1054–1055,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Source 14.7.27 for every original local, with the actual point image. -/
theorem local_threeCore_eq_bot_or_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pCore 3 (HStar I) = ⊥ ∨ pCore 3 (HStar I) =
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let P := pCore 3 (HStar I)
  let q := QuotientGroup.mk' (pCore 2 I)
  let A := (F.Li L 1).subgroupOf I
  by_cases hb : P = ⊥
  · exact Or.inl hb
  right
  have hc : Nat.card P = 3 := by
    have hbound := local_threeCore_card_le_three d h hab structural previous faithful earlier I hI
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := HStar I)).exists_card_eq
    have hnpos : n ≠ 0 := by
      intro he
      apply hb
      apply card_eq_one.mp
      rw [hn,he,pow_zero]
    have hlow : 3 ≤ Nat.card P := by
      rw [hn]
      exact Nat.le_of_dvd (pow_pos (by decide) _) (dvd_pow_self 3 hnpos)
    exact le_antisymm hbound hlow
  obtain ⟨Y,hYn,_,_,hYm,hYk,⟨eY⟩⟩ := exists_normal_three_residual_lift q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    P pCore_isPGroup
  let := hYn
  have hY3 : IsPGroup 3 (Y ⧸ pCore 2 Y) := pCore_isPGroup.of_equiv eY.symm
  have hYc : Nat.card (Y ⧸ pCore 2 Y) = 3 := (Nat.card_congr eY.toEquiv).trans hc
  have hYM : Y.map I.subtype ≤ normalizer (L : Set G) :=
    (map_mono (show Y ≤ P.comap q from map_le_iff_le_comap.mp hYm.le)).trans
      (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
  have hi := local_lift_intersection_of_cubic_sublift h structural I hI Y Y le_rfl hYM hYk hYc
  have hAY := local_three_lift_contains_point h structural I hI Y hY3 hi
  have hAP : A.map q ≤ P := (map_mono hAY).trans hYm.le
  have hAne : A.map q ≠ ⊥ := by
    intro he
    have hAQ : A ≤ pCore 2 I := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp he
    have hA2 : IsPGroup 2 (F.Li L 1) :=
      (pCore_isPGroup.to_le hAQ).of_equiv (subgroupOfEquivOfLe (F.Li_one_le_of_mem_Hz hI))
    have hdiv : 3 ∣ Nat.card (F.Li L 1) := by
      have hd := card_quotient_dvd_card (pCore 2 (F.Li L 1))
      rwa [pointResidual_core_quotient_card h structural] at hd
    obtain ⟨n,hn⟩ := hA2.exists_card_eq
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hn ▸ hdiv)
    norm_num at h32
  have hAc : Nat.card (A.map q) = 3 := by
    have hh := card_dvd_of_le hAP
    rw [hc] at hh
    exact ((Nat.dvd_prime Nat.prime_three).mp hh).resolve_left
      (fun he => hAne (card_eq_one.mp he))
  exact (eq_of_le_of_card_ge hAP (by rw [hc,hAc])).symm

/-- Source 14.7.28: the full odd core is trivial or the literal point cubic. -/
theorem local_oddCore_eq_bot_or_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    pPrimeCore 2 (HStar I) = ⊥ ∨ pPrimeCore 2 (HStar I) =
      ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  have hs : Group.IsSolvable (pPrimeCore 2 (HStar I)) :=
    odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  rw [oddCore_eq_threeCore_of_small_fitting hs
    (local_fitting_eq_threeCore h hab structural previous faithful I hI)
    (local_threeCore_card_le_three d h hab structural previous faithful earlier I hI)]
  exact local_threeCore_eq_bot_or_point d h hab structural previous faithful earlier I hI

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
