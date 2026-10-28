module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourFusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ExtraspecialNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralFour
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.NormalFourCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourOvergroups
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCore
public import CFSG.Quasithin.ChapterC.Section02.NormalCoreSetup
public import Theory.GroupTheory.MaximalTwoLocalCore
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourThree
public import Theory.GroupTheory.HeisenbergNormalizedSubgroups
public import Theory.GroupTheory.PResidual.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.SupplementCommutator
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourThreeCore
public import CFSG.Quasithin.ChapterA.Section01.RankActions.ThreeAutomorphisms
public import Theory.GroupTheory.TwoThreeSubnormalCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourComponents
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCharacteristic
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.ThreeFreeControl
public import CFSG.Quasithin.ChapterC.Section02
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.GroupTheory.CComponent.NormalQuotientActionKernel
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCatalogue
public import Theory.SpecificGroups.HeisenbergPrime.SmallAutomorphismExclusions
public import Theory.SpecificGroups.G2.BinaryHeisenbergExclusion
public import Theory.SpecificGroups.SL2.HeisenbergAutomorphismExclusion
public import Theory.SpecificGroups.SL3.HeisenbergAutomorphismExclusion
public import Theory.SpecificGroups.HeisenbergPrime.BinaryRankTwoExclusions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourOrdinary
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.SuzukiModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ModelThreeDivisibility
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.Solvable

/-!
# Guarded four group structure

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/
/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Sylow control and fusion of the extraspecial central four-group

For the subgroup D selected after 14.7.25, take x in D outside V₁.
Its centralizer in H is exactly C_G(D). This is normal in H and has
characteristic two. Its Sylow subgroup is the literal C_T(x).

The established centrality of Z(O₂(K)) makes K centralize the center of
O₂(C_H(x)), by residual commutator idempotence. Consequently H normalizes
Z(C_T(x)); maximal two-local uniqueness gives its exact normalizer H.
This promotes C_T(x) to Sylow in C_G(x). In the noncentral branch it has
index two in T, separating x from the point conjugacy class. The two
outside involutions form one T-orbit, so H controls fusion in D.

The final application uses the original selected D. It reduces its remaining
TI assertion to containment of the outside involution centralizers; it does
not assume that containment or assert completion of 14.7.26.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed p.1052,
and I.6.1(1), printed p.424.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem ExtraspecialFourFusion_four_sup_point (D Z : Subgroup G) (hD : Nat.card D = 4)
    (hZ : Nat.card Z = 2) (hZD : Z ≤ D) {x : G} (hx : x ∈ D) (hxZ : x ∉ Z) :
    Z ⊔ zpowers x = D := by
  have hle : Z ⊔ zpowers x ≤ D := sup_le hZD (zpowers_le.mpr hx)
  have hlt : Z < Z ⊔ zpowers x := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hxZ (he ▸ (le_sup_right : zpowers x ≤ Z ⊔ zpowers x) (mem_zpowers x)))
  have hh : 2 < Nat.card (Z ⊔ zpowers x : Subgroup G) := by
    by_contra! hh
    exact hlt.ne (eq_of_le_of_card_ge le_sup_left (by rwa [hZ]))
  apply eq_of_le_of_card_ge hle
  have hd := card_dvd_of_le hle
  rw [hD] at hd ⊢
  have heq : 4 = Nat.card (Z ⊔ zpowers x : Subgroup G) :=
    Nat.eq_of_dvd_of_lt_two_mul (by decide : 4 ≠ 0) hd (by omega)
  exact heq.le

private theorem ExtraspecialFourFusion_coreCenter_centralized (J A : Subgroup G)
    (hAJ : A ≤ J) (hJA : J ≤ normalizer (A : Set G)) (hA : IsPPerfect 2 A)
    (hc : (center (A.pCoreIn 2)).map (A.pCoreIn 2).subtype ≤
      centralizer (A : Set G)) :
    (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype ≤ centralizer (A : Set G) := by
  let Q := J.pCoreIn 2
  let P := A.pCoreIn 2
  let Z := (center Q).map Q.subtype
  have hPQ : P ≤ Q := pCoreIn_mono_of_normalizes hAJ hJA
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZC : Z ≤ centralizer (P : Set G) := by
    rw [show Z = Q ⊓ centralizer (Q : Set G) from map_center_subtype_eq_inf_centralizer Q]
    exact inf_le_right.trans (centralizer_le hPQ)
  have hAZ : A ≤ normalizer (Z : Set G) := hAJ.trans
    (J.le_normalizer.trans ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))))
  have hmove : ⁅Z,A⁆ ≤ (center P).map P.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    have hz := le_normalizer_iff_commutator_le_left.mp hAZ
    refine le_inf ?_ (hz.trans hZC)
    apply (le_inf ?_ (hz.trans hZQ)).trans (inf_pCoreIn_le_of_le 2 hAJ)
    exact le_normalizer_iff_commutator_le_right.mp ((hZQ.trans (pCoreIn_le 2 J)).trans hJA)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  rw [← commutator_isPPerfect_idempotent A Z hA ((isPGroup_pCoreIn 2 J).to_le hZQ) hAZ]
  exact (commutator_mono hmove le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr hc).le

variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

private theorem ExtraspecialFourFusion_four_point_centralizer (D Z H : Subgroup G)
    (hD : Nat.card D = 4) (hZ : Nat.card Z = 2) (hZD : Z ≤ D)
    (hHC : H ≤ centralizer (Z : Set G))
    (hCH : centralizer (D : Set G) ≤ H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ Z) :
    H ⊓ centralizer ({x} : Set G) = centralizer (D : Set G) := by
  apply le_antisymm
  · intro a ha
    have hZa : Z ≤ centralizer ({a} : Set G) := by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr (hHC ha.1 z hz)
    have hxa : x ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha.2).symm
    have hDa : D ≤ centralizer ({a} : Set G) := by
      rw [← ExtraspecialFourFusion_four_sup_point D Z hD hZ hZD hx hxZ]
      exact sup_le hZa (zpowers_le.mpr hxa)
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hDa hz)
  · intro a ha
    exact ⟨hCH ha,mem_centralizer_singleton_iff.mpr (ha x hx).symm⟩

/-- The centralizer in H of every nonpoint element of the source four-group
is characteristic two. Its Sylow center has normalizer exactly H, and the
same Sylow subgroup is Sylow in the full element centralizer. -/
theorem extraspecial_four_centralizer_sylow
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    let J := F.H ⊓ centralizer ({x} : Set G)
    let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
    J = centralizer (D : Set G) ∧ J ∈ He G ∧
      normalizer ((center S).map S.subtype : Set G) = F.H ∧
      normalizer (S : Set G) ≤ F.H ∧
      (∃ P : Sylow 2 J, (P : Subgroup J).map J.subtype = S) ∧
      (∃ P : Sylow 2 (centralizer ({x} : Set G)),
        (P : Subgroup (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype = S) := by
  let J := F.H ⊓ centralizer ({x} : Set G)
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  let ZS := (center S).map S.subtype
  obtain ⟨hNK,hHC,hmax,hcore⟩ := extraspecial_source_14721
    d h hab structural previous faithful earlier he
  have hHC' : F.H ≤ centralizer (F.Vi 1 : Set G) := hHC.le
  have hCH : centralizer (D : Set G) ≤ F.H :=
    (Subgroup.centralizer_le_normalizer _).trans hND.le
  have hJ : J = centralizer (D : Set G) := ExtraspecialFourFusion_four_point_centralizer D (F.Vi 1) F.H
    hcard (by simpa using F.card 1 (by decide)) hZD hHC' hCH hx hxZ
  have hS : S = (T : Subgroup G) ⊓ centralizer (D : Set G) := by
    calc
      S = (T : Subgroup G) ⊓ J := by
        dsimp [S,J]
        rw [← inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
      _ = _ := by rw [hJ]
  have hHnD : F.H ≤ normalizer (D : Set G) := hND.ge
  have hHnJ : F.H ≤ normalizer (J : Set G) := by
    rw [hJ]
    exact hHnD.trans (normalizer_le_normalizer_centralizer D)
  have hx1 : x ≠ 1 := fun he => hxZ (he ▸ (F.Vi 1).one_mem)
  have hxJ : x ∈ J := by
    rw [hJ]
    exact D.le_centralizer hx
  have hJne : J ≠ ⊥ := fun he => hx1 (show x ∈ (⊥ : Subgroup G) from he ▸ hxJ)
  have hJHe : J ∈ He G := lemma_1_1_3_1
    (mem_He_iff.mpr (d.qtke.evenCharacteristic T F.H hmax (F.invariant 1)))
    hJne inf_le_left (normal_subgroupOf_of_le_normalizer hHnJ).isSubnormal
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes D
    ((F.invariant 1).trans hHnD)
  have hPS : ∃ P : Sylow 2 J, (P : Subgroup J).map J.subtype = S := by
    rw [hJ,hS]
    exact ⟨P,hP⟩
  have hQS : J.pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := hPS
    exact hP ▸ pCoreIn_le_sylow J P
  have hZSC : ZS ≤ centralizer (S : Set G) := by
    rw [show ZS = S ⊓ centralizer (S : Set G) from map_center_subtype_eq_inf_centralizer S]
    exact inf_le_right
  have hZSJ : ZS ≤ J := (map_subtype_le _).trans
    (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  have hZSQ : ZS ≤ (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf ((le_inf hZSJ (hZSC.trans (centralizer_le hQS))).trans hJHe)
      (hZSC.trans (centralizer_le hQS))
  have hKJ : K F ≤ J := by
    rw [hJ]
    apply le_centralizer_iff.mp
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    exact hDK.trans inf_le_right
  have hKC : K F ≤ centralizer (ZS : Set G) := le_centralizer_iff.mp
    (hZSQ.trans (ExtraspecialFourFusion_coreCenter_centralized J (K F) hKJ
      (inf_le_left.trans (H_normalizes_K F)) (K_twoPerfect F)
      (hcore.trans (by rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_right))))
  have hTnS : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    rw [hS]
    exact (le_inf (T : Subgroup G).le_normalizer
      (((F.invariant 1).trans hHnD).trans (normalizer_le_normalizer_centralizer D))).trans
      inf_normalizer_le_normalizer_inf
  have hHnZS : F.H ≤ normalizer (ZS : Set G) := by
    rw [residual_product F]
    exact sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _))
      (hTnS.trans (normalizer_le_normalizer_characteristic_image S (center S)))
  have hxZS : x ∈ ZS := by
    rw [show ZS = S ⊓ centralizer (S : Set G) from map_center_subtype_eq_inf_centralizer S]
    refine ⟨⟨hDT hx,mem_centralizer_singleton_iff.mpr rfl⟩,?_⟩
    intro s hs
    exact mem_centralizer_singleton_iff.mp hs.2
  have hZSne : ZS ≠ ⊥ := fun he => hx1 (show x ∈ (⊥ : Subgroup G) from he ▸ hxZS)
  have hN : normalizer (ZS : Set G) = F.H := le_antisymm
    (hmax.2 ⟨ZS,hZSne,T.isPGroup'.to_le ((map_subtype_le _).trans inf_le_left),rfl⟩ hHnZS)
    hHnZS
  have hNS : normalizer (S : Set G) ≤ F.H :=
    (normalizer_le_normalizer_characteristic_image S (center S)).trans hN.le
  exact ⟨hJ,hJHe,hN,hNS,hPS,exists_sylow_eq_of_relative_normalizer_le hPS inf_le_right
    (le_inf (inf_le_right.trans hNS) inf_le_left)⟩

private theorem ExtraspecialFourFusion_not_isConj_of_proper_sylow_centralizer
    (T : Sylow 2 G) {x z : G}
    (hx : ¬ (T : Subgroup G) ≤ centralizer ({x} : Set G))
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hs : ∃ P : Sylow 2 (centralizer ({x} : Set G)),
      (P : Subgroup (centralizer ({x} : Set G))).map
        (centralizer ({x} : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer ({x} : Set G)) : ¬ IsConj x z := by
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let f : G ≃* G := MulAut.conj (g : G)
  have hf : f x = z := hg
  have hcard : Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({z} : Set G)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro a
    have hfa : f.toEquiv a = f a := rfl
    rw [hfa]
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul,hf] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul,hf] using ha
  obtain ⟨P,hP⟩ := hs
  have hsz : Nat.card P = Nat.card (T.subtype hz) := by
    rw [P.card_eq_multiplicity,(T.subtype hz).card_eq_multiplicity,hcard]
  have hst : Nat.card ((T : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card T := by
    rw [←hP,card_map_of_injective (centralizer ({x} : Set G)).subtype_injective,hsz]
    exact Nat.card_congr (subgroupOfEquivOfLe hz).toEquiv
  have heq : (T : Subgroup G) ⊓ centralizer ({x} : Set G) = (T : Subgroup G) :=
    eq_of_le_of_card_ge inf_le_left hst.ge
  exact hx (heq ▸ (inf_le_right : (T : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ _))

private theorem ExtraspecialFourFusion_four_outside_orbit (T D Z : Subgroup G)
    (hD : Nat.card D = 4) (hZ : Nat.card Z = 2) (hZD : Z ≤ D)
    (hTD : T ≤ normalizer (D : Set G)) (hTZ : T ≤ normalizer (Z : Set G))
    (x y : G) (hx : x ∈ D) (hxZ : x ∉ Z) (hy : y ∈ D) (hyZ : y ∉ Z)
    (hm : ¬ T ≤ centralizer ({x} : Set G)) :
    ∃ t : T, (t : G) * x * (t : G)⁻¹ = y := by
  classical
  let E := {a : D // (a : G) ∉ Z}
  let : Fintype D := Fintype.ofFinite D
  have hZi : Nat.card {a : D // (a : G) ∈ Z} = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZ
  have hE : Nat.card E = 2 := by
    change Nat.card {a : D // ¬ (a : G) ∈ Z} = 2
    simp only [Nat.card_eq_fintype_card] at hD hZi ⊢
    rw [Fintype.card_subtype_compl,hD,hZi]
  let a : E := ⟨⟨x,hx⟩,hxZ⟩
  let b : E := ⟨⟨y,hy⟩,hyZ⟩
  obtain ⟨t,ht,htc⟩ := SetLike.not_le_iff_exists.mp hm
  have hmove : t * x * t⁻¹ ≠ x := fun he => htc
    (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he))
  let c : E := ⟨⟨t*x*t⁻¹,(mem_normalizer_iff.mp (hTD ht) x).mp hx⟩,
    fun he => hxZ ((mem_normalizer_iff.mp (hTZ ht) x).mpr he)⟩
  have hca : c ≠ a := fun he => hmove (congrArg (fun e : E => ((e : D) : G)) he)
  by_cases hba : b = a
  · refine ⟨1,?_⟩
    simpa only [OneMemClass.coe_one,mul_one,one_mul,inv_one] using
      (show x = y from (congrArg (fun e : E => ((e : D) : G)) hba).symm)
  obtain ⟨r,_,hr⟩ := (Nat.card_eq_two_iff' a).mp hE
  have hcb : c = b := (hr c hca).trans (hr b hba).symm
  exact ⟨⟨t,ht⟩,congrArg (fun e : E => ((e : D) : G)) hcb⟩

/-- The original H controls fusion in the noncentral elementary four-group.
The two outside involutions form one T-orbit, disjoint from the point class. -/
theorem extraspecial_four_controls_fusion
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G)) :
    (∀ x ∈ D, x ∉ F.Vi 1 → ∀ z ∈ F.Vi 1, ¬ IsConj x z) ∧
    (∀ x y : G, x ∈ D → y ∈ D → IsConj x y →
      ∃ m : F.H, (m : G) * x * (m : G)⁻¹ = y) := by
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hHC : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    (extraspecial_source_14721 d h hab structural previous faithful earlier he).2.1.le
  have hm (x : G) (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
      ¬ (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro htx
    apply hnc
    apply le_centralizer_iff.mp
    have hC := ExtraspecialFourFusion_four_point_centralizer D (F.Vi 1) F.H hcard hZcard hZD hHC
      ((Subgroup.centralizer_le_normalizer _).trans hND.le) hx hxZ
    exact (le_inf (F.invariant 1) htx).trans hC.le
  have hn (x : G) (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) (z : G) (hz : z ∈ F.Vi 1) :
      ¬ IsConj x z := by
    apply ExtraspecialFourFusion_not_isConj_of_proper_sylow_centralizer T (hm x hx hxZ) ?_
      (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hHC (F.invariant 1 ht) z hz).symm
  refine ⟨hn,?_⟩
  intro x y hx hy hxy
  by_cases hxZ : x ∈ F.Vi 1
  · have hyZ : y ∈ F.Vi 1 := by
      by_contra hyZ
      exact hn y hy hyZ x hxZ hxy.symm
    have heq : x = y := by
      by_cases hx1 : x = 1
      · exact hx1.trans ((isConj_one_right.mp (hx1 ▸ hxy)).symm)
      have hy1 : y ≠ 1 := fun hy1 => hx1 (isConj_one_left.mp (hy1 ▸ hxy))
      obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hZcard
      exact congrArg Subtype.val ((hz ⟨x,hxZ⟩ (fun hh => hx1 (congrArg Subtype.val hh))).trans
        (hz ⟨y,hyZ⟩ (fun hh => hy1 (congrArg Subtype.val hh))).symm)
    exact ⟨1,by simpa using heq⟩
  · have hyZ : y ∉ F.Vi 1 := fun hyZ => hn x hx hxZ y hyZ hxy
    obtain ⟨t,ht⟩ := ExtraspecialFourFusion_four_outside_orbit (T : Subgroup G) D (F.Vi 1) hcard hZcard hZD
      ((F.invariant 1).trans hND.ge) (F.invariant 1) x y hx hxZ hy hyZ (hm x hx hxZ)
    exact ⟨⟨t,F.invariant 1 t.property⟩,ht⟩

private theorem ExtraspecialFourFusion_four_centralizer_index (T D : Subgroup G) [IsElementaryAbelian 2 D]
    (hT : IsPGroup 2 T) (hDT : D ≤ T) (hn : T ≤ normalizer (D : Set G))
    (hD : Nat.card D = 4) (hnc : ¬ D ≤ centralizer (T : Set G)) :
    (T ⊓ centralizer (D : Set G)).relIndex T = 2 := by
  let E := D.subgroupOf T
  let : E.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hDT
  have he : Nat.card E = 4 := (Nat.card_congr (subgroupOfEquivOfLe hDT).toEquiv).trans hD
  have hc : centralizer (E : Set T) = (centralizer (D : Set G)).subgroupOf T := by
    ext t
    constructor
    · intro ht x hx
      exact congrArg Subtype.val (ht ⟨x,hDT hx⟩ hx)
    · intro ht x hx
      exact Subtype.ext (ht x hx)
  have hb := centralizer_index_le_two_of_normal_four hT E he
  rw [hc] at hb
  have hne : (centralizer (D : Set G)).relIndex T ≠ 1 := fun hi =>
    hnc (le_centralizer_iff.mp (relIndex_eq_one.mp hi))
  have hz := ((centralizer (D : Set G)).subgroupOf T).index_ne_zero_of_finite
  rw [inf_relIndex_left]
  change ((centralizer (D : Set G)).subgroupOf T).index = 2
  change ((centralizer (D : Set G)).subgroupOf T).index ≠ 1 at hne
  omega

/-- The source outside centralizer has index two in the original T. -/
theorem extraspecial_four_centralizer_index
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    ((T : Subgroup G) ⊓ centralizer ({x} : Set G)).relIndex (T : Subgroup G) = 2 := by
  have hHC : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hj := ExtraspecialFourFusion_four_point_centralizer D (F.Vi 1) F.H hcard
    (by simpa using F.card 1 (by decide)) hZD hHC
    ((Subgroup.centralizer_le_normalizer _).trans hND.le) hx hxZ
  have heq : (T : Subgroup G) ⊓ centralizer ({x} : Set G) =
      (T : Subgroup G) ⊓ centralizer (D : Set G) := by
    rw [←hj,←inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
  rw [heq]
  exact ExtraspecialFourFusion_four_centralizer_index (T : Subgroup G) D T.isPGroup' hDT
    ((F.invariant 1).trans hND.ge) hcard hnc

/-- After the original Sylow and fusion deductions, precisely the outside
involution centralizers remain to prove the TI assertion of 14.7.26. -/
theorem extraspecial_four_ti_iff_centralizer_containment
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G)) :
    IsTISubgroup D ↔
      ∀ x ∈ D, x ∉ F.Vi 1 → centralizer ({x} : Set G) ≤ F.H := by
  constructor
  · intro ht x hx hxZ
    exact (ht.centralizer_le_normalizer hx (fun he => hxZ (he ▸ (F.Vi 1).one_mem))).trans hND.le
  · intro hc
    apply lemma_I_6_1_1 D F.H hND.symm ?_ ?_
    · intro x hx hx1
      by_cases hxZ : x ∈ F.Vi 1
      · have hcardZ : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
        have hz : zpowers x = F.Vi 1 := by
          have heq := congrArg (fun A : Subgroup (F.Vi 1) => A.map (F.Vi 1).subtype)
            (zpowers_eq_top_of_prime_card hcardZ
              (show (⟨x,hxZ⟩ : F.Vi 1) ≠ 1 from fun he => hx1 (congrArg Subtype.val he)))
          simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.coe_subtype] using heq
        have hC : centralizer ({x} : Set G) = centralizer (F.Vi 1 : Set G) := by
          rw [←hz,zpowers_eq_closure,centralizer_closure]
        rw [hC]
        exact Subgroup.centralizer_le_normalizer _
      · exact hc x hx hxZ
    · intro x y hx hy hconj
      exact (extraspecial_four_controls_fusion d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hnc).2 x y hx hy (isConj_iff.mpr hconj)

/-- Apply the noncentral four-group reductions to the subgroup selected from
14.7.25, without any additional local recognition premise. The remaining
centralizer-containment assertion is exposed as an equivalence, not assumed. -/
theorem extraspecial_center_four_fusion_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧ ⁅D,(T : Subgroup G)⁆ = F.Vi 1 ∧
        (∀ x ∈ D, x ∉ F.Vi 1 →
          let J := F.H ⊓ centralizer ({x} : Set G)
          let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
          J = centralizer (D : Set G) ∧ J ∈ He G ∧
            S.relIndex (T : Subgroup G) = 2 ∧
            normalizer ((center S).map S.subtype : Set G) = F.H ∧
            normalizer (S : Set G) ≤ F.H ∧
            ∃ P : Sylow 2 (centralizer ({x} : Set G)),
              (P : Subgroup (centralizer ({x} : Set G))).map
                (centralizer ({x} : Set G)).subtype = S) ∧
        (∀ x y : G, x ∈ D → y ∈ D → IsConj x y →
          ∃ m : F.H, (m : G) * x * (m : G)⁻¹ = y) ∧
        (IsTISubgroup D ↔ ∀ x ∈ D, x ∉ F.Vi 1 → centralizer ({x} : Set G) ≤ F.H))) := by
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,hcomm,hnc⟩
  · exact Or.inl ht
  let := hele
  refine Or.inr ⟨hele,hcomm,?_,?_,?_⟩
  · intro x hx hxZ
    obtain ⟨hJ,hHe,hZ,hS,_,hP⟩ := extraspecial_four_centralizer_sylow
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    exact ⟨hJ,hHe,extraspecial_four_centralizer_index D hZD hcard hDT hND hnc hx hxZ,hZ,hS,hP⟩
  · exact (extraspecial_four_controls_fusion d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc).2
  · exact extraspecial_four_ti_iff_centralizer_containment d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Reduction of the outside involution centralizers

An outside centralizer escaping H cannot act irreducibly through its actual
Sylow subgroup on K/O₂(K) modulo Frattini. The complete intrinsic Ξ embedding
theorem would make K normal there: all its nonnormal alternatives, including
the Held alternative, require a complement of order nine, whereas the marked
Heisenberg complement has order 27. The proved N_G(K) = H then contradicts
escape. Thus the original action has a proper nontrivial invariant subgroup.

The same centralizer is SQTK for the full known-simple class and satisfies
1.1.5 with the original point involution and literal Sylow inclusion. Its
point-residual normalizer is exactly its intersection with H. The final
application chooses an actual escaping centralizer whenever the original
selected four-group is not TI, retaining both the invariant subgroup and
these genuine earlier-source hypotheses.

The reducible overgroup analysis and the TI conclusion of 14.7.26 remain
open, as do the subsequent extraspecial exclusion and 14.7.52 assembly.
Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.1052–1053;
1.1.6, p.503, and 1.3.4, pp.509–511.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- If an outside involution centralizer escapes H, its actual Sylow
centralizer acts reducibly on the marked extraspecial Frattini quotient.
The full intrinsic embedding theorem excludes every irreducible alternative,
including the Held alternative, by the actual complement order 27. -/
theorem extraspecial_four_frattini_reducible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H) :
    let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
    let hn : S ≤ normalizer (K F : Set G) :=
      inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))
    ∃ A : Subgroup (XiFrattiniQuotient (K F)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A := by
  classical
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  let C := centralizer ({x} : Set G)
  have hn : S ≤ normalizer (K F : Set G) :=
    inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))
  change ∃ A : Subgroup (XiFrattiniQuotient (K F)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
    ∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A
  by_contra hnot
  have hirr : ∀ A : Subgroup (XiFrattiniQuotient (K F)),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A) → A = ⊥ ∨ A = ⊤ := by
    intro A hA
    by_contra! ha
    exact hnot ⟨A,ha.1,ha.2,hA⟩
  have hDK' : D ≤ K F := hDK.trans (map_subtype_le _)
  have hDcentral : D ≤ centralizer (K F : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    exact hDK.trans inf_le_right
  have hKC : K F ≤ C := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDcentral hx) k hk)
  have hgenC : K F ⊔ S ≤ C := sup_le hKC inf_le_right
  have hgenH : K F ⊔ S ≤ F.H := sup_le (K_le_H F) (inf_le_left.trans (F.invariant 1))
  have hDcore : D ≤ (K F ⊔ S).pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 D) (hDK'.trans le_sup_left) (hgenH.trans hND.ge)
  have hjoin : K F ⊔ S ∈ H G := by
    intro hc
    have hh : D = ⊥ := le_antisymm (hc ▸ hDcore) bot_le
    simp only [hh, Subgroup.card_bot] at hcard
    omega
  obtain ⟨e⟩ := he
  have hq : XiOddQuotient 3 (XiQuotient (K F)) := Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩
  have hX : K F ∈ Xi G S := ⟨K_twoPerfect F,hn,hjoin,⟨3,by decide,by decide,hq⟩,hirr⟩
  have hS : IsSylowIn 2 S C :=
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier ⟨e⟩
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
  have hxorder : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx)
    (fun hx1 => hxZ (hx1 ▸ (F.Vi 1).one_mem))
  let b := XiEmbedding.localInput_of_mem_Xi hX hS hgenC
    (by decide : Odd 3) hq (default : Sylow 3 (K F))
  rcases b.adequate_knownSimple (d.qtke.involution_centralizer_sqtk hxorder) hS with
    hnormal | ⟨J,_,_,_,ha⟩
  · have hN : C ≤ normalizer (K F : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hKC).mp hnormal
    exact hout (hN.trans (extraspecial_normalizer_eq_H d h hab structural previous faithful earlier ⟨e⟩).1.le)
  · have hplane : Nonempty (((default : Sylow 3 (K F)) : Subgroup (K F)).map (K F).subtype ≃*
        XiEmbedding.Plane 3) := by
      rcases ha with ha | ha
      · exact ha.1
      · exact ha.2.1
    obtain ⟨ep⟩ := hplane
    have h27 : Nat.card (((default : Sylow 3 (K F)) : Subgroup (K F)).map (K F).subtype) = 27 :=
      (Nat.card_congr b.complementQuotientEquiv.toEquiv).trans
        ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    have h9 := (Nat.card_congr ep.toEquiv).trans (XiEmbedding.plane_card 3)
    omega

/-- The outside centralizer has the full known-simple local hypothesis and
satisfies the original 1.1.5 hypotheses with the literal source point. -/
theorem extraspecial_four_centralizer_source_setup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    let C := centralizer ({x} : Set G)
    IsSQTK KnownSimple.IsKnownSimple C ∧
      C ⊓ normalizer (F.Li L 1 : Set G) = F.H ⊓ C ∧
      ∃ z : G, orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
        ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C ∧
          Lemma115Hypotheses C P F.H z := by
  let C := centralizer ({x} : Set G)
  have hx1 : x ≠ 1 := fun he => hxZ (he ▸ (F.Vi 1).one_mem)
  have hxo : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx) hx1
  obtain ⟨hNK,hHC,hmax,_⟩ := extraspecial_source_14721 d h hab structural previous faithful earlier he
  have hNpoint : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans hNK
  refine ⟨d.qtke.involution_centralizer_sqtk hxo,?_,?_⟩
  · rw [hNpoint,inf_comm]
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z,hz1,_⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hZcard
  have hzne : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hzo : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) (z : G) (hZD z.property)) hzne
  have hzpow : zpowers (z : G) = F.Vi 1 := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    rw [Nat.card_zpowers,hzo,hZcard]
  have hzC : centralizer ({(z : G)} : Set G) = F.H := calc
    centralizer ({(z : G)} : Set G) = centralizer (zpowers (z : G) : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
    _ = centralizer (F.Vi 1 : Set G) :=
      congrArg (fun A : Subgroup G => centralizer (A : Set G)) hzpow
    _ = F.H := hHC.symm
  obtain ⟨P,hP⟩ := (extraspecial_four_centralizer_sylow
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
  refine ⟨z,hzo,hzpow,P,hP,?_⟩
  have hB : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hxo]; decide)
  have hBC : zpowers x ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCC : centralizer (zpowers x : Set G) = C := by
    rw [zpowers_eq_closure,centralizer_closure]
  apply lemma_1_1_6 (B := zpowers x)
    (fun hb => hx1 (zpowers_eq_bot.mp hb)) hB hBC hCC.le
    (hCC ▸ Subgroup.centralizer_le_normalizer (zpowers x : Set G)) P T
    (hP ▸ inf_le_left) hzo (hDT (hZD z.property)) ?_ hmax hzC.le
    (fun N hN hTN => mem_He_iff.mpr (d.qtke.evenCharacteristic T N hN hTN))
  intro t ht
  exact ((normalizer_le_centralizer_of_card_two (F.Vi 1) hZcard)
    (F.invariant 1 ht) z z.property).symm

/-- A selected non-TI four-group supplies an actual escaping involution
centralizer and a proper invariant subgroup of the original Frattini section.
This is the reducible branch of the remaining 14.7.26 analysis. -/
theorem extraspecial_center_four_escaping_reducible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧
        ∃ x ∈ D, x ∉ F.Vi 1 ∧ ¬ centralizer ({x} : Set G) ≤ F.H ∧
          let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
          let hn : S ≤ normalizer (K F : Set G) :=
            inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))
          (∃ A : Subgroup (XiFrattiniQuotient (K F)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
            ∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A) ∧
          (∃ z : G, orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
            ∃ P : Sylow 2 (centralizer ({x} : Set G)),
              (P : Subgroup (centralizer ({x} : Set G))).map
                (centralizer ({x} : Set G)).subtype = S ∧
              Lemma115Hypotheses (centralizer ({x} : Set G)) P F.H z))) := by
  classical
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,_,hnc⟩
  · exact Or.inl ht
  let := hele
  by_cases ht : IsTISubgroup D
  · exact Or.inl ht
  have hout := (extraspecial_four_ti_iff_centralizer_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc).not.mp ht
  push Not at hout
  obtain ⟨x,hx,hxZ,hout⟩ := hout
  exact Or.inr ⟨hele,x,hx,hxZ,hout,
    extraspecial_four_frattini_reducible d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ hout,
    (extraspecial_four_centralizer_source_setup d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The original core in an escaping four-group centralizer

Let x lie outside V₁ in the selected elementary central four-group D.
If C_G(x) escapes H, its literal Sylow subgroup S = C_T(x) has index two
in T and acts reducibly on the original extraspecial Frattini quotient.
O₂(H) acts trivially on that quotient. Since T acts irreducibly, the
stabilizer of a proper invariant subgroup is exactly S; hence O₂(H) ≤ S.
This uses the established T-action directly, retaining the original
quotient kernel and avoiding any new R₁-action premise.

The normal intersection J = H ∩ C_G(x) consequently has O₂(J) = O₂(H).
Maximality of H identifies both N_G(O₂(H)) and C(G,O₂(H)) with H. For
every J ≤ G₀ ≤ C_G(x), restriction and the literal product J = KS
construct all of C.2.3, including radicality and the Sylow condition in
the normal closure. Strict overgroups have nontrivial two-core contained
in O₂(H), and L₁ is not normal in any of them.

Separately, the original U = [U,K] and A.1.26 centralize the odd core of
C_G(x). The same original 1.1.5 data makes its intersection with H trivial,
so that odd core vanishes. The last theorem applies these deductions to
the actual D selected from 14.7.25. The three-core and component analysis
of the overgroups, the TI conclusion and the extraspecial exclusion remain
open; no local recognition conclusion is assumed here.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed pp.1052–1053;
C.2.3, p.144; A.1.26(1), pp.25–26; 1.1.5(1–2), pp.501–502.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source Chapter1
open ChapterI.Section06To08
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourCore_frattini_action_core_trivial
    (hn : (T : Subgroup G) ≤ normalizer (K F : Set G))
    (t : T) (ht : (t : G) ∈ F.H.pCoreIn 2)
    (a : XiFrattiniQuotient (K F)) :
    xiFrattiniAction (T : Subgroup G) (K F) hn t a = a := by
  have htcore : (⟨t,F.invariant 1 t.property⟩ : F.H) ∈ pCore 2 F.H := by
    obtain ⟨q,hq,heq⟩ := ht
    exact (show q = ⟨t,F.invariant 1 t.property⟩ from Subtype.ext heq) ▸ hq
  have htz : starMap F ⟨t,F.invariant 1 t.property⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr htcore
  induction a using QuotientGroup.induction_on with | H a =>
    induction a using QuotientGroup.induction_on with | H k =>
      change xiFrattiniAction (T : Subgroup G) (K F) hn t
        (QuotientGroup.mk' _ (QuotientGroup.mk' _ k)) = _
      simp only [xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
      apply congrArg (QuotientGroup.mk' _)
      apply (residualStarEquiv F).injective
      apply Subtype.ext
      change _ = (residualStarEquiv F (QuotientGroup.mk' (pCore 2 (K F)) k) : HStar F.H)
      erw [residualStarEquiv_mk,residualStarEquiv_mk]
      change starMap F
        ((⟨t,F.invariant 1 t.property⟩ : F.H) * ⟨k,K_le_H F k.property⟩ *
          (⟨t,F.invariant 1 t.property⟩ : F.H)⁻¹) = _
      simp only [map_mul,map_inv,htz,one_mul,inv_one,mul_one]

private theorem ExtraspecialFourCore_kernel_le_index_two_of_reducible
    {A E : Type*} [Group A] [Finite A] [Group E]
    (α : A →* MulAut E) (S : Subgroup A) (hi : S.index = 2)
    (hirr : ∀ B : Subgroup E,
      (∀ a : A, ∀ b ∈ B, α a b ∈ B) → B = ⊥ ∨ B = ⊤)
    (B : Subgroup E) (hb : B ≠ ⊥) (ht : B ≠ ⊤)
    (hs : ∀ s : S, ∀ b ∈ B, α s b ∈ B) : α.ker ≤ S := by
  let C := (MulAction.stabilizer (MulAut E) B).comap α
  have hSC : S ≤ C := by
    intro s hs'
    change α s • B = B
    change B.map (α s).toMonoidHom = B
    apply le_antisymm
    · rintro _ ⟨b,hb',rfl⟩
      exact hs ⟨s,hs'⟩ b hb'
    · intro b hb'
      refine ⟨α s⁻¹ b,hs ⟨s⁻¹,S.inv_mem hs'⟩ b hb',?_⟩
      change (α s * α s⁻¹) b = b
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
  have hC : C ≠ ⊤ := by
    intro he
    apply (hirr B ?_).elim hb ht
    intro a b hb'
    have ha : a ∈ C := he ▸ mem_top a
    have hae : B.map (α a).toMonoidHom = B := ha
    exact hae ▸ mem_map_of_mem (α a).toMonoidHom hb'
  have hindex : C.index ≠ 1 := fun he => hC (index_eq_one.mp he)
  have hm : S.relIndex C * C.index = 2 := by rw [relIndex_mul_index hSC,hi]
  have hr : S.relIndex C = 1 := by
    have hd : C.index ∣ 2 := ⟨S.relIndex C,by simpa only [Nat.mul_comm] using hm.symm⟩
    have htwo : C.index = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hindex
    rw [htwo] at hm
    omega
  have hCS : C ≤ S := relIndex_eq_one.mp hr
  intro a ha
  apply hCS
  change α a • B = B
  rw [show α a = 1 from ha,one_smul]

/-- Reducibility at the literal outside Sylow centralizer places the full
original two-core in that centralizer. -/
theorem extraspecial_four_core_le_sylow
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H) :
    F.H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer ({x} : Set G) := by
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  let hn := (F.invariant 1).trans (H_normalizes_K F)
  let α := xiFrattiniAction (T : Subgroup G) (K F) hn
  obtain ⟨A,hAb,hAt,hAs⟩ := extraspecial_four_frattini_reducible
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ hout
  have hi : (S.subgroupOf (T : Subgroup G)).index = 2 :=
    extraspecial_four_centralizer_index D hZD hcard hDT hND hnc hx hxZ
  have hirr := (extraspecial_residual_mem_Xi h hab structural previous faithful he).irreducible
  have hk : α.ker ≤ S.subgroupOf (T : Subgroup G) :=
    ExtraspecialFourCore_kernel_le_index_two_of_reducible α _ hi hirr A hAb hAt (by
      intro s a ha
      exact hAs ⟨s,s.property⟩ a ha)
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
      using pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
  intro q hq
  apply hk (x := ⟨q,hQT hq⟩)
  change α ⟨q,hQT hq⟩ = 1
  ext a
  exact ExtraspecialFourCore_frattini_action_core_trivial hn ⟨q,hQT hq⟩ hq a

/-- The intersection in the original outside centralizer has exactly O₂(H).
The normalizer of that core, and its characteristic-normalizer closure,
are the original maximal two-local H. -/
theorem extraspecial_four_core_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H) :
    (F.H ⊓ centralizer ({x} : Set G)).pCoreIn 2 = F.H.pCoreIn 2 ∧
      normalizer (F.H.pCoreIn 2 : Set G) = F.H ∧
      (F.H.pCoreIn 2).characteristicNormalizerClosure = F.H := by
  have hQ := extraspecial_four_core_le_sylow d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout
  have hJ := (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hx hxZ).1
  have hn : F.H ≤ normalizer ((F.H ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) := by
    rw [hJ]
    exact hND.ge.trans (normalizer_le_normalizer_centralizer D)
  have hmax := (extraspecial_source_14721 d h hab structural previous faithful earlier he).2.2.1
  have hN := maximalTwoLocal_normalizer_core hmax
  refine ⟨le_antisymm (pCoreIn_mono_of_normalizes inf_le_left hn) ?_,hN,
    maximalTwoLocal_characteristicNormalizer_core hmax⟩
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 F.H)
    (le_inf (pCoreIn_le 2 F.H) (hQ.trans inf_le_right)) (inf_le_left.trans hN.ge)

/-- The literal intersection H ∩ C_G(x) is generated by K and C_T(x). -/
private theorem ExtraspecialFourCore_four_intersection_product {D : Subgroup G}
    (hDK : D ≤ (center (K F)).map (K F).subtype) {x : G} (hx : x ∈ D) :
    K F ⊔ ((T : Subgroup G) ⊓ centralizer ({x} : Set G)) =
      F.H ⊓ centralizer ({x} : Set G) := by
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  apply le_antisymm
  · exact sup_le (le_inf (K_le_H F) hKC)
      (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  · rintro y ⟨hyH,hyC⟩
    rw [residual_product F] at hyH
    have hm : y ∈ (K F : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (K F) (T : Subgroup G)
        ((F.invariant 1).trans (H_normalizes_K F))]
      exact hyH
    obtain ⟨k,hk,t,ht,rfl⟩ := hm
    have htC := (centralizer ({x} : Set G)).mul_mem
      ((centralizer ({x} : Set G)).inv_mem (hKC hk)) hyC
    rw [inv_mul_cancel_left] at htC
    exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨ht,htC⟩)

/-- Every actual overgroup of H ∩ C_G(x) in C_G(x) satisfies C.2.3 with
the original O₂(H), its exact normalizer and characteristic-normalizer closure. -/
theorem extraspecial_four_overgroup_pushingUp_setup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G)) :
    normalizer ((F.H.pCoreIn 2).subgroupOf G₀ : Set G₀) =
        (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀ ∧
      ((F.H.pCoreIn 2).subgroupOf G₀).characteristicNormalizerClosure =
        (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀ ∧
      RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
        (F.H ⊓ centralizer ({x} : Set G)) := by
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  let Q := F.H.pCoreIn 2
  have hQ := extraspecial_four_core_le_sylow d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout
  obtain ⟨hcore,hN,hchar⟩ := extraspecial_four_core_eq d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout
  have hQJ : Q ≤ J := le_inf (pCoreIn_le 2 F.H) (hQ.trans inf_le_right)
  have hQG : Q ≤ G₀ := hQJ.trans hJG
  have hmax := (extraspecial_source_14721 d h hab structural previous faithful earlier he).2.2.1
  have hQne : Q ≠ ⊥ := maximalTwoLocal_core_ne_bot hmax
  have hQne₀ : Q.subgroupOf G₀ ≠ ⊥ := by
    intro heq
    apply hQne
    simpa only [map_subgroupOf_eq_of_le hQG,Subgroup.map_bot] using
      congrArg (map G₀.subtype) heq
  have hHJ : F.H.subgroupOf G₀ = J.subgroupOf G₀ := by
    ext g
    exact ⟨fun hg => ⟨hg,hGC g.property⟩,fun hg => hg.1⟩
  have hN₀ : normalizer (Q.subgroupOf G₀ : Set G₀) = J.subgroupOf G₀ := by
    rw [←subgroupOf_normalizer_eq hQG,hN,hHJ]
  have hchar₀ : (Q.subgroupOf G₀).characteristicNormalizerClosure = J.subgroupOf G₀ := by
    apply le_antisymm
    · rw [←hHJ]
      exact characteristicNormalizerClosure_subgroupOf_le hQG hchar.le
    · rw [←hN₀]
      exact normalizer_le_characteristicNormalizerClosure_self _ hQne₀
  refine ⟨hN₀,hchar₀,?_⟩
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp (hC.subgroup (G₀.subgroupOf C))
  have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ :=
    IsSylowIn.restrict (H := C)
      (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
      ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG) hGC
  obtain ⟨P,hP⟩ := hS
  have hprod := ExtraspecialFourCore_four_intersection_product hDK hx
  apply ChapterC.pushingUpSetup_of_normal_core P hG
    (X := K F) (le_sup_left.trans hprod.le) hJG
    (inf_le_left.trans (H_normalizes_K F)) (K_twoPerfect F)
  · rw [hP]
    exact le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right
  · rw [hP,hprod]
    exact hcore.symm
  · exact hQne
  · exact hchar₀.le


/-- The original commutator module centralizes the full odd core of the
outside involution centralizer. The same 1.1.5 data then kills that core. -/
theorem extraspecial_four_oddCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) : pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ := by
  let C := centralizer ({x} : Set G)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨hC,_,z,hzo,hzpow,P,hP,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hUC : F.U ≤ C := ((span_le_residual_core h hab).trans (pCoreIn_le 2 (K F))).trans hKC
  let : IsElementaryAbelian 2 (F.U.subgroupOf C) := IsElementaryAbelian.subgroupOf hUC
  have hp : IsPPerfect 2 ((K F).subgroupOf C) := (K_twoPerfect F).of_surjective
    (subgroupOfEquivOfLe hKC).symm.toMonoidHom (subgroupOfEquivOfLe hKC).symm.surjective
  have hcomm : ⁅F.U.subgroupOf C,(K F).subgroupOf C⁆ = F.U.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUC,map_subgroupOf_eq_of_le hKC,commutator_U h F]
  have hcent := commutator_eq_bot_iff_le_centralizer.mp
    (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hC.stronglyQuasithin
      ((K F).subgroupOf C) (F.U.subgroupOf C) hp hcomm)
  have hzU : z ∈ F.U := ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (hzpow ▸ mem_zpowers z)
  have hzC : z ∈ C := hUC hzU
  apply bot_unique
  intro r hr
  have hcentral : z * (r : G) = (r : G) * z :=
    (congrArg Subtype.val (hcent (show (⟨z,hzC⟩ : C) ∈ F.U.subgroupOf C from hzU) r hr)).symm
  have hrH : (r : G) ∈ F.H := h115.centralizer_le
    (mem_centralizer_singleton_iff.mpr hcentral.symm)
  have hr0 : (⟨r,hrH⟩ : F.H.subgroupOf C) ∈
      (pPrimeCore 2 C).subgroupOf (F.H.subgroupOf C) := hr
  rw [h115.oddCore_intersection_eq_bot] at hr0
  exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hr0))


/-- A strict overgroup has nontrivial two-core contained in the original
O₂(H), and its original point residual is not normal. -/
theorem extraspecial_four_strict_overgroup_geometry
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G)) :
    G₀ ∈ H G ∧ G₀.pCoreIn 2 ≤ F.H.pCoreIn 2 ∧
      G₀ ⊓ normalizer (F.Li L 1 : Set G) = F.H ⊓ centralizer ({x} : Set G) ∧
      ¬ ((F.Li L 1).subgroupOf G₀).Normal := by
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  have hxJ : x ∈ J := ⟨K_le_H F ((hDK.trans (map_subtype_le _)) hx),
    mem_centralizer_singleton_iff.mpr rfl⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx)
    (fun hx1 => hxZ (hx1 ▸ (F.Vi 1).one_mem))
  have hXQ : zpowers x ≤ G₀.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hxo]; decide))
    (zpowers_le.mpr (hJG.le hxJ)) (hGC.trans (by
      simpa only [zpowers_eq_closure,centralizer_closure] using
        Subgroup.centralizer_le_normalizer (zpowers x : Set G)))
  have hG : G₀ ∈ H G := by
    intro hbot
    have hx1 := mem_bot.mp (hbot ▸ hXQ (mem_zpowers x))
    simp [hx1] at hxo
  have hcore := (extraspecial_four_core_eq d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout).1
  have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ := IsSylowIn.restrict (H := C)
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
  obtain ⟨P,hP⟩ := hS
  have hcoreS : G₀.pCoreIn 2 ≤ (T : Subgroup G) ⊓ C := hP ▸ pCoreIn_le_sylow G₀ P
  have hcoreJ : G₀.pCoreIn 2 ≤ J := hcoreS.trans
    (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  have hcoreQ : G₀.pCoreIn 2 ≤ F.H.pCoreIn 2 := hcore ▸
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 G₀) hcoreJ
      (hJG.le.trans (G₀.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image G₀ (pCore 2 G₀))))
  have hL : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans
      (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have hN : G₀ ⊓ normalizer (F.Li L 1 : Set G) = J := by
    rw [hL]
    exact le_antisymm (le_inf inf_le_right (inf_le_left.trans hGC)) (le_inf hJG.le inf_le_left)
  refine ⟨hG,hcoreQ,hN,?_⟩
  have hLG : F.Li L 1 ≤ G₀ := (pointResidual_le F).trans
    ((le_sup_left.trans (ExtraspecialFourCore_four_intersection_product hDK hx).le).trans hJG.le)
  intro hn
  have hGN := (normal_subgroupOf_iff_le_normalizer hLG).mp hn
  have hGJ : G₀ ≤ J := hN ▸ le_inf le_rfl hGN
  exact hJG.not_ge hGJ


/-- Apply the full core and C.2.3 reductions to the four-group selected from
14.7.25. Every extra input comes from the original group and flag. -/
theorem extraspecial_center_four_core_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧
        ∃ x ∈ D, x ∉ F.Vi 1 ∧ ¬ centralizer ({x} : Set G) ≤ F.H ∧
          pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥ ∧
          F.H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
          (F.H ⊓ centralizer ({x} : Set G)).pCoreIn 2 = F.H.pCoreIn 2 ∧
          ∀ G₀ : Subgroup G, F.H ⊓ centralizer ({x} : Set G) < G₀ →
            G₀ ≤ centralizer ({x} : Set G) →
            RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
              (F.H ⊓ centralizer ({x} : Set G)) ∧
            G₀ ∈ H G ∧ G₀.pCoreIn 2 ≤ F.H.pCoreIn 2 ∧
              G₀ ⊓ normalizer (F.Li L 1 : Set G) = F.H ⊓ centralizer ({x} : Set G) ∧
              ¬ ((F.Li L 1).subgroupOf G₀).Normal)) := by
  classical
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,_,hnc⟩
  · exact Or.inl ht
  let := hele
  by_cases ht : IsTISubgroup D
  · exact Or.inl ht
  have hout := (extraspecial_four_ti_iff_centralizer_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc).not.mp ht
  push Not at hout
  obtain ⟨x,hx,hxZ,hout⟩ := hout
  refine Or.inr ⟨hele,x,hx,hxZ,hout,
    extraspecial_four_oddCore_eq_bot d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ,
    extraspecial_four_core_le_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout,
    (extraspecial_four_core_eq d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout).1,?_⟩
  intro G₀ hJG hGC
  exact ⟨(extraspecial_four_overgroup_pushingUp_setup d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout G₀ hJG.le hGC).2.2,
    extraspecial_four_strict_overgroup_geometry d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout G₀ hJG hGC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The common cubic and the original three-core branch

The actual common Sylow three-subgroup Y of K and H is Heisenberg27, and
X = Y ∩ L₁ is exactly Z(Y). Every Y-normalized subgroup of C_G(x) whose
order is divisible by three has an invariant Sylow containing X centrally.
Since X normally generates the original two-perfect L₁, any such subgroup
also normalized by L₁ contains L₁. In particular this applies to the actual
normal subgroups of every overgroup H ∩ C_G(x) < G₀ ≤ C_G(x).

When O₃(G₀/O₂(G₀)) is nontrivial, its literal preimage contains L₁, and
O₂(L₁) lies in O₂(G₀). The actual residual identity is
L₁ = O²(X O₂(G₀)) = X[O₂(G₀),X]. A full Sylow three-subgroup of G₀ then
normalizes L₁, so it lies in H ∩ C_G(x). That proper subgroup already
contains a full Sylow two-subgroup, hence G₀ has a prime divisor greater
than three.

The extension ExtraspecialFourThreeCore uses the quotient three-core
action to exclude such a prime and complete three-core vanishing.
No normality of L₁ in G₀ or local-recognition premise is assumed.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed pp.1052–1053.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Select the actual common three-Sylow in K and H. Its intersection with
L₁ is precisely its center of order three. -/
theorem extraspecial_four_three_sylow_center
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype := by
  obtain ⟨B,hYK,_,⟨e⟩,_,_⟩ := extraspecial_normalizer_three_sylow_in_residual
    d h hab structural previous faithful earlier he
  let Y := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
  have hNH := (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have hYH : IsSylowIn 3 Y F.H := by
    rw [←hNH]
    exact ⟨B,rfl⟩
  have hc := (extraspecial_normalizer_point_three_sylow h hab structural previous faithful he B).2
  have hYN : Y ≤ normalizer (K F : Set G) := map_subtype_le _
  have hYL : Y ≤ normalizer (F.Li L 1 : Set G) := hYN.trans
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  let X := (F.Li L 1).subgroupOf Y
  let : X.Normal := normal_subgroupOf_of_le_normalizer hYL
  have hX : Nat.card X = 3 := by
    rw [←card_map_of_injective Y.subtype_injective,subgroupOf_map_subtype,inf_comm]
    exact hc
  have hp : IsPGroup 3 Y := B.isPGroup'.map (normalizer (K F : Set G)).subtype
  have hXZ : X ≤ center Y := hp.normal_le_center_of_card_dvd_prime X (by rw [hX])
  have hXeq : X = center Y := eq_of_le_of_card_ge hXZ (by
    rw [hX,Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center])
  have hh := congrArg (map Y.subtype) hXeq
  rw [subgroupOf_map_subtype,inf_comm] at hh
  exact ⟨Y,hYK,IsSylowIn.restrict hYH hYK (K_le_H F),hYH,⟨e⟩,hc,hh⟩

/-- The original central cubic lies centrally in an invariant Sylow of
every Y-normalized subgroup of the outside involution centralizer whose
order is divisible by three. This applies simultaneously to all the
source overgroups G₀ and their normalized subgroups. -/
theorem extraspecial_four_invariant_three_sylows
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype ∧
      ∀ I : Subgroup G, I ≤ centralizer ({x} : Set G) →
        Y ≤ normalizer (I : Set G) → 3 ∣ Nat.card I →
        ∃ P : Sylow 3 I,
          let R := (P : Subgroup I).map I.subtype
          Y ≤ normalizer (R : Set G) ∧ Y ⊓ F.Li L 1 ≤ (center R).map R.subtype := by
  obtain ⟨Y,hYK,hSYK,hSYH,⟨e⟩,hc,hX⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  refine ⟨Y,hYK,hSYK,hSYH,⟨e⟩,hc,hX,?_⟩
  let C := centralizer ({x} : Set G)
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hr : primeRank 3 C ≤ 2 := hC.stronglyQuasithin 3 (by decide) (by decide)
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  intro I hIC hYI hd
  rw [hX]
  exact exists_sylow_center_containing_heisenberg_center_in Y I C e hr (hYK.trans hKC) hIC hYI hd


/-- The cubic intersection normally generates the actual two-perfect point
residual; its complement is the literal two-core of L₁. -/
theorem extraspecial_point_generated_by_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (X : Subgroup G) (hXL : X ≤ F.Li L 1) (hc : Nat.card X = 3) :
    X ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 ∧
      conjugateSpanBy X (F.Li L 1) = F.Li L 1 := by
  let A := F.Li L 1
  let Q := A.pCoreIn 2
  have hx : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hc]; decide)
  have hd : Disjoint X Q := hx.disjoint_of_coprime (isPGroup_pCoreIn 2 A) (by decide)
  have hn : A ≤ normalizer (Q : Set G) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hjoin : X ⊔ Q = A := eq_of_le_of_card_ge (sup_le hXL (pCoreIn_le 2 A)) (by
    rw [sup_comm X Q,card_sup_eq_mul_of_normalizes_of_disjoint Q X (hXL.trans hn) hd.symm,hc]
    have he := card_eq_card_quotient_mul_card_subgroup (s := pCore 2 A)
    rw [show Nat.card (A ⧸ pCore 2 A) = 3 from pointResidual_core_quotient_card h structural] at he
    have hQ : Nat.card Q = Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
    rw [hQ,he,Nat.mul_comm])
  refine ⟨hjoin,?_⟩
  exact conjugateSpan_eq_of_pPerfect_supplement A X A Q
    (isPPerfect_embedded_pResidual 2 (L ⊓ F.H)) (isPGroup_pCoreIn 2 A)
    hjoin (pCoreIn_le 2 A) A.le_normalizer

/-- Every subgroup normalized by the original Y and L₁ whose order is
divisible by three contains L₁. The conclusion uses the actual central
cubic and its normal generation, rather than a group-family label. -/
theorem extraspecial_four_point_containment
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype ∧
      ∀ I : Subgroup G, I ≤ centralizer ({x} : Set G) →
        Y ≤ normalizer (I : Set G) → F.Li L 1 ≤ normalizer (I : Set G) →
        3 ∣ Nat.card I → F.Li L 1 ≤ I := by
  obtain ⟨Y,hYK,hSYK,hSYH,heY,hc,hX,hSyl⟩ := extraspecial_four_invariant_three_sylows
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  refine ⟨Y,hYK,hSYK,hSYH,heY,hc,hX,?_⟩
  intro I hIC hYI hLI hd
  obtain ⟨P,_,hXP⟩ := hSyl I hIC hYI hd
  have hXI : Y ⊓ F.Li L 1 ≤ I :=
    hXP.trans ((map_subtype_le _).trans (map_subtype_le _))
  rw [←(extraspecial_point_generated_by_cubic h structural (Y ⊓ F.Li L 1) inf_le_right hc).2]
  exact conjugateSpanBy_le hXI hLI

/-- For every actual overgroup G₀, a normal subgroup divisible by three
contains the original L₁. Thus the nontrivial three-core preimage and every
normal component candidate are constrained by the same original cubic. -/
theorem extraspecial_four_normal_subgroup_contains_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ I : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hIG : I ≤ G₀) (hGI : G₀ ≤ normalizer (I : Set G)) (hd : 3 ∣ Nat.card I) :
    F.Li L 1 ≤ I := by
  obtain ⟨Y,hYK,_,_,_,_,_,hcontains⟩ := extraspecial_four_point_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hKG : K F ≤ G₀ := (le_inf (K_le_H F) hKC).trans hJG
  exact hcontains I (hIG.trans hGC) (hYK.trans (hKG.trans hGI))
    ((pointResidual_le F).trans (hKG.trans hGI)) hd


/-- A nontrivial three-core above O₂(G₀) contains L₁ in its literal
preimage. Consequently the intrinsic core of L₁ lies in O₂(G₀). -/
theorem extraspecial_four_threeCore_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    let I := (pCore 3 (G₀ ⧸ pCore 2 G₀)).comap (QuotientGroup.mk' (pCore 2 G₀))
    F.Li L 1 ≤ I.map G₀.subtype ∧ (F.Li L 1).pCoreIn 2 ≤ G₀.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let R := pCore 3 (G₀ ⧸ pCore 2 G₀)
  let I := R.comap q
  have hi : I.Normal := inferInstance
  have hd : 3 ∣ Nat.card (I.map G₀.subtype) := by
    rw [card_map_of_injective G₀.subtype_injective]
    have hRdiv : 3 ∣ Nat.card R := (pCore_isPGroup (p := 3)).card_eq_or_dvd.resolve_left
      (fun hc => hthree ((eq_bot_iff_card R).mpr hc))
    have hm : I.map q = R := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    exact hRdiv.trans (hm ▸ card_map_dvd I q)
  have hGI : G₀ ≤ normalizer (I.map G₀.subtype : Set G) := by
    have hh := (I.le_normalizer_map G₀.subtype)
    rw [I.normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hLI := extraspecial_four_normal_subgroup_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    G₀ (I.map G₀.subtype) hJG hGC (map_subtype_le _) hGI hd
  refine ⟨hLI,?_⟩
  let P := (F.Li L 1).pCoreIn 2
  have hPI : P ≤ I.map G₀.subtype := (pCoreIn_le 2 _).trans hLI
  have hPG : P ≤ G₀ := hPI.trans (map_subtype_le _)
  have hmap : (P.subgroupOf G₀).map q ≤ R := by
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨i,hi,hie⟩ := hPI hp
    exact (show i = p from Subtype.ext hie) ▸ hi
  have h2 : IsPGroup 2 ((P.subgroupOf G₀).map q) :=
    (isPGroup_pCoreIn 2 (F.Li L 1)).comap_subtype.map q
  have h3 : IsPGroup 3 ((P.subgroupOf G₀).map q) :=
    (pCore_isPGroup (p := 3)).to_le hmap
  have hbot : (P.subgroupOf G₀).map q = ⊥ := by
    simpa only [inf_idem] using (h2.disjoint_of_coprime h3 (by decide)).eq_bot
  have hk : P.subgroupOf G₀ ≤ pCore 2 G₀ := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hbot
  change P ≤ (pCore 2 G₀).map G₀.subtype
  simpa only [map_subgroupOf_eq_of_le hPG] using map_mono (f := G₀.subtype) hk

/-- In the three-core branch, the point residual is the literal two-residual
of X O₂(G₀), equivalently X[O₂(G₀),X], for the actual X = Y ∩ L₁.
The original strict-overgroup hypotheses provide normalization; no
ambient normality of L₁ is asserted or assumed. -/
theorem extraspecial_four_threeCore_point_reconstruction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype ∧
      let X := Y ⊓ F.Li L 1
      (pResidual 2 (G₀.pCoreIn 2 ⊔ X : Subgroup G)).map (G₀.pCoreIn 2 ⊔ X).subtype = F.Li L 1 ∧
        F.Li L 1 = X ⊔ ⁅G₀.pCoreIn 2,X⁆ := by
  obtain ⟨Y,hYK,hSYK,hSYH,heY,hc,hX⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  refine ⟨Y,hYK,hSYK,hSYH,heY,hc,hX,?_⟩
  let X := Y ⊓ F.Li L 1
  let Q := G₀.pCoreIn 2
  have hcore := (extraspecial_four_threeCore_point d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hx hxZ G₀ hJG.le hGC hthree).2
  have hQH := (extraspecial_four_strict_overgroup_geometry
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC).2.1
  have hNL : Q ≤ normalizer (F.Li L 1 : Set G) :=
    (hQH.trans (pCoreIn_le 2 F.H)).trans (by
      rw [←(extraspecial_source_14721 d h hab structural previous faithful earlier he).1]
      exact extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  have hgen := (extraspecial_point_generated_by_cubic h structural X inf_le_right hc).1
  have hjoin : Q ⊔ X = F.Li L 1 ⊔ Q := by
    apply le_antisymm
    · exact sup_le le_sup_right (inf_le_right.trans le_sup_left)
    · apply sup_le _ le_sup_left
      rw [←hgen]
      exact sup_le le_sup_right (hcore.trans le_sup_left)
  have hp : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 (L ⊓ F.H)
  have hr : (pResidual 2 (Q ⊔ X : Subgroup G)).map (Q ⊔ X).subtype = F.Li L 1 := by
    rw [hjoin]
    exact embedded_pResidual_join_pGroup _ _ hp (isPGroup_pCoreIn 2 G₀) hNL
  refine ⟨hr,?_⟩
  have hXp : IsPPerfect 2 X := by
    apply (pResidual_eq_top_iff 2 X).mp
    apply top_unique
    intro a _
    exact mem_pResidual_of_orderOf_coprime
      ((show Nat.Coprime 2 (Nat.card X) by rw [hc]; decide).of_dvd_right (orderOf_dvd_natCard a))
  change F.Li L 1 = X ⊔ ⁅Q,X⁆
  exact hr.symm.trans (embedded_pResidual_sup_eq_sup_commutator Q X (isPGroup_pCoreIn 2 G₀) hXp)


/-- If the actual quotient has a three-core, a full Sylow three-subgroup
of G₀ lies in H ∩ G₀. This is normalizer control from the retained
X O₂(G₀) residual, without assuming L₁ normal in G₀. -/
theorem extraspecial_four_threeCore_sylow_control
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    ∃ P : Sylow 3 G₀, (P : Subgroup G₀).map G₀.subtype ≤
      F.H ⊓ centralizer ({x} : Set G) := by
  obtain ⟨Y,hYK,_,_,⟨e⟩,hc,hX,hr,_⟩ := extraspecial_four_threeCore_point_reconstruction
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  let Q := G₀.pCoreIn 2
  let X := Y ⊓ F.Li L 1
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hYG : Y ≤ G₀ := hYK.trans ((le_inf (K_le_H F) hKC).trans hJG.le)
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hC.subgroup (G₀.subgroupOf (centralizer ({x} : Set G))))
  have hdiv : 3 ∣ Nat.card G₀ := (by
    rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    decide : 3 ∣ Nat.card Y).trans (card_dvd_of_le hYG)
  obtain ⟨P,_,hXP⟩ := exists_sylow_center_containing_heisenberg_center_in Y G₀ G₀ e
    (hG.stronglyQuasithin 3 (by decide) (by decide)) hYG le_rfl
    (hYG.trans G₀.le_normalizer) hdiv
  let R := (P : Subgroup G₀).map G₀.subtype
  have hRX : R ≤ normalizer (X : Set G) := by
    change R ≤ normalizer ((Y ⊓ F.Li L 1 : Subgroup G) : Set G)
    rw [hX]
    have hh : (center Y).map Y.subtype ≤ centralizer (R : Set G) :=
      hXP.trans (by rw [map_center_subtype_eq_inf_centralizer R]; exact inf_le_right)
    exact (le_centralizer_iff.mp hh).trans (Subgroup.centralizer_le_normalizer _)
  have hRQ : R ≤ normalizer (Q : Set G) := (map_subtype_le _).trans
    (G₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image G₀ (pCore 2 G₀)))
  have hRjoin : R ≤ normalizer ((Q ⊔ X : Subgroup G) : Set G) :=
    (le_inf hRQ hRX).trans (normalizer_inf_normalizer_le_normalizer_sup Q X)
  have hRL : R ≤ normalizer (F.Li L 1 : Set G) := by
    rw [←hr]
    exact hRjoin.trans (normalizer_le_normalizer_characteristic_image (Q ⊔ X) (pResidual 2 _))
  have hNL : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans
      (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  exact ⟨P,le_inf (hRL.trans_eq hNL) ((map_subtype_le _).trans hGC)⟩

/-- In the three-core branch the strict overgroup has a prime divisor
larger than three: its proper point normalizer already contains full
Sylow two- and three-subgroups. This is the contradiction used once the
quotient three-core action excludes every prime greater than three. -/
theorem extraspecial_four_threeCore_large_prime
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ Nat.card G₀ := by
  let J := (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀
  obtain ⟨P,hP⟩ := extraspecial_four_threeCore_sylow_control
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  have hPJ : (P : Subgroup G₀) ≤ J := fun p hp => hP (mem_map_of_mem G₀.subtype hp)
  have h3 : ¬ 3 ∣ J.index := fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPJ))
  have hSyl := IsSylowIn.restrict (H := centralizer ({x} : Set G))
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
  obtain ⟨S,hS⟩ := hSyl
  have hSJ : (S : Subgroup G₀) ≤ J := by
    intro s hs
    have hm : (s : G) ∈ (S : Subgroup G₀).map G₀.subtype := mem_map_of_mem _ hs
    rw [hS] at hm
    exact ⟨F.invariant 1 hm.1,hm.2⟩
  have h2 : ¬ 2 ∣ J.index := fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSJ))
  have hn : J.index ≠ 1 := by
    intro heq
    exact hJG.not_ge (relIndex_eq_one.mp heq)
  obtain ⟨q,hq,hqd⟩ := Nat.exists_prime_and_dvd hn
  have hq2 : q ≠ 2 := fun hh => h2 (hh ▸ hqd)
  have hq3 : q ≠ 3 := fun hh => h3 (hh ▸ hqd)
  exact ⟨q,hq,by have := hq.two_le; omega,hqd.trans J.index_dvd_card⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Vanishing of the original overgroup's quotient three-core

For each actual strict overgroup H ∩ C_G(x) < G₀ ≤ C_G(x), the quotient
G₀/O₂(G₀) has trivial three-core. If that core were nontrivial, the common
cubic and Sylow argument supplies a prime r > 3 dividing |G₀|. An element
of order r acts trivially on the quotient three-core by A.1.25(3). It
therefore normalizes X O₂(G₀) and its actual two-residual L₁, hence belongs
to H. This contradicts H's {2,3} prime support.

This proves the source three-core exclusion directly from the literal
quotient action, without an additional generalized-Fitting hypothesis.
Consequently every subnormal subgroup of G₀ lying in H is contained in
O₂(G₀). The original group, flag, central four-group, quotient maps and
earlier-source hypotheses are retained throughout.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed p.1053.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourThreeCore_extraspecial_H_prime_divisor
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card F.H) : r = 2 ∨ r = 3 := by
  have two_prime {A : Type u} [Group A] [Finite A] (hA : IsPGroup 2 A)
      (hdA : r ∣ Nat.card A) : r = 2 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn] at hdA
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdA)).resolve_left hr.ne_one
  have hcH := (pResidual 2 F.H).card_mul_index
  rw [←hcH] at hd
  rcases hr.dvd_mul.mp hd with hR | hQ
  · have hK : r ∣ Nat.card (K F) := by
      change r ∣ Nat.card ((pResidual 2 F.H).map F.H.subtype)
      rw [card_map_of_injective F.H.subtype_injective]
      exact hR
    have hcK := (pCore 2 (K F)).card_mul_index
    rw [←hcK] at hK
    rcases hr.dvd_mul.mp hK with hcore | hquot
    · exact Or.inl (two_prime (pCore_isPGroup (p := 2) (G := K F)) hcore)
    · obtain ⟨e⟩ := he
      change r ∣ Nat.card ((K F) ⧸ pCore 2 (K F)) at hquot
      rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card] at hquot
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hr.dvd_of_dvd_pow hquot)).resolve_left hr.ne_one)
  · change r ∣ Nat.card (F.H ⧸ pResidual 2 F.H) at hQ
    exact Or.inl (two_prime (isPGroup_quotient_pResidual (G := F.H) 2) hQ)

/-- The actual quotient of every strict outside-centralizer overgroup by
its two-core has trivial three-core. A prime greater than three supplied
by Sylow control acts trivially on that core by A.1.25(3), hence normalizes
X O₂(G₀) and its actual two-residual L₁, contradicting H's prime support. -/
theorem extraspecial_four_threeCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G)) :
    pCore 3 (G₀ ⧸ pCore 2 G₀) = ⊥ := by
  by_contra hthree
  obtain ⟨r,hr,hrbig,hrG⟩ := extraspecial_four_threeCore_large_prime
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' r hrG
  obtain ⟨Y,hYK,_,_,_,_,_,hres,_⟩ := extraspecial_four_threeCore_point_reconstruction
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  let Q := G₀.pCoreIn 2
  let X := Y ⊓ F.Li L 1
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let R := pCore 3 (G₀ ⧸ pCore 2 G₀)
  have hLI := (extraspecial_four_threeCore_point d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hx hxZ G₀ hJG.le hGC hthree).1
  have hXG : X ≤ G₀ := (inf_le_right.trans hLI).trans (map_subtype_le _)
  let X₀ := X.subgroupOf G₀
  have hXR : X₀.map q ≤ R := by
    rintro _ ⟨b,hb,rfl⟩
    obtain ⟨c,hc,hce⟩ := hLI (show (b : G) ∈ F.Li L 1 from hb.2)
    exact (show c = b from Subtype.ext hce) ▸ hc
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : primeRank 3 G₀ ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hGC) (inclusion_injective hGC)).trans
      (hC.stronglyQuasithin 3 (by decide) (by decide))
  have hR : primeRank 3 R ≤ 2 := (primeRank_subgroup_le 3 R).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G₀) pCore_isPGroup).trans hG)
  let f : G₀ →* MulAut R := (MulAut.conjNormal : (G₀ ⧸ pCore 2 G₀) →* MulAut R).comp q
  have hfa : f a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes
      ((hr.coprime_iff_not_dvd).mpr (fun hd => by
        have hh := ChapterA.lemma_A_1_25_3 pCore_isPGroup hR hr hd
        omega))
    · exact ha ▸ orderOf_map_dvd f a
    · exact orderOf_dvd_natCard _
  have hcent : q a ∈ centralizer (X₀.map q : Set (G₀ ⧸ pCore 2 G₀)) := by
    intro b hb
    have hh := congrArg (fun z : MulAut R => (z ⟨b,hXR hb⟩ : G₀ ⧸ pCore 2 G₀)) hfa
    change q a * b * (q a)⁻¹ = b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hnorm : a ∈ normalizer ((X₀ ⊔ pCore 2 G₀ : Subgroup G₀) : Set G₀) := by
    have hh := le_normalizer_comap q
      (show a ∈ (normalizer (X₀.map q : Set (G₀ ⧸ pCore 2 G₀))).comap q from
        Subgroup.centralizer_le_normalizer _ hcent)
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hnormG : (a : G) ∈ normalizer ((Q ⊔ X : Subgroup G) : Set G) := by
    have hh := (X₀ ⊔ pCore 2 G₀).le_normalizer_map G₀.subtype
      (mem_map_of_mem G₀.subtype hnorm)
    rw [Subgroup.map_sup,show X₀.map G₀.subtype = X from map_subgroupOf_eq_of_le hXG,
      show (pCore 2 G₀).map G₀.subtype = Q from rfl,sup_comm X Q] at hh
    exact hh
  have haL : (a : G) ∈ normalizer (F.Li L 1 : Set G) := by
    rw [←hres]
    exact normalizer_le_normalizer_characteristic_image (Q ⊔ X) (pResidual 2 _) hnormG
  have hNL : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans
      (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have haH : (a : G) ∈ F.H := hNL ▸ haL
  have horder : orderOf (⟨a,haH⟩ : F.H) = r := by
    exact (orderOf_injective F.H.subtype F.H.subtype_injective _).symm.trans
      ((orderOf_injective G₀.subtype G₀.subtype_injective a).trans ha)
  have hh := ExtraspecialFourThreeCore_extraspecial_H_prime_divisor he hr (horder ▸ orderOf_dvd_natCard (⟨a,haH⟩ : F.H))
  omega
/-- O₂(G₀) contains every subnormal subgroup of the actual overgroup lying in H. -/
theorem extraspecial_four_subnormal_le_core
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (J : Subgroup G) (hJH : J ≤ F.H) (hJG₀ : J ≤ G₀)
    (hsub : (J.subgroupOf G₀).IsSubnormal) : J ≤ G₀.pCoreIn 2 := by
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hh := le_twoCore_of_subnormal_two_three h3 (J.subgroupOf G₀) hsub (by
    intro p hp hd
    have hcardJ : Nat.card (J.subgroupOf G₀) = Nat.card J :=
      Nat.card_congr (subgroupOfEquivOfLe hJG₀).toEquiv
    rw [hcardJ] at hd
    exact ExtraspecialFourThreeCore_extraspecial_H_prime_divisor he hp (hd.trans (card_dvd_of_le hJH)))
  change J ≤ (pCore 2 G₀).map G₀.subtype
  simpa only [map_subgroupOf_eq_of_le hJG₀] using map_mono (f := G₀.subtype) hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The component divisible by three in the original overgroup

Every C-component of G₀ whose order is divisible by three contains the
original L₁: the two-perfect Y and L₁ normalize it by the proved source
orbit theorem, so the common cubic and its normal generation apply.
In a strict outside-centralizer overgroup, there is at most one such
component. Distinct components commute modulo the literal two-core;
their common cubic would then lie in O₃(G₀/O₂(G₀)), already proved trivial.
Conjugation preserves the prime divisor, so this component is normal.

These are the component containment, uniqueness and normality reductions
in Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf. Existence,
the characteristic-two-overgroup exclusions, the automorphism restrictions
and the final outside-centralizer containment still require proof.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Every actual C-component of the overgroup whose order is divisible by three contains the original point residual. -/
theorem extraspecial_four_component_contains_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (B : Subgroup G₀) (hB : B.IsCComponent) (hd : 3 ∣ Nat.card B) :
    F.Li L 1 ≤ B.map G₀.subtype := by
  obtain ⟨Y,hYK,_,_,⟨e⟩,_,_,hcontains⟩ := extraspecial_four_point_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hKG : K F ≤ G₀ := (le_inf (K_le_H F) hKC).trans hJG
  have hYG := hYK.trans hKG
  have hLG : F.Li L 1 ≤ G₀ := (pointResidual_le F).trans hKG
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hC.subgroup (G₀.subgroupOf (centralizer ({x} : Set G))))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G₀ ⧸ pCore 2 G₀) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have hYperfect : IsPPerfect 2 Y := by
    apply (pResidual_eq_top_iff 2 Y).mp
    apply top_unique
    intro a _
    apply mem_pResidual_of_orderOf_coprime
    apply Nat.Coprime.of_dvd_right (orderOf_dvd_natCard a)
    rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    decide
  have normalizes (A : Subgroup G) (hAG : A ≤ G₀) (hA : IsPPerfect 2 A) :
      A ≤ normalizer (B.map G₀.subtype : Set G) := by
    have hp := hA.of_surjective (subgroupOfEquivOfLe hAG).symm.toMonoidHom
      (subgroupOfEquivOfLe hAG).symm.surjective
    have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hB hp
    have hm := (map_mono (f := G₀.subtype) hn).trans (B.le_normalizer_map G₀.subtype)
    simpa only [map_subgroupOf_eq_of_le hAG] using hm
  exact hcontains _ ((map_subtype_le _).trans hGC)
    (normalizes Y hYG hYperfect)
    (normalizes (F.Li L 1) hLG (isPPerfect_embedded_pResidual 2 (L ⊓ F.H)))
    (by rw [card_map_of_injective G₀.subtype_injective]; exact hd)

/-- The actual overgroup has at most one C-component divisible by three. -/
theorem extraspecial_four_component_unique
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (B C : Subgroup G₀) (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hdB : 3 ∣ Nat.card B) (hdC : 3 ∣ Nat.card C) : B = C := by
  by_contra hne
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let B₀ := B.map q
  let C₀ := C.map q
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hCen := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hCen.subgroup (G₀.subgroupOf (centralizer ({x} : Set G))))
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G₀ ⧸ pCore 2 G₀) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let := (pCore_isPGroup (p := 2) (G := G₀)).isNilpotent
  have hBC := ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
    (pCore_quotient_pCore_eq_bot 2) (hB.map_quotient (pCore 2 G₀))
    (hC.map_quotient (pCore 2 G₀))
    (fun hh => hne (hB.eq_of_map_quotient_eq hC (pCore 2 G₀) hh))
  have hLB := extraspecial_four_component_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    G₀ hJG.le hGC B hB hdB
  have hLC := extraspecial_four_component_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    G₀ hJG.le hGC C hC hdC
  obtain ⟨Y,_,_,_,_,hc,_⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  let X := Y ⊓ F.Li L 1
  have hXG : X ≤ G₀ := (inf_le_right.trans hLB).trans (map_subtype_le _)
  let X₀ := X.subgroupOf G₀
  have hXcard : Nat.card X₀ = 3 := (Nat.card_congr (subgroupOfEquivOfLe hXG).toEquiv).trans hc
  have hXp : IsPGroup 3 X₀ := IsPGroup.of_card (n := 1) (by rw [hXcard]; decide)
  have hXB : X₀ ≤ B := by
    have hh := comap_mono (f := G₀.subtype) (inf_le_right.trans hLB : X ≤ B.map G₀.subtype)
    rw [comap_map_eq_self_of_injective G₀.subtype_injective] at hh
    exact hh
  have hXC : X₀ ≤ C := by
    have hh := comap_mono (f := G₀.subtype) (inf_le_right.trans hLC : X ≤ C.map G₀.subtype)
    rw [comap_map_eq_self_of_injective G₀.subtype_injective] at hh
    exact hh
  have hZN : B₀ ≤ normalizer (X₀.map q : Set (G₀ ⧸ pCore 2 G₀)) :=
    ((commutator_eq_bot_iff_le_centralizer.mp hBC).trans
      (centralizer_le (map_mono (f := q) hXC))).trans (Subgroup.centralizer_le_normalizer _)
  have hZ3 : X₀.map q ≤ pCore 3 (G₀ ⧸ pCore 2 G₀) :=
    (le_pCoreIn_of_normalizes (hXp.map q) (map_mono (f := q) hXB) hZN).trans
      (pCoreIn_le_of_subnormal 3 (hB.subnormal.map (QuotientGroup.mk'_surjective _)))
  have hZbot : X₀.map q = ⊥ := le_bot_iff.mp (hZ3.trans h3.le)
  have hXtwo : X₀ ≤ pCore 2 G₀ := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff X₀).mp hZbot
  have hp2 : IsPGroup 2 X₀ := (pCore_isPGroup (p := 2) (G := G₀)).to_le hXtwo
  rcases hp2.card_eq_or_dvd with h1 | hd
  · rw [hXcard] at h1
    omega
  · rw [hXcard] at hd
    norm_num at hd

/-- The C-component divisible by three is normal in the original overgroup. -/
theorem extraspecial_four_component_normal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (B : Subgroup G₀) (hB : B.IsCComponent) (hdB : 3 ∣ Nat.card B) : B.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  exact extraspecial_four_component_unique
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC (B.map (MulAut.conj g).toMonoidHom) B (hB.map_equiv (MulAut.conj g)) hB
    (by rw [card_map_of_injective (MulAut.conj g).injective]; exact hdB) hdB

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Component and automorphism reductions in the outside centralizer

For each original strict overgroup H ∩ C_G(x) < G₀ ≤ C_G(x) of
characteristic two, C.1.29 absorbs the prime-to-three core into H.
The preceding subnormal reduction then makes O₃′(G₀/O₂(G₀)) trivial.
Together with the proved three-core vanishing this kills the solvable
radical of the quotient, and every C-component is divisible by three.
Thus there is a unique normal component, containing the original L₁.

Its quotient by its own two-core is simple. The genuine C.2.7 hypotheses
are constructed in the original ambient group; the central comparison
kernel vanishes, identifying this quotient with the classified star image.
The literal quotient action has kernel exactly O₂(G₀), so the original
Heisenberg subgroup acts faithfully. The action image contains the inner
group, and the actual local intersection has odd index in it and retains
its marked Heisenberg residual modulo its own two-core.

If the full outside centralizer fails characteristic two, its already
proved trivial odd core supplies an ordinary component. The original
1.1.5 data gives its marked model action and escape from H. The model
exclusions in both branches, centralizer containment, TI and the eventual
14.7.52 residual alternatives are not asserted here.

Source: Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf;
C.1.29, C.2.5–7 and1.1.5 provide the earlier source inputs.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem ExtraspecialFourCharacteristic_extraspecial_H_prime_divisor
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card F.H) : r = 2 ∨ r = 3 := by
  have two_prime {A : Type u} [Group A] [Finite A] (hA : IsPGroup 2 A)
      (hdA : r ∣ Nat.card A) : r = 2 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn] at hdA
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdA)).resolve_left hr.ne_one
  have hcH := (pResidual 2 F.H).card_mul_index
  rw [←hcH] at hd
  rcases hr.dvd_mul.mp hd with hR | hQ
  · have hK : r ∣ Nat.card (K F) := by
      change r ∣ Nat.card ((pResidual 2 F.H).map F.H.subtype)
      rw [card_map_of_injective F.H.subtype_injective]
      exact hR
    have hcK := (pCore 2 (K F)).card_mul_index
    rw [←hcK] at hK
    rcases hr.dvd_mul.mp hK with hcore | hquot
    · exact Or.inl (two_prime (pCore_isPGroup (p := 2) (G := K F)) hcore)
    · obtain ⟨e⟩ := he
      change r ∣ Nat.card ((K F) ⧸ pCore 2 (K F)) at hquot
      rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card] at hquot
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hr.dvd_of_dvd_pow hquot)).resolve_left hr.ne_one)
  · change r ∣ Nat.card (F.H ⧸ pResidual 2 F.H) at hQ
    exact Or.inl (two_prime (isPGroup_quotient_pResidual (G := F.H) 2) hQ)

/-- Under characteristic two, the actual strict overgroup has trivial prime-to-three core modulo its two-core. -/
theorem extraspecial_four_primeToThreeCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    pPrimeCore 3 (G₀ ⧸ pCore 2 G₀) = ⊥ := by
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  let R := (F.H.pCoreIn 2).subgroupOf G₀
  let M := J.subgroupOf G₀
  obtain ⟨_,_,hsetup⟩ := extraspecial_four_overgroup_pushingUp_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG.le hGC
  have hH23 : IsPiGroup twoThreePrimes F.H := (IsPiGroup_iff _ _).mpr
    (fun p hp => ExtraspecialFourCharacteristic_extraspecial_H_prime_divisor he p.property hp)
  have hM23 : IsPiGroup twoThreePrimes M :=
    hH23.of_injective ((inclusion (show J ≤ F.H from inf_le_left)).comp
      (subgroupOfEquivOfLe hJG.le).toMonoidHom)
      ((inclusion_injective inf_le_left).comp (subgroupOfEquivOfLe hJG.le).injective)
  have hR : IsPGroup 2 R := hsetup.radical.isPGroup
  have hcore : pCore 2 G₀ ≤ R :=
    ChapterC.twoCore_le_radical R hR hsetup.radical.2
  have hRM : M.pCoreIn 2 ≤ R := by
    rw [pCoreIn_subgroupOf 2 J G₀ hJG.le]
    rw [(extraspecial_four_core_eq d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc hx hxZ hout).1]
  have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ := IsSylowIn.restrict (H := C)
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
  obtain ⟨P,hP⟩ := hS
  have hPM : (P : Subgroup G₀) ≤ M := by
    intro a ha
    have hh : (a : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem G₀.subtype ha
    exact ⟨F.invariant 1 hh.1,hh.2⟩
  have hNM := ChapterC.Section02Source.primeToThreeCore_le_control hsetup.sqtk
    R M hR hcore hsetup.characteristic_control
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf) hM23 hRM P hPM
  have h3 := extraspecial_four_threeCore_eq_bot d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hnc hx hxZ hout G₀ hJG hGC
  have hNcore : pPrimeCore 3 G₀ ≤ pCore 2 G₀ := le_twoCore_of_subnormal_two_three h3 _
    (inferInstance : (pPrimeCore 3 G₀).Normal).isSubnormal (by
      intro p hp hd
      exact (IsPiGroup_iff _ _).mp hM23 ⟨p,hp⟩ (hd.trans (card_dvd_of_le hNM)))
  let q := QuotientGroup.mk' (pCore 2 G₀)
  have hker : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G₀)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  apply le_bot_iff.mp
  have hpre := pPrimeCore_comap_eq_of_surjective_coprime 3 q
    (QuotientGroup.mk'_surjective _) hker
  have hm := map_mono (f := q) (hpre.trans_le hNcore)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _,
    show (pCore 2 G₀).map q = ⊥ from by
      rw [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']] at hm
  exact hm

/-- The actual characteristic-two overgroup has a unique normal C-component containing L₁, with simple two-core quotient and faithful ambient quotient action. -/
theorem extraspecial_four_characteristicTwo_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ B.Normal ∧
      F.Li L 1 ≤ B.map G₀.subtype ∧
      (∀ A : Subgroup G₀, A.IsCComponent → A = B) ∧
      fittingSubgroup (G₀ ⧸ pCore 2 G₀) = ⊥ ∧
      centralizer (B.map (QuotientGroup.mk' (pCore 2 G₀)) : Set (G₀ ⧸ pCore 2 G₀)) = ⊥ ∧
      IsSimpleGroup (B ⧸ pCore 2 B) := by
  let q := QuotientGroup.mk' (pCore 2 G₀)
  have ho := extraspecial_four_primeToThreeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hfit : fittingSubgroup (G₀ ⧸ pCore 2 G₀) = ⊥ :=
    le_bot_iff.mp ((fitting_le_pPrimeCore_of_pCore_eq_bot 3 h3).trans ho.le)
  have hnsol : ¬ Group.IsSolvable G₀ := by
    intro hs
    let := hs
    have hcardQ := (fitting_eq_bot_iff_card_eq_one_of_solvable (G₀ ⧸ pCore 2 G₀)).mp hfit
    have htop : pCore 2 G₀ = ⊤ := index_eq_one.mp hcardQ
    have hcore := (extraspecial_four_strict_overgroup_geometry
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC).2.1
    have hGle : G₀ ≤ F.H := by
      intro a ha
      apply (pCoreIn_le 2 F.H) (hcore ?_)
      exact mem_map_of_mem G₀.subtype (show (⟨a,ha⟩ : G₀) ∈ pCore 2 G₀ by
        rw [htop]; exact mem_top _)
    exact hJG.not_ge (le_inf hGle hGC)
  let := (pCore_isPGroup (p := 2) (G := G₀)).isNilpotent
  have hdiv (B : Subgroup G₀) (hB : B.IsCComponent) : 3 ∣ Nat.card B := by
    by_contra hd
    let B₀ := B.map q
    have hB₀ : B₀.IsCComponent := hB.map_quotient _
    have hBthree : ¬ 3 ∣ Nat.card B₀ := fun hh => hd (hh.trans (card_map_dvd B q))
    have hBo : pPrimeCore 3 B₀ = ⊥ := hB₀.subnormal.pPrimeCore_eq_bot ho
    have ht : (⊤ : Subgroup B₀) ≤ pPrimeCore 3 B₀ := le_sSup ⟨inferInstance,by
      simpa only [card_top] using Nat.prime_three.coprime_iff_not_dvd.mpr hBthree⟩
    have heq : (⊤ : Subgroup B₀) = ⊥ := le_bot_iff.mp (ht.trans hBo.le)
    have hbcard : Nat.card B₀ = 1 := by
      simpa only [card_top,card_bot] using congrArg (fun A : Subgroup B₀ => Nat.card A) heq
    exact hB₀.ne_bot ((eq_bot_iff_card B₀).mpr hbcard)
  obtain ⟨B,hB⟩ := exists_isCComponent_of_not_isSolvable hnsol
  have hu (A : Subgroup G₀) (hA : A.IsCComponent) : A = B :=
    extraspecial_four_component_unique
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC A B hA hB (hdiv A hA) (hdiv B hB)
  have hB₀ : (B.map q).IsCComponent := hB.map_quotient _
  have hu₀ (A : Subgroup (G₀ ⧸ pCore 2 G₀)) (hA : A.IsCComponent) : A = B.map q :=
    hB.unique_map_quotient hu _ hA
  have hs : IsSimpleGroup (B ⧸ pCore 2 B) := by
    let := hB₀.isSimpleGroup_of_solvableRadical_eq_bot (radical_bot_of_fitting_bot hfit)
    exact (cComponentTwoCoreQuotientEquiv hB).isSimpleGroup
  exact ⟨B,hB,hB.normal_of_unique hu,
    extraspecial_four_component_contains_point d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ G₀ hJG.le hGC B hB (hdiv B hB),
    hu,hfit,hB₀.centralizer_bot_of_unique_of_fitting_bot hu₀ hfit,hs⟩

/-- Construct the genuine C.2.7 input and identify the original component quotient with its classified star image. -/
theorem extraspecial_four_characteristicTwo_source_model
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ E : Subgroup G, E ∈ cComponentsIn G₀ ∧ (E.subgroupOf G₀).Normal ∧
      F.Li L 1 ≤ E ∧ IsSimpleGroup (E ⧸ pCore 2 E) ∧
      RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
          (F.H ⊓ centralizer ({x} : Set G)) E ∧
      Nonempty ((E ⧸ pCore 2 E) ≃*
        RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E) ∧
      ChapterC.C27Source.StarModels.Model
        (RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E) := by
  obtain ⟨B,hB,hn,hLB,hu,hfit,hcen,hs⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  let := hn
  let E := B.map G₀.subtype
  let e : B ≃* E := equivMapOfInjective B G₀.subtype G₀.subtype_injective
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let eQ := QuotientGroup.congr (pCore 2 B) (pCore 2 E) e (pCore_map_iso 2 e)
  have hEB : E.subgroupOf G₀ = B := comap_map_eq_self_of_injective G₀.subtype_injective B
  have hE : E ∈ cComponentsIn G₀ := ⟨map_subtype_le _,hEB ▸ hB⟩
  have hEn : (E.subgroupOf G₀).Normal := hEB ▸ hn
  let : IsSimpleGroup (B ⧸ pCore 2 B) := hs
  have hEs : IsSimpleGroup (E ⧸ pCore 2 E) := eQ.symm.isSimpleGroup
  let := (pCore_isPGroup (p := 2) (G := G₀)).isNilpotent
  have hBq : (B.map q).IsCComponent := hB.map_quotient _
  have hr := radical_bot_of_fitting_bot hfit
  have hq : IsQuasisimple (B.map q) :=
    ((isCComponent_iff_isSubnormal_and_isQuasisimple_of_solvableRadical_eq_bot hr).mp hBq).2
  have hEq : IsQuasisimple (E ⧸ pCore 2 E) := hq.of_mulEquiv
    ((cComponentTwoCoreQuotientEquiv hB).symm.trans eQ)
  have hEf : generalizedFitting E = pCore 2 E := by
    have hBf : generalizedFitting B = pCore 2 B :=
      generalizedFitting_eq_pCore_of_selfCentralizing 2
        (subnormal_core_selfCentralizing ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
          B hB.subnormal)
    have hh := congrArg (map e.toMonoidHom) hBf
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hEout : ¬ E ≤ F.H ⊓ centralizer ({x} : Set G) := by
    intro hEJ
    apply hB.not_isSolvable
    apply isSolvable_of_prime_dvd_card_eq_two_or_three B
    intro p hp hd
    have hdE : p ∣ Nat.card E := (Nat.card_congr e.toEquiv) ▸ hd
    exact ExtraspecialFourCharacteristic_extraspecial_H_prime_divisor he hp
      (hdE.trans (card_dvd_of_le (hEJ.trans inf_le_left)))
  obtain ⟨_,_,hsetup⟩ := extraspecial_four_overgroup_pushingUp_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG.le hGC
  have hnorm : F.H.pCoreIn 2 ≤ normalizer (E : Set G) :=
    hsetup.radical_le.trans ((normal_subgroupOf_iff_le_normalizer hE.1).mp hEn)
  have hi : RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
        (F.H ⊓ centralizer ({x} : Set G)) E :=
    ⟨hsetup,hE,hEq,hEf,hEout,hnorm⟩
  have hz : center (E ⧸ pCore 2 E) = ⊥ := by
    let a := eQ.symm.trans (cComponentTwoCoreQuotientEquiv hB)
    have hbz := center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hr hBq.subnormal
    have hh : (center (E ⧸ pCore 2 E)).map a.toMonoidHom = center (B.map q) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (centerCongr a ⟨y,hy⟩).property
      · intro hx
        exact ⟨a.symm x,(centerCongr a.symm ⟨x,hx⟩).property,a.apply_symm_apply x⟩
    exact (map_eq_bot_iff_of_injective _ a.injective).mp (hh.trans hbz)
  have hker : (RadicalExclusions.ModelReduction.coreToStar hnorm).ker = ⊥ :=
    le_bot_iff.mp ((ChapterC.C27Source.coreToStar_ker_central_from_source hi).trans hz.le)
  let es := MulEquiv.ofBijective (RadicalExclusions.ModelReduction.coreToStar hnorm)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hker,RadicalExclusions.ModelReduction.coreToStar_surjective hnorm⟩
  exact ⟨E,hE,hEn,hLB,hEs,hi,⟨es⟩,ChapterC.C27Source.star_model_from_source hi⟩

private theorem ExtraspecialFourCharacteristic_four_intersection_product {D : Subgroup G}
    (hDK : D ≤ (center (K F)).map (K F).subtype) {x : G} (hx : x ∈ D) :
    K F ⊔ ((T : Subgroup G) ⊓ centralizer ({x} : Set G)) =
      F.H ⊓ centralizer ({x} : Set G) := by
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  apply le_antisymm
  · exact sup_le (le_inf (K_le_H F) hKC)
      (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  · rintro y ⟨hyH,hyC⟩
    rw [residual_product F] at hyH
    have hm : y ∈ (K F : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (K F) (T : Subgroup G)
        ((F.invariant 1).trans (H_normalizes_K F))]
      exact hyH
    obtain ⟨k,hk,t,ht,rfl⟩ := hm
    have htC := (centralizer ({x} : Set G)).mul_mem
      ((centralizer ({x} : Set G)).inv_mem (hKC hk)) hyC
    rw [inv_mul_cancel_left] at htC
    exact mul_mem (mem_sup_left hk) (mem_sup_right ⟨ht,htC⟩)

/-- Every image of the actual intersection with two-group kernel retains
the marked Heisenberg two-residual after dividing by its own two-core. -/
theorem extraspecial_four_image_residual
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {D : Subgroup G} (hDK : D ≤ (center (K F)).map (K F).subtype)
    {x : G} (hx : x ∈ D)
    {A : Type*} [Group A] [Finite A]
    (f : (F.H ⊓ centralizer ({x} : Set G) : Subgroup G) →* A)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty (pResidual 2 (A ⧸ pCore 2 A) ≃* HeisenbergPrime 3) := by
  let J := F.H ⊓ centralizer ({x} : Set G)
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  have hprod : K F ⊔ S = J := ExtraspecialFourCharacteristic_four_intersection_product hDK hx
  have hres : (pResidual 2 J).map J.subtype = K F := by
    rw [←hprod]
    exact embedded_pResidual_join_pGroup (K F) S (K_twoPerfect F)
      (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F)))
  let eR : pResidual 2 J ≃* K F :=
    (equivMapOfInjective (pResidual 2 J) J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hres)
  let eK := QuotientGroup.congr (pCore 2 (pResidual 2 J)) (pCore 2 (K F)) eR
    (pCore_map_iso 2 eR)
  have hcore : pCore 2 (pResidual 2 J) = (pCore 2 J).subgroupOf (pResidual 2 J) :=
    pCore_subnormal_eq_comap 2 (inferInstance : (pResidual 2 J).Normal).isSubnormal
  let eJ := (QuotientGroup.quotientMulEquivOfEq hcore).trans
    (pResidualQuotientEquiv 2 (pCore 2 J))
  let eA := f.pCoreQuotientEquiv hf hk
  let erA := (eA.subgroupMap (pResidual 2 (J ⧸ pCore 2 J))).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 eA))
  obtain ⟨e⟩ := he
  exact ⟨erA.symm.trans (eJ.symm.trans (eK.trans e))⟩

/-- The original Heisenberg Sylow subgroup acts faithfully on the actual component quotient. -/
theorem extraspecial_four_characteristicTwo_faithful_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ ∃ hn : B.Normal,
      letI := hn
      (normalQuotientAction B (pCore 2 B)).ker = pCore 2 G₀ ∧
      ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y F.H ∧
        Nonempty (Y ≃* HeisenbergPrime 3) ∧ ∃ hYG : Y ≤ G₀,
          Function.Injective ((normalQuotientAction B (pCore 2 B)).comp (inclusion hYG)) := by
  obtain ⟨B,hB,hn,_,_,_,hc,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  refine ⟨B,hB,hn,?_⟩
  let := hn
  have hk := hB.normalQuotientAction_ker_of_centralizer_eq_bot hc
  refine ⟨hk,?_⟩
  obtain ⟨Y,hYK,_,hYH,⟨e⟩,_,_⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hkk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hkk)
  have hYG : Y ≤ G₀ := hYK.trans ((le_inf (K_le_H F) hKC).trans hJG.le)
  refine ⟨Y,hYK,hYH,⟨e⟩,hYG,?_⟩
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 3)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hcop : Nat.Coprime 3 (Nat.card (normalQuotientAction B (pCore 2 B)).ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G₀)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (injective_comp_subtype_of_coprime_ker (normalQuotientAction B (pCore 2 B))
    hcop (Y.subgroupOf G₀) hYp.comap_subtype).comp (subgroupOfEquivOfLe hYG).symm.injective

/-- The actual automorphism image contains the inner group and the image of the original local intersection has odd index and marked Heisenberg residual. -/
theorem extraspecial_four_characteristicTwo_automorphism_restrictions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ ∃ hn : B.Normal,
      letI := hn
      let a := normalQuotientAction B (pCore 2 B)
      let M := (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀
      let Mₐ := M.map a.rangeRestrict
      a.ker = pCore 2 G₀ ∧ MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range ∧
        Odd Mₐ.index ∧ Nonempty (pResidual 2 (Mₐ ⧸ pCore 2 Mₐ) ≃* HeisenbergPrime 3) := by
  obtain ⟨B,hB,hn,_,_,_,hc,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  refine ⟨B,hB,hn,?_⟩
  let := hn
  let a := normalQuotientAction B (pCore 2 B)
  let C := centralizer ({x} : Set G)
  let J := F.H ⊓ C
  let M := J.subgroupOf G₀
  let Mₐ := M.map a.rangeRestrict
  have hk : a.ker = pCore 2 G₀ := hB.normalQuotientAction_ker_of_centralizer_eq_bot hc
  refine ⟨hk,?_,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    exact ⟨b,normalQuotientAction_inner B (pCore 2 B) b⟩
  · have hS : IsSylowIn 2 ((T : Subgroup G) ⊓ C) G₀ := IsSylowIn.restrict (H := C)
      (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
      ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
    obtain ⟨P,hP⟩ := hS
    have hPM : (P : Subgroup G₀) ≤ M := by
      intro b hb
      have hh : (b : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem G₀.subtype hb
      exact ⟨F.invariant 1 hh.1,hh.2⟩
    have hodd : Odd M.index := Nat.not_even_iff_odd.mp (fun heven =>
      P.not_dvd_index (((even_iff_two_dvd).mp heven).trans (index_dvd_of_le hPM)))
    exact hodd.of_dvd_nat (M.index_map_dvd a.rangeRestrict_surjective)
  · let f : J →* Mₐ := (a.rangeRestrict.subgroupMap M).comp
      (subgroupOfEquivOfLe hJG.le).symm.toMonoidHom
    have hf : Function.Surjective f := (a.rangeRestrict.subgroupMap_surjective M).comp
      (subgroupOfEquivOfLe hJG.le).symm.surjective
    have hkf : f.ker = (pCore 2 G₀).comap (inclusion hJG.le) := by
      ext j
      change f j = 1 ↔ inclusion hJG.le j ∈ pCore 2 G₀
      rw [Subtype.ext_iff,Subtype.ext_iff]
      change inclusion hJG.le j ∈ a.ker ↔ inclusion hJG.le j ∈ pCore 2 G₀
      rw [hk]
    have hpf : IsPGroup 2 f.ker := by
      rw [hkf]
      exact pCore_isPGroup.comap_of_injective (inclusion hJG.le) (inclusion_injective hJG.le)
    exact extraspecial_four_image_residual he hDK hx f hf hpf

/-- Failure of characteristic two supplies an actual ordinary component and its original marked 1.1.5 action. -/
theorem extraspecial_four_ordinary_component_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hf : generalizedFitting (centralizer ({x} : Set G)) ≠
      pCore 2 (centralizer ({x} : Set G))) :
    ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      Chapter15.Section03.Candidates.ComponentStructure.HasModelAction115 B z := by
  have ho := extraspecial_four_oddCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨B,hB⟩ := exists_component_of_oddCore_eq_bot ho hf
  obtain ⟨_,_,z,hz,hzp,P,_,hs⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨hm,houtB,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple d.qtke
    (centralizer ({x} : Set G)) P F.H z hs B hB
  exact ⟨B,z,hB,hz,hzp,hm,houtB,hmodel⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end



/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Excluding characteristic-two overgroups in the extraspecial four-group branch

For the original strict overgroups H ∩ C_G(x) < G₀ ≤ C_G(x), the genuine
C.2.7 catalogue and faithful Heisenberg action first leave only Sp₄(q) and
G₂(q), q > 2 even. The same literal action image contains the inner group,
has three-rank at most two, and contains a solvable odd-index subgroup
carrying the original faithful Heisenberg action. Cubic field-actor control
makes that action inner; solvable Sylow control then places it in a Borel
whose odd subgroups are abelian, a contradiction.

Consequently no such strict overgroup has F*(G₀) = O₂(G₀). This is the
maximality assertion (*) of 14.7.26. Applying it to the full escaping
centralizer discharges the extra characteristic-two premise in the
ordinary-component extraction and preserves the actual 1.1.5 marking.
The ordinary-component catalogue exclusions, centralizer containment and
TI conclusion remain subsequent steps.

Source: Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The faithful original action reduces the C.2.7 catalogue to the two larger rank-two families. -/
theorem extraspecial_four_characteristicTwo_lie_model
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ E : Subgroup G, E ∈ cComponentsIn G₀ ∧ (E.subgroupOf G₀).Normal ∧
      F.Li L 1 ≤ E ∧ IsSimpleGroup (E ⧸ pCore 2 E) ∧
      RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple G₀ (F.H.pCoreIn 2)
          (F.H ⊓ centralizer ({x} : Set G)) E ∧
      ∃ k : ChapterB.QuasisimpleSource.BinaryField, 1 < k.degree ∧
        (Nonempty ((E ⧸ pCore 2 E) ≃* Matrix.symplecticGroup (Fin 2) k.Carrier) ∨
         Nonempty ((E ⧸ pCore 2 E) ≃* Atlas.G2.Model k.Carrier)) := by
  obtain ⟨E,hE,hnE,hLE,hs,hi,⟨es⟩,hm⟩ := extraspecial_four_characteristicTwo_source_model
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  obtain ⟨B₀,_,_,_,hu,_,_,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  have hBE (B : Subgroup G₀) (hB : B.IsCComponent) : B = E.subgroupOf G₀ :=
    (hu B hB).trans (hu _ hE.2).symm
  let eqB (B : Subgroup G₀) (hB : B.IsCComponent) : B ≃* E :=
    (MulEquiv.subgroupCongr (hBE B hB)).trans (subgroupOfEquivOfLe hE.1)
  let eqQ (B : Subgroup G₀) (hB : B.IsCComponent) :
      (B ⧸ pCore 2 B) ≃* (E ⧸ pCore 2 E) :=
    QuotientGroup.congr _ _ (eqB B hB) (pCore_map_iso 2 (eqB B hB))
  let Q := RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E
  have hfaithful : ∃ a : HeisenbergPrime 3 →* MulAut Q, Function.Injective a := by
    obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_faithful_action
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC hf
    let := hn
    obtain ⟨_,Y,_,_,⟨ey⟩,hYG,hinj⟩ := hb
    let a := (normalQuotientAction B (pCore 2 B)).comp (inclusion hYG)
    let e := MulAut.congr ((eqQ B hB).trans es)
    exact ⟨e.toMonoidHom.comp (a.comp ey.symm.toMonoidHom),
      e.injective.comp (hinj.comp ey.symm.injective)⟩
  obtain ⟨a,ha⟩ := hfaithful
  have h27 : 27 ∣ Nat.card (MulAut Q) := by
    have hd := card_dvd_of_injective a ha
    simpa only [HeisenbergPrime.card, Nat.reducePow] using hd
  let := hs
  let : IsQuasisimple (E ⧸ pCore 2 E) := hi.quasisimple
  let : IsSimpleGroup Q := es.symm.isSimpleGroup
  let : IsQuasisimple Q := IsQuasisimple.of_mulEquiv es
  have hzQ : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) inferInstance with hz | hz
    · exact hz
    · let := center_eq_top_iff.mp hz
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  have hG2 (e : RadicalExclusions.ModelReduction.starImage E (F.H.pCoreIn 2) E ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
    obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_automorphism_restrictions
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      G₀ hJG hGC hf
    let := hn
    obtain ⟨_,hinner,hodd,hres⟩ := hb
    exact Atlas.G2.BinaryLocalResidual.no_odd_index_heisenberg
      ((eqQ B hB).trans (es.trans e)) _ hinner _ hodd hres
  refine ⟨E,hE,hnE,hLE,hs,hi,?_⟩
  cases hm with
  | linearTwo k e =>
    exact (Matrix.SL2.no_heisenberg_automorphism_action
      ((MulAut.congr e).toMonoidHom.comp a) ((MulAut.congr e).injective.comp ha)).elim
  | linearThree k e =>
    have hz : center SL(3,k.Carrier) = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      have hh := (centerCongr e.symm ⟨z,hz⟩).property
      change e.symm z ∈ center Q at hh
      rw [hzQ,mem_bot] at hh
      exact mem_bot.mpr (e.symm.map_eq_one_iff.mp hh)
    exact (Matrix.SL3.no_heisenberg_automorphism_action k.degree_pos k.card_eq hz
      ((MulAut.congr e).toMonoidHom.comp a) ((MulAut.congr e).injective.comp ha)).elim
  | symplectic k large e => exact ⟨k,large,Or.inl ⟨es.trans e⟩⟩
  | g2 k large e => exact ⟨k,large,Or.inr ⟨es.trans e⟩⟩
  | g2DerivedTwo e => exact (hG2 e).elim
  | alternating n hn e =>
    rw [Nat.card_congr (MulAut.congr e).toEquiv] at h27
    exact (HeisenbergPrime.SmallAutomorphismExclusions.alternating_not_three_cube hn h27).elim
  | linearFiveTwo e =>
    rw [Nat.card_congr (MulAut.congr e).toEquiv] at h27
    exact (HeisenbergPrime.SmallAutomorphismExclusions.binary_five_not_three_cube h27).elim
  | tripleSix ez _ =>
    have hc : Nat.card (center Q) = 3 := by
      rw [Nat.card_congr ez.toEquiv]
      simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
    rw [hzQ,card_bot] at hc
    omega

/-- The actual local image is solvable of odd index, contains the original faithful
Heisenberg action, and retains the ambient three-rank bound. -/
theorem extraspecial_four_characteristicTwo_local_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    ∃ B : Subgroup G₀, B.IsCComponent ∧ ∃ hn : B.Normal,
      letI := hn
      let a := normalQuotientAction B (pCore 2 B)
      let J := ((F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀).map a.rangeRestrict
      primeRank 3 a.range ≤ 2 ∧ Group.IsSolvable J ∧
      MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range ∧ Odd J.index ∧
      ∃ f : HeisenbergPrime 3 →* a.range, Function.Injective f ∧ ∀ y, f y ∈ J := by
  obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_automorphism_restrictions
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  let := hn
  obtain ⟨hk,hi,ho,⟨er⟩⟩ := hb
  let a := normalQuotientAction B (pCore 2 B)
  let J := ((F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀).map a.rangeRestrict
  have hr : primeRank 3 a.range ≤ 2 := by
    rw [←primeRank_equiv 3 (QuotientGroup.quotientKerEquivRange a)]
    have hC := (extraspecial_four_centralizer_source_setup
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) a.ker
      (hk.symm ▸ pCore_isPGroup)).trans
        ((_root_.primeRank_le_of_injective 3 (inclusion hGC) (inclusion_injective hGC)).trans
          (hC.stronglyQuasithin 3 (by decide) (by decide)))
  have hs : Group.IsSolvable J := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact Or.inl h2
    · have hh := odd_prime_dvd_twoCore_quotient_residual hp (Nat.odd_iff.mpr hodd) hd
      rw [Nat.card_congr er.toEquiv,HeisenbergPrime.card] at hh
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hp.dvd_of_dvd_pow hh)).resolve_left hp.ne_one)
  refine ⟨B,hB,hn,hr,hs,hi,ho,?_⟩
  obtain ⟨Y,hYK,_,_,⟨e⟩,_,_⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hkk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hkk)
  have hYJ : Y ≤ F.H ⊓ centralizer ({x} : Set G) := hYK.trans (le_inf (K_le_H F) hKC)
  have hYG : Y ≤ G₀ := hYJ.trans hJG.le
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 3)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hcop : Nat.Coprime 3 (Nat.card a.ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G₀)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hinj : Function.Injective (a.comp (inclusion hYG)) :=
    (injective_comp_subtype_of_coprime_ker a hcop (Y.subgroupOf G₀) hYp.comap_subtype).comp
      (subgroupOfEquivOfLe hYG).symm.injective
  let f := (a.rangeRestrict.comp (inclusion hYG)).comp e.symm.toMonoidHom
  refine ⟨f,?_,?_⟩
  · intro y z hh
    exact e.symm.injective (hinj (congrArg Subtype.val hh))
  · intro y
    exact ⟨inclusion hYG (e.symm y),hYJ (e.symm y).property,rfl⟩

private theorem ExtraspecialFourCatalogue_transport_rankTwo_exclusion
    {Q W : Type*} [Group Q] [Finite Q] [Group W] [Finite W] (e : Q ≃* W)
    (exclude : ∀ (A : Subgroup (MulAut W)), MulAut.innerSubgroup W ≤ A →
      primeRank 3 A ≤ 2 → ∀ J : Subgroup A, Group.IsSolvable J → Odd J.index →
      ∀ f : HeisenbergPrime 3 →* A, Function.Injective f → (∀ y, f y ∈ J) → False)
    (A : Subgroup (MulAut Q)) (hA : MulAut.innerSubgroup Q ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) (hs : Group.IsSolvable J) (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  let ea := MulAut.congr e
  let A' := A.map ea.toMonoidHom
  let eA : A ≃* A' := ea.subgroupMap A
  let J' := J.map eA.toMonoidHom
  have hA' : MulAut.innerSubgroup W ≤ A' := by
    rw [←MulAut.map_innerSubgroup_congr e]
    exact map_mono hA
  have hr' : primeRank 3 A' ≤ 2 := (primeRank_equiv 3 eA).symm ▸ hr
  let := hs
  have hs' : Group.IsSolvable J' := Group.isSolvable_of_surjective
    (eA.toMonoidHom.subgroupMap_surjective J)
  have ho' : Odd J'.index := (index_map_of_bijective (f := eA.toMonoidHom) eA.bijective J).symm ▸ ho
  exact exclude A' hA' hr' J' hs' ho' (eA.toMonoidHom.comp f) (eA.injective.comp hf)
    (fun y => mem_map_of_mem _ (hJ y))

/-- No strict overgroup of the original local intersection inside the outside
centralizer has generalized Fitting subgroup equal to its two-core. -/
theorem extraspecial_four_overgroup_not_characteristicTwo
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    :
    generalizedFitting G₀ ≠ pCore 2 G₀ := by
  intro hf
  obtain ⟨E,hE,_,_,_,_,k,hk,hm⟩ := extraspecial_four_characteristicTwo_lie_model
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  obtain ⟨B,hB,hn,hb⟩ := extraspecial_four_characteristicTwo_local_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  let := hn
  obtain ⟨hr,hs,hi,ho,f,hinj,hfJ⟩ := hb
  obtain ⟨B₀,_,_,_,hu,_,_,_⟩ := extraspecial_four_characteristicTwo_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hf
  have hBE : B = E.subgroupOf G₀ := (hu B hB).trans (hu _ hE.2).symm
  let eB : B ≃* E := (MulEquiv.subgroupCongr hBE).trans (subgroupOfEquivOfLe hE.1)
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  have hq : 2 < Nat.card k.Carrier := by
    rw [k.card_eq]
    exact (show 2 = 2^1 by norm_num) ▸ Nat.pow_lt_pow_right (by decide : 1 < 2) hk
  rcases hm with hsymp | hg2
  · obtain ⟨e⟩ := hsymp
    apply ExtraspecialFourCatalogue_transport_rankTwo_exclusion (eQ.trans e) _ _ hi hr _ hs ho f hinj hfJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.symplectic k.card_eq k.degree_pos hq
      A hA hr J ho f hf hJ
  · obtain ⟨e⟩ := hg2
    apply ExtraspecialFourCatalogue_transport_rankTwo_exclusion (eQ.trans e) _ _ hi hr _ hs ho f hinj hfJ
    intro A hA hr J hs ho f hf hJ
    let := hs
    exact HeisenbergPrime.BinaryRankTwoExclusions.g2 hq A hA hr J ho f hf hJ

/-- An escaping original involution centralizer has an ordinary component,
with the full 1.1.5 marking, without any characteristic-two branch assumption. -/
theorem extraspecial_four_ordinary_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      Chapter15.Section03.Candidates.ComponentStructure.HasModelAction115 B z := by
  have hstrict : F.H ⊓ centralizer ({x} : Set G) < centralizer ({x} : Set G) :=
    lt_of_le_of_ne inf_le_right (fun heq => hout (heq ▸ inf_le_left))
  exact extraspecial_four_ordinary_component_source
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    (extraspecial_four_overgroup_not_characteristicTwo
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
      _ hstrict le_rfl)

/-- The original local intersection has no proper characteristic-two overgroup
inside the involution centralizer: the maximality assertion (*) on p.1053. -/
theorem extraspecial_four_characteristicTwo_overgroup_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hf : generalizedFitting G₀ = pCore 2 G₀) :
    G₀ = F.H ⊓ centralizer ({x} : Set G) := by
  by_contra hne
  have hlt := lt_of_le_of_ne hJG (Ne.symm hne)
  have hout : ¬ centralizer ({x} : Set G) ≤ F.H := by
    intro hCH
    exact hlt.not_ge (le_inf (hGC.trans hCH) hGC)
  exact extraspecial_four_overgroup_not_characteristicTwo
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hlt hGC hf

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Ordinary components in the extraspecial four-group centralizer

For every strict overgroup of H ∩ C_G(x) inside C_G(x), the original
U = [U,K] centralizes its odd core. The marked involution then places that
core in H, where the subnormal-subgroup reduction forces it into O₂.
Thus the odd core vanishes. A solvable such overgroup would have
F* = O₂, contrary to the proved characteristic-two maximality.

A Suzuki component produces a solvable Borel extension of the original
intersection. Its odd torus has order 2^(2m+1)-1, impossible in the
{2,3}-group H. Every ordinary component therefore has order divisible by
three. It is normal and contains L₁; its centralizer normalizes L₁ and
hence lies in H, so the same subnormal reduction identifies that
centralizer with the actual O₂(C_G(x)). Perfectness lifts centralizers
through the two-core quotient.

The literal quotient action consequently has exactly that two-core as
kernel. Its image contains the inner group and the original faithful
Heisenberg subgroup; the local image is solvable of odd index and retains
its Heisenberg residual. The alternating rows of 1.1.5 are impossible:
the triple covers conflict with the two-primary center, and the simple
rows have no faithful ternary Heisenberg automorphisms. Hence the original
marked involution acts by an inner automorphism of the ordinary component.
The final theorem applies this chain to the original escaping centralizer.

The remaining inner-action model exclusions, centralizer containment, TI
and subsequent reductions through 14.7.52 are not asserted here.
Source: Aschbacher–Smith, 14.7.26, printed p.1053, refs/quasithin.pdf;
1.1.5(3), printed pp.501–503, for the actual model/action alternatives.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
private theorem ExtraspecialFourOrdinary_extraspecial_H_prime_divisor
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card F.H) : r = 2 ∨ r = 3 := by
  have two_prime {A : Type u} [Group A] [Finite A] (hA : IsPGroup 2 A)
      (hdA : r ∣ Nat.card A) : r = 2 := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn] at hdA
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hdA)).resolve_left hr.ne_one
  have hcH := (pResidual 2 F.H).card_mul_index
  rw [←hcH] at hd
  rcases hr.dvd_mul.mp hd with hR | hQ
  · have hK : r ∣ Nat.card (K F) := by
      change r ∣ Nat.card ((pResidual 2 F.H).map F.H.subtype)
      rw [card_map_of_injective F.H.subtype_injective]
      exact hR
    have hcK := (pCore 2 (K F)).card_mul_index
    rw [←hcK] at hK
    rcases hr.dvd_mul.mp hK with hcore | hquot
    · exact Or.inl (two_prime (pCore_isPGroup (p := 2) (G := K F)) hcore)
    · obtain ⟨e⟩ := he
      change r ∣ Nat.card ((K F) ⧸ pCore 2 (K F)) at hquot
      rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card] at hquot
      exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp
        (hr.dvd_of_dvd_pow hquot)).resolve_left hr.ne_one)
  · change r ∣ Nat.card (F.H ⧸ pResidual 2 F.H) at hQ
    exact Or.inl (two_prime (isPGroup_quotient_pResidual (G := F.H) 2) hQ)


/-- The actual odd core vanishes in every strict overgroup of the original local intersection inside the involution centralizer. -/
theorem extraspecial_four_overgroup_oddCore_eq_bot
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    : pPrimeCore 2 G₀ = ⊥ := by
  let C := centralizer ({x} : Set G)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨hC,_,z,hzo,hzpow,P,hP,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hKG : K F ≤ G₀ := (le_inf (K_le_H F) hKC).trans hJG.le
  have hUG : F.U ≤ G₀ :=
    ((span_le_residual_core h hab).trans (pCoreIn_le 2 (K F))).trans hKG
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hC.subgroup (G₀.subgroupOf C))
  let : IsElementaryAbelian 2 (F.U.subgroupOf G₀) := IsElementaryAbelian.subgroupOf hUG
  have hp : IsPPerfect 2 ((K F).subgroupOf G₀) := (K_twoPerfect F).of_surjective
    (subgroupOfEquivOfLe hKG).symm.toMonoidHom (subgroupOfEquivOfLe hKG).symm.surjective
  have hcomm : ⁅F.U.subgroupOf G₀,(K F).subgroupOf G₀⁆ = F.U.subgroupOf G₀ := by
    apply map_injective G₀.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUG,map_subgroupOf_eq_of_le hKG,commutator_U h F]
  have hcent := commutator_eq_bot_iff_le_centralizer.mp
    (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hG.stronglyQuasithin
      ((K F).subgroupOf G₀) (F.U.subgroupOf G₀) hp hcomm)
  have hzU : z ∈ F.U := ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (hzpow ▸ mem_zpowers z)
  have hNH : (pPrimeCore 2 G₀).map G₀.subtype ≤ F.H := by
    rintro _ ⟨r,hr,rfl⟩
    have hcentral : z * (r : G) = (r : G) * z :=
      (congrArg Subtype.val (hcent (show (⟨z,hUG hzU⟩ : G₀) ∈ F.U.subgroupOf G₀ from hzU) r hr)).symm
    exact h115.centralizer_le (mem_centralizer_singleton_iff.mpr hcentral.symm)
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC
  have hle : pPrimeCore 2 G₀ ≤ pCore 2 G₀ :=
    le_twoCore_of_subnormal_two_three h3 _
      (inferInstance : (pPrimeCore 2 G₀).Normal).isSubnormal (by
        intro p hp hd
        exact ExtraspecialFourOrdinary_extraspecial_H_prime_divisor he hp (hd.trans (card_dvd_of_injective
          ((inclusion hNH).comp ((pPrimeCore 2 G₀).equivMapOfInjective G₀.subtype
            G₀.subtype_injective).toMonoidHom)
          ((inclusion_injective hNH).comp
            ((pPrimeCore 2 G₀).equivMapOfInjective G₀.subtype G₀.subtype_injective).injective))))
  have hp2 : IsPGroup 2 (pPrimeCore 2 G₀) := pCore_isPGroup.to_le hle
  rcases hp2.card_eq_or_dvd with h1 | hd
  · exact (eq_bot_iff_card _).mpr h1
  · exact ((Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) hd).elim

/-- The original local intersection is maximal among solvable subgroups of the involution centralizer. -/
theorem extraspecial_four_solvable_overgroup_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hs : Group.IsSolvable G₀) : G₀ = F.H ⊓ centralizer ({x} : Set G) := by
  by_contra hne
  have hlt := lt_of_le_of_ne hJG (Ne.symm hne)
  have hout : ¬ centralizer ({x} : Set G) ≤ F.H := by
    intro hCH
    exact hlt.not_ge (le_inf (hGC.trans hCH) hGC)
  have ho := extraspecial_four_overgroup_oddCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hlt hGC
  let := hs
  have hf : generalizedFitting G₀ = pCore 2 G₀ :=
    (generalizedFitting_eq_fitting_of_solvable G₀).trans (Fitting_eq_pcore G₀ 2 ho)
  exact extraspecial_four_overgroup_not_characteristicTwo
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hlt hGC hf

/-- The literal Suzuki Borel extension contradicts solvable maximality of the original intersection. -/
theorem extraspecial_four_not_suzuki_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    {m : ℕ} (hm : 0 < m)
    (e : B ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let C := centralizer ({x} : Set G)
  let M := F.H.subgroupOf C
  obtain ⟨_,_,_,_,_,P,hP,_⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hPM : (P : Subgroup C) ≤ M := by
    intro a ha
    have hh : (a : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem C.subtype ha
    exact F.invariant 1 hh.1
  have hsol : Group.IsSolvable F.H := isSolvable_of_prime_dvd_card_eq_two_or_three F.H
    (fun p hp hd => ExtraspecialFourOrdinary_extraspecial_H_prime_divisor he hp hd)
  let := hsol
  let f : M →* F.H := (C.subtype.comp M.subtype).codRestrict F.H (fun a => a.property)
  have hf : Function.Injective f := by
    intro a b hh
    exact Subtype.ext (Subtype.ext (show ((a : C) : G) = ((b : C) : G) from
      congrArg (fun y : F.H => (y : G)) hh))
  have hMsol : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective hf
  obtain ⟨A,hMA,hAs,hd⟩ := Chapter14.Section06.OddNormalizer.suzuki_component_solvable_extension
    P M B hPM hMsol hB.isCComponent hm e
  let G₀ := A.map C.subtype
  have hJG : F.H ⊓ C ≤ G₀ := by
    intro a ha
    exact ⟨⟨a,ha.2⟩,hMA ha.1,rfl⟩
  let := hAs
  have heq : G₀ = F.H ⊓ C := extraspecial_four_solvable_overgroup_eq
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ
    G₀ hJG (map_subtype_le A) (Group.isSolvable_of_surjective (C.subtype.subgroupMap_surjective A))
  have hdiv : 2 ^ (2*m+1) - 1 ∣ Nat.card F.H := by
    have hc : Nat.card A = Nat.card G₀ := (card_map_of_injective C.subtype_injective).symm
    exact (hc ▸ hd).trans (card_dvd_of_le (heq.le.trans inf_le_left))
  have hq : 8 ≤ 2 ^ (2*m+1) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ 2*m+1)
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ (2*m+1) - 1 ≠ 1 by omega)
  rcases ExtraspecialFourOrdinary_extraspecial_H_prime_divisor he hp (hpd.trans hdiv) with rfl | rfl
  · have hmod : 2 ^ (2*m+1) % 2 = 0 := by simp [pow_add]
    have hmod' := Nat.mod_eq_zero_of_dvd hpd
    omega
  · have hmod : 2 ^ (2*m+1) % 3 = 2 := by
      simp [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    have hmod' := Nat.mod_eq_zero_of_dvd hpd
    omega

/-- Every ordinary component of the original centralizer has order divisible by three. -/
theorem extraspecial_four_ordinary_three_dvd
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) : 3 ∣ Nat.card B := by
  obtain ⟨_,_,z,_,_,P,_,h115⟩ := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  obtain ⟨_,_,α,_,hmodel⟩ := Chapter1.lemma_1_1_5_three_knownSimple d.qtke
    (centralizer ({x} : Set G)) P F.H z h115 B hB
  rcases Chapter15.Section03.Candidates.SuzukiExclusion.ModelThreeDivisibility.suzuki_or_three_dvd
      α hmodel with ⟨m,hm,⟨e⟩⟩ | hd
  · exact (extraspecial_four_not_suzuki_component
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ B hB hm e).elim
  · exact hd

/-- The ordinary component is normal, contains the original L₁, and has exactly O₂(C_G(x)) as centralizer. Its literal two-core quotient has trivial centralizer in C_G(x)/O₂(C_G(x)). -/
theorem extraspecial_four_ordinary_structure
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    B.Normal ∧ F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      centralizer (B : Set (centralizer ({x} : Set G))) = pCore 2 (centralizer ({x} : Set G)) ∧
      center B = pCore 2 B ∧ IsSimpleGroup (B ⧸ pCore 2 B) ∧
      centralizer (B.map (QuotientGroup.mk' (pCore 2 (centralizer ({x} : Set G)))) :
        Set ((centralizer ({x} : Set G)) ⧸ pCore 2 (centralizer ({x} : Set G)))) = ⊥ := by
  let C := centralizer ({x} : Set G)
  have hstrict : F.H ⊓ C < C :=
    lt_of_le_of_ne inf_le_right (fun heq => hout (heq.symm.trans_le inf_le_left))
  have hd := extraspecial_four_ordinary_three_dvd
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ B hB
  have hnormal : B.Normal := extraspecial_four_component_normal
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    C hstrict le_rfl B hB.isCComponent hd
  let := hnormal
  have hLB := extraspecial_four_component_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    C inf_le_right le_rfl B hB.isCComponent hd
  have hNK := (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have hNpoint : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans hNK
  let Z := centralizer (B : Set C)
  have hZH : Z.map C.subtype ≤ F.H := by
    rintro _ ⟨c,hc,rfl⟩
    rw [←hNpoint]
    apply Subgroup.centralizer_le_normalizer (F.Li L 1 : Set G)
    intro l hl
    obtain ⟨b,hb,rfl⟩ := hLB hl
    exact congrArg Subtype.val (hc b hb)
  have h3 := extraspecial_four_threeCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    C hstrict le_rfl
  have hZle : Z ≤ pCore 2 C := le_twoCore_of_subnormal_two_three h3 Z
    (inferInstance : Z.Normal).isSubnormal (by
      intro p hp hpZ
      have hd : p ∣ Nat.card (Z.map C.subtype) := by
        rwa [card_map_of_injective C.subtype_injective]
      exact ExtraspecialFourOrdinary_extraspecial_H_prime_divisor he hp (hd.trans (card_dvd_of_le hZH)))
  let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
  have hCle : pCore 2 C ≤ Z := le_centralizer_iff.mp
    (hB.le_centralizer_of_solvable_normal (pCore 2 C))
  have hZ : Z = pCore 2 C := le_antisymm hZle hCle
  let : IsQuasisimple B := hB.2
  have ho := extraspecial_four_oddCore_eq_bot
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hz : center B = pCore 2 B := IsQuasisimple.center_eq_pCore (hB.1.pPrimeCore_eq_bot ho)
  have hs : IsSimpleGroup (B ⧸ pCore 2 B) := by
    let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    exact (QuotientGroup.quotientMulEquivOfEq hz.symm).isSimpleGroup
  refine ⟨hnormal,hLB,hZ,hz,hs,?_⟩
  let q := QuotientGroup.mk' (pCore 2 C)
  apply (comap_injective (QuotientGroup.mk'_surjective (pCore 2 C)))
  rw [comap_centralizer_map_eq_of_perfect q B (by
    rw [QuotientGroup.ker_mk']; exact hCle)]
  change Z = q.ker
  rw [QuotientGroup.ker_mk']
  exact hZ

/-- The literal action of C_G(x) on the surviving ordinary component quotient has exactly the two-core as kernel. The original local image is solvable of odd index, with its marked Heisenberg residual and faithful original Heisenberg subgroup. -/
theorem extraspecial_four_ordinary_action
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B) :
    ∃ hn : B.Normal, letI := hn
      let a := normalQuotientAction B (pCore 2 B)
      let M := (F.H ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))
      let J := M.map a.rangeRestrict
      a.ker = pCore 2 (centralizer ({x} : Set G)) ∧
        MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range ∧
        primeRank 3 a.range ≤ 2 ∧ Group.IsSolvable J ∧ Odd J.index ∧
        Nonempty (pResidual 2 (J ⧸ pCore 2 J) ≃* HeisenbergPrime 3) ∧
        ∃ f : HeisenbergPrime 3 →* a.range, Function.Injective f ∧ ∀ y, f y ∈ J := by
  have hsB := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  have hn : B.Normal := hsB.1
  let := hn
  refine ⟨hn,?_⟩
  let C := centralizer ({x} : Set G)
  let H₀ := F.H ⊓ C
  let M := H₀.subgroupOf C
  let a := normalQuotientAction B (pCore 2 B)
  let J := M.map a.rangeRestrict
  have hk : a.ker = pCore 2 C := hB.isCComponent.normalQuotientAction_ker_of_centralizer_eq_bot hsB.2.2.2.2.2
  have setup := extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hC := setup.1
  have hz := setup.2.2.choose_spec
  let P := hz.2.2.choose
  have hP := hz.2.2.choose_spec.1
  have hi : MulAut.innerSubgroup (B ⧸ pCore 2 B) ≤ a.range := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
    exact ⟨b,normalQuotientAction_inner B (pCore 2 B) b⟩
  have hr : primeRank 3 a.range ≤ 2 := by
    rw [←primeRank_equiv 3 (QuotientGroup.quotientKerEquivRange a)]
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) a.ker
      (hk.symm ▸ pCore_isPGroup)).trans (hC.stronglyQuasithin 3 (by decide) (by decide))
  have hsol : Group.IsSolvable F.H := isSolvable_of_prime_dvd_card_eq_two_or_three F.H
    (fun p hp hd => ExtraspecialFourOrdinary_extraspecial_H_prime_divisor he hp hd)
  let := hsol
  let φ : M →* F.H := (C.subtype.comp M.subtype).codRestrict F.H (fun y => y.property.1)
  have hφ : Function.Injective φ := by
    intro y z hh
    exact Subtype.ext (Subtype.ext (show ((y : C) : G) = ((z : C) : G) from
      congrArg (fun w : F.H => (w : G)) hh))
  let : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective hφ
  have hs : Group.IsSolvable J := Group.isSolvable_of_surjective (a.rangeRestrict.subgroupMap_surjective M)
  have hPM : (P : Subgroup C) ≤ M := by
    intro y hy
    have hh : (y : G) ∈ (T : Subgroup G) ⊓ C := hP ▸ mem_map_of_mem C.subtype hy
    exact ⟨F.invariant 1 hh.1,hh.2⟩
  have hodd : Odd M.index := Nat.not_even_iff_odd.mp (fun heven =>
    P.not_dvd_index (((even_iff_two_dvd).mp heven).trans (index_dvd_of_le hPM)))
  have ho : Odd J.index := hodd.of_dvd_nat (M.index_map_dvd a.rangeRestrict_surjective)
  have hres : Nonempty (pResidual 2 (J ⧸ pCore 2 J) ≃* HeisenbergPrime 3) := by
    let f : H₀ →* J := (a.rangeRestrict.subgroupMap M).comp
      (subgroupOfEquivOfLe (show H₀ ≤ C from inf_le_right)).symm.toMonoidHom
    have hf : Function.Surjective f := (a.rangeRestrict.subgroupMap_surjective M).comp
      (subgroupOfEquivOfLe (show H₀ ≤ C from inf_le_right)).symm.surjective
    have hkf : f.ker = (pCore 2 C).comap (inclusion (show H₀ ≤ C from inf_le_right)) := by
      ext j
      change f j = 1 ↔ inclusion (show H₀ ≤ C from inf_le_right) j ∈ pCore 2 C
      rw [Subtype.ext_iff,Subtype.ext_iff]
      change inclusion (show H₀ ≤ C from inf_le_right) j ∈ a.ker ↔ _
      rw [hk]
    have hpf : IsPGroup 2 f.ker := by
      rw [hkf]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective inf_le_right)
    exact extraspecial_four_image_residual he hDK hx f hf hpf
  refine ⟨hk,hi,hr,hs,ho,hres,?_⟩
  have hY := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  let Y := hY.choose
  have hYK := hY.choose_spec.1
  let e := Classical.choice hY.choose_spec.2.2.2.1
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hkk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hkk)
  have hYH : Y ≤ H₀ := hYK.trans (le_inf (K_le_H F) hKC)
  have hYC : Y ≤ C := hYH.trans inf_le_right
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 3)
    ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hcop : Nat.Coprime 3 (Nat.card a.ker) := by
    rw [hk]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hinj : Function.Injective (a.comp (inclusion hYC)) :=
    (injective_comp_subtype_of_coprime_ker a hcop (Y.subgroupOf C) hYp.comap_subtype).comp
      (subgroupOfEquivOfLe hYC).symm.injective
  let f := (a.rangeRestrict.comp (inclusion hYC)).comp e.symm.toMonoidHom
  refine ⟨f,?_,?_⟩
  · intro y z hh
    exact e.symm.injective (hinj (congrArg Subtype.val hh))
  · intro y
    exact ⟨inclusion hYC (e.symm y),hYH (e.symm y).property,rfl⟩

private theorem ExtraspecialFourOrdinary_ordinary_alternating_false
    {A : Type*} [Group A] [Finite A]
    (hc : center A = pCore 2 A) {α : MulAut A} {n : ℕ}
    (hn : n = 6 ∨ n = 7) (σ : Equiv.Perm (Fin n))
    (ha : Chapter15.Section03.Candidates.ComponentStructure.AlternatingAction α n σ)
    (f : HeisenbergPrime 3 →* MulAut (A ⧸ pCore 2 A)) (hf : Function.Injective f) : False := by
  rcases ha with ⟨e,_⟩ | ⟨_,⟨ez⟩,_,_⟩
  · have hn4 : 4 ≤ Nat.card (Fin n) := by simp only [Nat.card_fin]; omega
    have hzA : center (alternatingGroup (Fin n)) = ⊥ :=
      alternatingGroup.center_eq_bot hn4
    have hz : center A = ⊥ := (eq_bot_iff_card _).mpr (by
      rw [Nat.card_congr (centerCongr e).toEquiv,hzA,card_bot])
    let eQ : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientMulEquivOfEq (hc.symm.trans hz)).trans (QuotientGroup.quotientBot.trans e)
    exact HeisenbergPrime.SmallAutomorphismExclusions.no_alternating_action
      (by omega) eQ f hf
  · have hcard : Nat.card (pCore 2 A) = 3 := by
      rw [←hc,Nat.card_congr ez.toEquiv]
      simp only [Nat.card_eq_fintype_card,Fintype.card_multiplicative,ZMod.card]
    rcases (pCore_isPGroup (p := 2) (G := A)).card_eq_or_dvd with he | hd
    · omega
    · rw [hcard] at hd
      norm_num at hd

/-- The two alternating-action rows of 1.1.5 are impossible on the original component. Every surviving marked involution action is inner. -/
theorem extraspecial_four_ordinary_inner
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (B : Subgroup (centralizer ({x} : Set G)))
    (hB : IsComponent (centralizer ({x} : Set G)) B)
    (z : G) (hm : Chapter15.Section03.Candidates.ComponentStructure.HasModelAction115 B z) :
    ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
      α ∈ (MulAut.conj (G := B)).range ∧
      Chapter15.Section03.Candidates.ComponentStructure.ModelAction115 B α := by
  obtain ⟨_,_,_,hz,_,_⟩ := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  obtain ⟨hn,ha⟩ := extraspecial_four_ordinary_action
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  let := hn
  obtain ⟨_,_,_,_,_,_,f,hf,_⟩ := ha
  let f' := (normalQuotientAction B (pCore 2 B)).range.subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  obtain ⟨α,hα,hmodel⟩ := hm
  have hi : α ∈ (MulAut.conj (G := B)).range := by
    cases hmodel with
    | lie _ _ hi => exact hi
    | two_cover _ _ _ hi => exact hi
    | six σ _ a => exact (ExtraspecialFourOrdinary_ordinary_alternating_false hz (Or.inl rfl) σ a f' hf').elim
    | seven σ _ a => exact (ExtraspecialFourOrdinary_ordinary_alternating_false hz (Or.inr rfl) σ a f' hf').elim
    | odd _ hi => exact hi
    | sporadic _ _ _ hi => exact hi.1
  exact ⟨α,hα,hi,hmodel⟩

/-- Application to the original escaping centralizer: the marked ordinary component is normal, contains L₁, and its actual z-action is inner. -/
theorem extraspecial_four_ordinary_inner_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    : ∃ (B : Subgroup (centralizer ({x} : Set G))) (z : G),
      IsComponent (centralizer ({x} : Set G)) B ∧ B.Normal ∧
      F.Li L 1 ≤ B.map (centralizer ({x} : Set G)).subtype ∧
      orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
      B.map (centralizer ({x} : Set G)).subtype =
        ⁅B.map (centralizer ({x} : Set G)).subtype,zpowers z⁆ ∧
      ¬ B.map (centralizer ({x} : Set G)).subtype ≤ F.H ∧
      ∃ α : MulAut B, (∀ y : B, ((α y : centralizer ({x} : Set G)) : G) = z * (y : G) * z⁻¹) ∧
        α ∈ (MulAut.conj (G := B)).range ∧
        Chapter15.Section03.Candidates.ComponentStructure.ModelAction115 B α := by
  obtain ⟨B,z,hB,hz,hzp,hm,houtB,hmodel⟩ := extraspecial_four_ordinary_component
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
  obtain ⟨hn,hLB,_,_,_,_⟩ := extraspecial_four_ordinary_structure
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB
  exact ⟨B,z,hB,hn,hLB,hz,hzp,hm,houtB,extraspecial_four_ordinary_inner
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout B hB z hmodel⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
