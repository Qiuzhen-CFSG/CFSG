module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOrdinary
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourComponents
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOuter
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOnePushingUpOrdinary
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl

/-!
# Actual J₄ component alternatives at the Hermitian extraspecial centers

The original Hermitian action supplies binary rank nine. In the ordinary
pushing-up branch the actual covering residual has no fixed points, so the
same nine-space embeds in the ordinary component's central quotient. The
field-four component sieves identify that quotient with the native J₄ model.
In the residual-uniqueness branch the original normal component also has
this quotient; its full centralizer is the full odd core. The actual inner
action identifies the whole odd normalizer modulo that odd core with J₄.

The tensor endpoint applies these results to every extraspecial Sylow center
on both original weak-closure branches. It retains the original Sylow,
four-space, residual kernel and SL₂(4) quotient, containing C-component,
H-star membership, full odd cores and escaping normalizers. No SQTK premise
on an odd normalizer or normalization callback is added. The J₄ local
exclusions, hence whole-normalizer control and original 8.2.7, remain open.
Source: Aschbacher--Smith 4.4.3 and Remark 4.4.2, with 4.4.11--12,
printed pp.619,621--623, applied in 8.2.7, printed p.718, refs/quasithin.pdf.
The proof-only imports reuse the existing internal residual and rank
transports without changing their public boundaries.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem sourceOrbit_hermitian_field_four_rank
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) : 9 ≤ primeRank 2 D.sourceOrbit := by
  have hh := D.sourceOrbit_rank_ge_of_finrank
    ((D.hermitianOrbitCoordinates 1 d).finrank_eq.trans (finrank_binary 1))
  simpa using hh

/-- The exact pushing-up residual and unchanged nine-space identify the
central quotient of every actual ordinary component. -/
theorem sourceOrbit_hermitian_field_four_ordinary_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  obtain ⟨hn,hcore,hfix,⟨es⟩⟩ := D.sourceOrbit_pushingUp_residual_data h hmany hV hnon hw
  obtain ⟨_,_,_,_,_,_,hc,_,_,_,hVF,⟨a,ha⟩,_⟩ := hw
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := h.toHypothesis1221.quasisimple
  let : IsQuasisimple (F ⧸ pCore 2 F) := IsQuasisimple.of_mulEquiv a.symm
  let J := K.map H.subtype
  have hFJ : F ≤ J := by
    intro f hf
    exact ⟨⟨f,hc.component_le.trans hc.local_le hf⟩,
      hc.ordinary_component_contains_original K hK hf,rfl⟩
  let e : J ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := QuotientGroup.congr (center J) (center K) e (FixedElementary.map_center e)
  have hr : 9 ≤ primeRank 2 (K ⧸ center K) := by
    rw [←primeRank_congr 2 z]
    exact (D.sourceOrbit_hermitian_field_four_rank d).trans
      (rank_le_central_quotient_of_fixed_eq_bot hFJ hVF hfix)
  exact field_four_ordinary_janko_four hc (by rw [B.card_eq,hfield]; decide)
    (es.trans eQ) K hK (by omega)

/-- The original C.2.8 witnesses, with the same ordinary component and
its actual J₄ central quotient. -/
@[expose] def HermitianPushingUpJankoCase (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K ∧
      W.subgroupOf H ≤ K ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model)

/-- The ordinary branch retains every original pushing-up witness. -/
theorem sourceOrbit_hermitian_field_four_pushingUp_janko_case
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A : Subgroup G} (hc : HermitianPushingUpOrdinaryCase L D.sourceOrbit A) :
    HermitianPushingUpJankoCase L D.sourceOrbit A := by
  obtain ⟨J,H,W,hJ,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hcomm,hVL,he,
    hcore,hrad,hsyl,hfit,hP,hsize,hVW,K,hK,hn,hout,hFK,hWK⟩ := hc
  have hw : Witness L D.sourceOrbit A J H W :=
    ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hC,hcover,hN,hcomm,hVL,he,
      hcore,hrad,hsyl,hfit,hP,hsize,hVW⟩
  exact ⟨J,H,W,hw,K,hK,hn,hout,hFK,hWK,
    D.sourceOrbit_hermitian_field_four_ordinary_janko h hmany hV hnon d B eQ hfield hw K hK⟩

private theorem normal_janko_odd_quotient
    {N : Type*} [Group N] (K : Subgroup N) [K.Normal] [Group.IsPerfect K]
    (hc : centralizer (K : Set N) = pPrimeCore 2 N)
    (e : (K ⧸ center K) ≃* Janko4.Model) :
    Nonempty ((N ⧸ pPrimeCore 2 N) ≃* Janko4.Model) := by
  let f := Janko4.perfectCoverAction K e
  have hk : f.ker = pPrimeCore 2 N := (Janko4.perfectCoverAction_ker K e).trans hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (Janko4.perfectCoverAction_surjective K e))⟩

/-- Residual uniqueness, the original normal-component witnesses and full
odd centralizer, with the actual remaining central quotient. -/
@[expose] def HermitianNormalJankoCase (L V A : Subgroup G) : Prop :=
  UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ⁅K,V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    pCore 2 K = ⊥ ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
    9 ≤ primeRank 2 (K ⧸ center K) ∧ Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
    Nonempty (((normalizer (A : Set G)) ⧸ pPrimeCore 2 (normalizer (A : Set G))) ≃* Janko4.Model)

/-- Residual uniqueness identifies the original normal component without
assuming the odd normalizer is an SQTK group. -/
theorem sourceOrbit_hermitian_field_four_normal_janko_case
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    HermitianNormalJankoCase L D.sourceOrbit A := by
  obtain ⟨K,hK,hn,hmove,houtK,hcore,hm,hv,hf,hcent,hrK,hsection⟩ :=
    D.sourceOrbit_hermitian_field_four_normal_component h hV d B eQ hfield A hne hA ho hu hout
  have hr := (D.sourceOrbit_hermitian_field_four_rank d).trans hrK
  have hsect := (le_sectionCentralizer_iff A L).mp
    (hA.trans (D.sourceOrbit_relative_centralizer_le_sectionCentralizer h hV))
  have hAV : A ≤ centralizer (V : Set G) := hV ▸ hA.trans inf_le_right
  obtain ⟨hcover,hcomm,hWF,_⟩ := chosen_oddActorResidual_cover h D A hsect.1 hsect.2 ho hAV
  rw [hV] at hcomm hWF
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  let J := K.map N.subtype
  let a : J ≃* K := (K.equivMapOfInjective N.subtype N.subtype_injective).symm
  let z := QuotientGroup.congr (center J) (center K) a (FixedElementary.map_center a)
  let es := Classical.choice (D.sourceOrbit_covering_central_quotient h
    ((oddActorResidual_le L A).trans inf_le_left) hcover.subset)
  let S := D.orbitComponent ⧸ center D.orbitComponent
  let := D.orbitComponent_quasisimple h
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let π := es.toMonoidHom.comp ((QuotientGroup.mk' (center (F ⧸ pCore 2 F))).comp
    (QuotientGroup.mk' (pCore 2 F)))
  have hπ : Function.Surjective π := es.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨ej⟩ := field_four_containing_component_janko_four F J D.sourceOrbit
    hf hWF (hV ▸ D.ne_bot) hcomm (Group.IsPerfect.not_isSolvable S) eQ
    (by rw [B.card_eq,hfield]; decide) π hπ
    (by rwa [primeRank_congr 2 z]) (hm.of_mulEquiv z)
  let := hn
  let := hK.2
  exact ⟨hu,K,hK,hn,hmove,houtK,hcore,hv,hf,hcent,hr,⟨z.symm.trans ej⟩,
    normal_janko_odd_quotient K hcent (z.symm.trans ej)⟩

/-- Both remaining branches for the actual odd actor have a J₄ component,
with their original ambient embeddings and full kernels retained. -/
theorem sourceOrbit_hermitian_field_four_oddActor_janko_cases
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    HermitianNormalJankoCase L D.sourceOrbit A ∨ HermitianPushingUpJankoCase L D.sourceOrbit A := by
  rcases D.sourceOrbit_hermitian_field_four_oddActor_alternatives h.toHypothesis1221 hV
    B eQ hfield A hA ho with hu | hc
  · exact Or.inl (D.sourceOrbit_hermitian_field_four_normal_janko_case h.toHypothesis1221
      hV d B eQ hfield A hne hA ho hu hout)
  · exact Or.inr (D.sourceOrbit_hermitian_field_four_pushingUp_janko_case
      h hmany hV hnon d B eQ hfield hc)

/-- The literal tensor identifies the remaining J₄ configurations for every actual center. -/
theorem sourceOrbit_hermitian_tensor_nilpotent_center_janko_cases
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 ∧
      ∃ U : Subgroup G, ∃ hU : IsElementaryAbelian 2 U, letI := hU
        U ≤ D.sourceOrbit ∧ rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        let R := Chapter8.Section02.Normalizer.localResidual L U
        R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          ¬ Chapter1.Section02.A36Natural (Chapter1.XiQuotient K) ∧
          (Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K) →
            ∀ (p : ℕ) (_ : Fact p.Prime),
              p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) →
              Chapter1.Section02.LocalModels.OddExtraspecialThree p
                (pCore p (Chapter1.XiQuotient K)) ∧
              IsExtraspecial p (Chapter1.XiQuotient (Chapter1.XiP p K)) ∧
              Nat.card (Chapter1.XiQuotient (Chapter1.XiP p K)) = p^3 ∧
              Monoid.exponent (Chapter1.XiQuotient (Chapter1.XiP p K)) = p ∧
              (Chapter1.XiP p K ⊔ (T : Subgroup G) ∈
                Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
                (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (R : Set G) =
                  (Chapter1.XiP p K ⊔ (T : Subgroup G)) ⊓ normalizer (L : Set G) ∧
                ∀ P : Sylow p (Chapter1.XiP p K),
                  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
                  let Z := (center Y).map Y.subtype
                  Nat.card Z = p ∧ IsCyclic Z ∧ Z ≠ ⊥ ∧
                    Z ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) ∧
                    ¬ normalizer (Z : Set G) ≤ normalizer (L : Set G) ∧
                    (pPrimeCore 2 (normalizer (Z : Set G))).map (normalizer (Z : Set G)).subtype ≤
                      normalizer (L : Set G) ∧
                    (HermitianNormalJankoCase L D.sourceOrbit Z ∨
                      HermitianPushingUpJankoCase L D.sourceOrbit Z))) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_nilpotent_centers
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  subst hn
  let := hU
  refine ⟨rfl,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,?_⟩
  intro hnil p hp hd
  let := hp
  obtain ⟨hfull,hx,hcard,hexp,hH,heq,hcenters⟩ := hcores hnil p hp hd
  have hgt := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  refine ⟨hfull,hx,hcard,hexp,hH,heq,?_⟩
  intro P
  obtain ⟨hc,hcyc,hne,hplaced,hout,hcore⟩ := hcenters P
  let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
  let Z := (center Y).map Y.subtype
  let : IsCyclic Z := hcyc
  let : CommGroup Z := IsCyclic.commGroup
  exact ⟨hc,hcyc,hne,hplaced,hout,hcore,
    D.sourceOrbit_hermitian_field_four_oddActor_janko_cases
      h hmany hV hnon d B eQ hB Z hne hplaced (by rwa [hc]) hout⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
