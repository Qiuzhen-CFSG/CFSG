module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationCenterThree
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanPermutability
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.NoncentralOddCore
public import Theory.GroupTheory.LocalSolvableCoreNormalizer

/-!
# The invariant normalizer residual in the original odd-core branch

Retain the chosen normal containing component J in the original tensor-line
normalizer, the old residual K=O²(H), and the exact intersection A ∩ J=B.
The actual Cartan–Sylow product AT=TA and original A₅ recognition supply
all inputs to the solvable-core normalizer theorem. For every solvable
characteristic R in J, K lies in N_J(T ∩ R)^∞ and A normalizes that residual.

In the noncentral odd-core branch, the proved A.3.6 quotient theorem supplies
F(I)=O(I) for the literal image I of J in the ambient two-core quotient.
Transport through the exact C-component quotient equivalence identifies
O_{2,2′,2}(J) with the solvable radical and discharges its solvability.
The final theorem constructs exactly the printed smaller residual, with no
A₅ recognition, product-permutability or invariant-residual callback.

Identifying its two-core quotient as PSL₂(p), and the subsequent rank-one
normalizer lift, remain separate mathematical steps.

Source: Aschbacher–Smith, Proposition 9.3.1, second reduction, printed
p.732 of the combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterA.Section03 ChapterE
open Theory.GroupTheory.LocalSolvableCoreNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Apply the literal Cartan–Sylow product and original A₅ recognition to a
solvable characteristic subgroup of the chosen containing component. -/
theorem cartan_invariant_solvable_core_normalizer_residual
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B J : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hAe : IsElementaryAbelian 3 A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hAJB : A ⊓ J = B)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (R : Subgroup J) [R.Characteristic] [Group.IsSolvable R] :
    (pResidual 2 H).map H.subtype ≤
      localNormalizerResidual J ((T : Subgroup G) ⊓ R.map J.subtype) ∧
    A ≤ normalizer (localNormalizerResidual J ((T : Subgroup G) ⊓ R.map J.subtype) : Set G) := by
  let := hAe
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  let K0 := (pResidual 2 H).map H.subtype
  let N := normalizer (m.tensorLine : Set G)
  let P := T.subtype m.tensorLine_normalized
  let K := K0.subgroupOf N
  let C := A.subgroupOf N
  let R0 := R.map J.subtype
  let S := R0.subgroupOf N
  let Q := (T : Subgroup G) ⊓ R0
  have hAU : A ≤ N := hAB.trans m.borel_normalizes_tensorLine
  have hKN : K0 ≤ N := hKJ.trans hJU
  have hQN : Q ≤ N := inf_le_left.trans m.tensorLine_normalized
  have hNJ : N ≤ normalizer (J : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hJU).mp hnJ
  have hNR : N ≤ normalizer (R0 : Set G) := hNJ.trans
    (normalizer_le_normalizer_characteristic_image J R)
  let : S.Normal := normal_subgroupOf_of_le_normalizer hNR
  let : Group.IsSolvable R0 := Group.isSolvable_of_surjective (J.subtype.subgroupMap_surjective R)
  let : Group.IsSolvable S := Group.isSolvable_of_isSolvable_injective
    (f := N.subtype.subgroupComap R0) (fun a b h => Subtype.ext (Subtype.ext
      (congrArg (fun x : R0 => (x : G)) h)))
  let k : K ≃* K0 := subgroupOfEquivOfLe hKN
  let : Group.IsPerfect K0 := Chapter1.mem_L_isPerfect (source_hstar_residual_mem_local_of_a5 hH eK)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := k.symm.toMonoidHom) k.symm.surjective
  let ek : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK
  let : IsSimpleGroup (K ⧸ pCore 2 K) := ek.isSimpleGroup
  have hPK : (P : Subgroup N) ≤ normalizer (K : Set N) := by
    rw [← subgroupOf_normalizer_eq hKN]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  have hCS : C ⊓ S ≤ K := by
    intro x hx
    apply hBK
    rw [←hAJB]
    exact ⟨hx.1,map_subtype_le R hx.2⟩
  have hp : (C : Set N) * (P : Set N) = (P : Set N) * (C : Set N) := by
    simpa only [map_id,C,P,Sylow.coe_coe] using m.cartan_sylow_image_permute A N hAB hA9 hAU
      m.tensorLine_normalized (MonoidHom.id N)
  obtain ⟨hAQ,hKQ⟩ := cartan_and_local_normalize_sylow_core P K C S hPK
    (IsElementaryAbelian.isPGroup 3 A).comap_subtype hCS hp
  have hQ : ((P : Subgroup N) ⊓ S) = Q.subgroupOf N := rfl
  rw [hQ,← subgroupOf_normalizer_eq hQN] at hAQ hKQ
  have hAQ0 : A ≤ normalizer (Q : Set G) := fun a ha => hAQ (show (⟨a,hAU ha⟩ : N) ∈ C from ha)
  have hKQ0 : K0 ≤ normalizer (Q : Set G) := fun k hk => hKQ (show (⟨k,hKN hk⟩ : N) ∈ K from hk)
  refine ⟨le_map_solvableResidual_of_isPerfect K0 _ (le_inf hKJ hKQ0),?_⟩
  exact ((le_inf (hAU.trans hNJ) (hAQ0.trans (normalizer _).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))

/-- In the actual noncentral odd-core branch, construct the printed
A-invariant N_J(T ∩ O_{2,2′,2}(J))^∞ containing the old residual. -/
theorem cartan_invariant_oddCore_normalizer_residual
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B J : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A = 9)
    (hAe : IsElementaryAbelian 3 A)
    (hBK : B ≤ (pResidual 2 H).map H.subtype) (hAJB : A ⊓ J = B)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hn : let N := normalizer (m.tensorLine : Set G)
      let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      ¬ fittingSubgroup I ≤ center I) :
    twoOddTwoCore J = solvableRadical J ∧
    (pResidual 2 H).map H.subtype ≤
      localNormalizerResidual J ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype) ∧
    A ≤ normalizer (localNormalizerResidual J
      ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype) : Set G) := by
  let N := normalizer (m.tensorLine : Set G)
  let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  have hq : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  let := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
  have hFO := NoncentralFitting.noncentral_fitting_quotient_consequences
    ChapterA.RankActions.primeSL2CoverRigidity hq (pCore_quotient_pCore_eq_bot 2)
    (hJ.map_quotient (pCore 2 N)) hn
  let : Group.IsSolvable (pPrimeCore 2 I) := hFO.1 ▸ inferInstanceAs (Group.IsSolvable (fittingSubgroup I))
  let j : J.subgroupOf N ≃* J := subgroupOfEquivOfLe hJU
  let ej : (J ⧸ pCore 2 J) ≃* I :=
    (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans (cComponentTwoCoreQuotientEquiv hJ)
  let o : pPrimeCore 2 (J ⧸ pCore 2 J) ≃* pPrimeCore 2 I :=
    ((pPrimeCore 2 (J ⧸ pCore 2 J)).equivMapOfInjective ej.toMonoidHom ej.injective).trans
      (MulEquiv.subgroupCongr (pPrimeCore_map_iso 2 ej))
  let : Group.IsSolvable (pPrimeCore 2 (J ⧸ pCore 2 J)) :=
    Group.isSolvable_of_isSolvable_injective (f := o.toMonoidHom) o.injective
  let : IsQuasisimple (I ⧸ fittingSubgroup I) := hFO.2
  let : IsQuasisimple (I ⧸ pPrimeCore 2 I) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hFO.1)
  let eq : ((J ⧸ pCore 2 J) ⧸ pPrimeCore 2 (J ⧸ pCore 2 J)) ≃* (I ⧸ pPrimeCore 2 I) :=
    QuotientGroup.congr _ _ ej (pPrimeCore_map_iso 2 ej)
  let : IsQuasisimple ((J ⧸ pCore 2 J) ⧸ pPrimeCore 2 (J ⧸ pCore 2 J)) :=
    IsQuasisimple.of_mulEquiv eq.symm
  let : Group.IsSolvable (twoOddTwoCore J) := twoOddTwoCore_isSolvable
  exact ⟨twoOddTwoCore_eq_solvableRadical,
    m.cartan_invariant_solvable_core_normalizer_residual hH hlarge A B J hAB hA9 hAe
      hBK hAJB hJU hnJ hKJ (twoOddTwoCore J)⟩
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
