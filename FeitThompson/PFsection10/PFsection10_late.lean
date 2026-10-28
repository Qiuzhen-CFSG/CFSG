module

public import FeitThompson.PFsection10.Basic
import FeitThompson.PFsection8.SourceTypePBridge
import FeitThompson.PFsection5.PFsection5_8
import FeitThompson.PFsection5.PFsection5_9
import FeitThompson.PFsection7.PFsection7_5
import FeitThompson.PFsection7.PFsection7_8_a
import FeitThompson.PFsection7.PFsection7_8_b
import FeitThompson.PFsection8.PFsection8_13
import FeitThompson.PFsection8.PFsection8_15
import FeitThompson.PFsection8.PFsection8_16
import FeitThompson.PFsection8.PFsection8_18
import FeitThompson.PFsection8.PFsection8_9
import FeitThompson.PFsection2.PFsection2_7_11
import FeitThompson.PFsection6.PFsection6_5_a
import FeitThompson.PFsection6.PFsection6_5_b
import FeitThompson.PFsection6.PFsection6_5_c
public import FeitThompson.PFsection6.PFsection6_8
import FeitThompson.PFsection9.PFsection9_3
import FeitThompson.PFsection9.PFsection9_4
import FeitThompson.PFsection9.PFsection9_6
public import FeitThompson.PFsection9.PFsection9_11
import FeitThompson.PFsection10.PFsection10_supported
open Representation



/-!
# Peterfalvi, Section 10: Theorem (10.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace Section10
universe u v w
open Section1 Section2 Section3 Section4

public theorem theorem_10_9_candidate_decomposition_eq
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    {M : Subgroup G}
    {W : Subgroup M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (hμ0 : μ0 = muColumn μ j0) :
    τ (μ0 - ξ) =
      Section4Scratch.omegaColumnSigma σ ω j0 -
        (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)) := by
  rw [hμ0]
  unfold Section4Scratch.omegaColumnSigma
  abel


/-- The PF `(10.5)` bridge is supported on the exact PF `(8.10)` carrier.

This is the source-facing support assertion reused in PF `(11.8)`.  The
Section 4 carrier also contains conjugates of the outer complement; here those
extra points are removed by conjugating the source and selected Type-P
complements and checking the values directly. -/
public theorem alphaChar_CFOn_source_A0book_of_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    {d n : ℕ}
    {δ : ℤ}
    {MFsrc Ms : Subgroup G}
    {Abook A0book A1book : Set G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hSource :
      A = Section8.section8SubgroupSetPreimage M Abook ∧
        Section8.section8SubgroupSetPreimage M A0book ⊆ A0 ∧
        Section8.notation_8_10_source_data M MFsrc Ms Abook A0book A1book ∧
        ∃ H_A0 : G → Subgroup G,
          ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
            ∀ α : Section1.ClassFunction M,
              Section2.CFOn M A0book α →
                τ α = Section2.dadeTransform H_A0 hA0M.subset_L α)
    (hζS : ζ ∈ S)
    (hζIrr : Section1.IsIrreducibleCharacterOnGroup ζ)
    (hζDegree : Section1.degree ζ = (Nat.card W1 : ℂ))
    (hUniform : uniformMuData W1 W2 j0 μ δSign d n δ)
    (hδ : δ = 1)
    {i : I} {j : J}
    (hj : j ≠ j0) :
    Section2.CFOn M A0book (alphaChar μ ζ n δ j0 i j) := by
  classical
  have hnotationAll := hnotation
  have hTail := theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data h10
  rcases h10 with
    ⟨_hM, hType, hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hType with ⟨_hV, U, hP, _hTypeCases⟩
  rcases hSource with ⟨_hApre, _hA0sub, hNotationSrc, _hDadeSrc⟩
  have hMFsrc_eq : MFsrc = MF :=
    section16MFSubgroup_unique hNotationSrc.2.1 hP.1
  subst MFsrc
  have hNot :=
    section10_source_not_typeI_typeII_of_msChoice_tail
      hNotationSrc.2.2.1 hTail
  rcases hNotationSrc with
    ⟨_hMsrc, _hMFsrc, _hMsChoice, _hA1src, hSourceBranch⟩
  rcases hSourceBranch with hTypeI | hTypeP
  · exact False.elim (hNot.1 hTypeI.1)
  rcases hTypeP with
    ⟨Usrc, W1src, W2src, hPsrc, _hSourceType, _hAbook,
      hA0book, hLateSets⟩
  have hLateSets' := hLateSets hTail
  have hA0pre :
      Section8.section8SubgroupSetPreimage M A0book =
        Section8.section8CyclicA0Set M W1src W2src Abook :=
    Section8.theorem_8_15_subgroupSetPreimage_typeP_A0_eq hPsrc hA0book
  have h42src :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup M)
        (W1src.subgroupOf M)
        (W2src.subgroupOf M)
        ((W1src ⊔ W2src).subgroupOf M) :=
    Section8.theorem_8_15_hypothesis_4_2_of_typeP
      (by infer_instance) hPsrc
  rcases theorem_10_7_typeP_outer_complements_conj_source_data hP hPsrc with
    ⟨c, hW1src⟩
  rcases hnotation with
    ⟨_MFbook, _Msbook, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
      _h45, _h48, _hTauA0, hFull⟩
  have h42target := h46.1
  rcases h42target with
    ⟨hSemi, _hHall, _hW1cyc, _hW1ne, _hW2cyc, _hW2ne, _hCentralizer,
      hW1W, _hW2W, hDirect, _hWodd⟩
  rcases hFull with ⟨σM, _xChar, _H_A, _H_A0, hFull46, _hGalois⟩
  rcases hFull46 with
    ⟨_h46full, _hW2K, _h31, _hIsoFull, _hVirtFull, _hClassFull,
      _hPrinFull, _h22A, hFullRest⟩
  rcases hFullRest with
    ⟨_hωFull, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc,
      _hTauA0Full, _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hδ0 : (δSign j0 : ℂ) = 1 :=
    (Section4.proposition_4_4_base
      (W1.subgroupOf M) (W2.subgroupOf M) W I J i0 j0 ω σM μ
        (fun k => (δSign k : ℂ)) hω h43b).1
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hd, _hSign, _hn, hDegree, hδSign, hdn⟩
  have hδj : (δSign j : ℂ) = 1 := by
    rw [hδSign j hj, hδ]
    norm_num
  have hζDerived :
      Section1.supportedOn ζ ((derivedSubgroup M : Subgroup M) : Set M) := by
    rcases (hS ζ).mp hζS with ⟨θ, _hθirr, _hθne, hζeq⟩
    rw [hζeq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ
  have hdegreeAlpha :
      Section1.degree (alphaChar μ ζ n δ j0 i j) = 0 := by
    have hbase : Section1.degree (μ i j0) = 1 :=
      baseColumn_degree_one_of_section10FourSixNotationSupportedData_pairing
        hnotationAll i
    have hdnC : (d : ℂ) = (n : ℂ) * (Nat.card W1 : ℂ) + (δ : ℂ) := by
      exact_mod_cast hdn
    have hdegApply : μ i j 1 = (d : ℂ) := by
      simpa [Section1.degree] using hDegree i j hj
    have hbaseApply : μ i j0 1 = (1 : ℂ) := by
      simpa [Section1.degree] using hbase
    have hζApply : ζ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hζDegree
    unfold alphaChar Section1.degree
    simp [hdegApply, hbaseApply, hζApply, hdnC]
  have hαClass :
      Section1.IsClassFunction (alphaChar μ ζ n δ j0 i j) := by
    have hμClass : ∀ r k, Section1.IsClassFunction (μ r k) := fun r k =>
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (theorem_10_3_mu_entry_irreducible_supported hnotationAll r k))
    have hζClass : Section1.IsClassFunction ζ :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζIrr)
    intro x g
    simp [alphaChar, hμClass i j x g, hμClass i j0 x g, hζClass x g]
  have hαW1 :
      ∀ x : M, (x : G) ∈ W1 → alphaChar μ ζ n δ j0 i j x = 0 := by
    intro x hxW1
    by_cases hx1 : x = 1
    · subst x
      simpa [Section1.degree] using hdegreeAlpha
    · have hxW1local : x ∈ W1.subgroupOf M := hxW1
      have hxNotDerived : x ∉ derivedSubgroup M := by
        intro hxDerived
        have hxInf : x ∈ derivedSubgroup M ⊓ W1.subgroupOf M :=
          ⟨hxDerived, hxW1local⟩
        rw [hSemi.inf_eq_bot] at hxInf
        exact hx1 (Subgroup.mem_bot.mp hxInf)
      have hζzero : ζ x = 0 :=
        (Section1.supportedOn_iff.mp hζDerived) x hxNotDerived
      have hxW : x ∈ W := hW1W hxW1local
      have hxNotW2 : x ∉ W2.subgroupOf M := by
        intro hxW2
        have hxInf : x ∈ W1.subgroupOf M ⊓ W2.subgroupOf M :=
          ⟨hxW1local, hxW2⟩
        rw [hDirect.inf_eq_bot] at hxInf
        exact hx1 (Subgroup.mem_bot.mp hxInf)
      have hxMinus : x ∈ ((W : Set M) \ (W2.subgroupOf M : Set M)) :=
        ⟨hxW, hxNotW2⟩
      let xW : W := ⟨x, hxW⟩
      have hωright : ω i0 j xW = 1 := by
        have hker := hω.right_kernel j ⟨xW, hxW1local⟩
        simpa [hω.degree_one i0 j] using hker
      have hωeq : ω i j xW = ω i j0 xW := by
        rw [hω.product i j xW, hωright]
        ring
      have hμj : μ i j x = ω i j xW := by
        simpa [xW, hδj] using h43c.1 i j x hxMinus
      have hμ0 : μ i j0 x = ω i j0 xW := by
        simpa [xW, hδ0] using h43c.1 i j0 x hxMinus
      simp [alphaChar, hδ, hμj, hμ0, hζzero, hωeq]
  refine ⟨hαClass, ?_⟩
  intro x hxA0book
  by_cases hx1 : x = 1
  · subst x
    simpa [Section1.degree] using hdegreeAlpha
  · have hxNotDerived : x ∉ derivedSubgroup M := by
      intro hxDerived
      apply hxA0book
      rw [hA0book]
      left
      rw [hLateSets'.2, hLateSets'.1]
      have hxDerivedAmbient : (x : G) ∈ ambientDerivedSubgroup M := by
        have hxSub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
          simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hxDerived
        exact hxSub
      exact ⟨hxDerivedAmbient, by
        intro hxG
        exact hx1 (Subtype.ext hxG)⟩
    have hxConj :
        x ∈ Section2.conjugateSet
          ((((W1src ⊔ W2src).subgroupOf M : Subgroup M) : Set M) \
            (W2src.subgroupOf M : Set M)) := by
      by_contra hx
      exact hxNotDerived
        (Section4Scratch.mem_K_of_not_mem_conjugateSet_wMinusW2_pf45
          h42src hx)
    rcases hxConj with ⟨w, hw, m, hmx⟩
    have hwW1 : w ∈ W1src.subgroupOf M := by
      by_contra hwNotW1
      have hwCyc :
          w ∈ Section3.cyclicTISet
            (W1src.subgroupOf M) (W2src.subgroupOf M)
              ((W1src ⊔ W2src).subgroupOf M) :=
        (Section3.cyclicTISet_mem_iff
          (W1src.subgroupOf M) (W2src.subgroupOf M)
            ((W1src ⊔ W2src).subgroupOf M)).2
          ⟨hw.1, hwNotW1, hw.2⟩
      apply hxA0book
      have hxPre : x ∈ Section8.section8SubgroupSetPreimage M A0book := by
        rw [hA0pre]
        exact Or.inr ⟨w, hwCyc, m, hmx⟩
      exact hxPre
    have hwConj : (w : G) ∈ W1.conjBy (c : G) := by
      rw [← hW1src]
      exact hwW1
    rw [Subgroup.conjBy, Subgroup.mem_map] at hwConj
    rcases hwConj with ⟨y, hyW1, hyw⟩
    let yM : M := ⟨y, hW1M hyW1⟩
    have hywM : c * yM * c⁻¹ = w := by
      apply Subtype.ext
      simpa [yM, MulAut.conj_apply] using hyw
    have hmxM : m * w * m⁻¹ = x := by
      simpa [Section2.conjBy] using hmx
    calc
      alphaChar μ ζ n δ j0 i j x =
          alphaChar μ ζ n δ j0 i j w := by
        simpa [hmxM] using hαClass m w
      _ = alphaChar μ ζ n δ j0 i j yM := by
        simpa [hywM] using hαClass c yM
      _ = 0 := hαW1 yM hyW1

public theorem theorem_10_9_baseColumnMinusXi_CFOn_A0book_of_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {MFsrc Ms : Subgroup G}
    {Abook A0book A1book : Set G}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hSource :
      A = Section8.section8SubgroupSetPreimage M Abook ∧
        Section8.section8SubgroupSetPreimage M A0book ⊆ A0 ∧
        Section8.notation_8_10_source_data M MFsrc Ms Abook A0book A1book ∧
        ∃ H_A0 : G → Subgroup G,
          ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
            ∀ α : Section1.ClassFunction M,
              Section2.CFOn M A0book α →
                τ α = Section2.dadeTransform H_A0 hA0M.subset_L α)
    (hξS : ξ ∈ S)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section2.CFOn M A0book (muColumn μ j0 - ξ) := by
  classical
  rcases h10 with
    ⟨_hM, hType, hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hSource with ⟨_hApre, _hA0sub, hNotationSrc, _hDadeSrc⟩
  rcases hnotation with
    ⟨_MFsrc', _Ms', _Abook', _A0book', _A1book', _hSource',
      _hW, _hA0, _h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, h45, _h48,
      _hTauA0, hFull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  have hMFsrc_eq : MFsrc = MF := by
    rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
    exact section16MFSubgroup_unique hNotationSrc.2.1 hP.1
  have hNotationOuter :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book := by
    simpa [hMFsrc_eq] using hNotationSrc
  have hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF :=
    theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hA_eq_A1 :
      Abook = A1book :=
    theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data
      hNotationOuter hTail
  have hA1_eq_derived :
      A1book = section16NonidentityElements
        (ambientDerivedSubgroup M : Set G) :=
    theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
      hNotationOuter hTail
  have hA_subset_A0 : Abook ⊆ A0book :=
    theorem_10_7_A_subset_A0_of_notation_8_10_source_data hNotationOuter
  have hDerivedSub :
      ((derivedSubgroup M : Subgroup M) : Set M) \ {1} ⊆
        Section8.section8SubgroupSetPreimage M A0book := by
    intro x hx
    have hxDsub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hx.1
    have hxDG : (x : G) ∈ ambientDerivedSubgroup M := hxDsub
    have hxGne : (x : G) ≠ 1 := by
      intro hxG
      exact hx.2 (Subtype.ext hxG)
    have hxA1 : (x : G) ∈ A1book := by
      rw [hA1_eq_derived]
      exact ⟨hxDG, hxGne⟩
    have hxA : (x : G) ∈ Abook := by
      rw [hA_eq_A1]
      exact hxA1
    have hxA0 : (x : G) ∈ A0book := hA_subset_A0 hxA
    simpa [Section8.section8SubgroupSetPreimage] using hxA0
  have hμ0_eq :
      muColumn μ j0 =
        Section1.inducedCF (derivedSubgroup M) (xChar j0) := by
    simpa [muColumn, Section4Scratch.piColumn] using (h45a.2.2 j0).symm
  have hμ0Derived :
      Section1.supportedOn (muColumn μ j0)
        ((derivedSubgroup M : Subgroup M) : Set M) := by
    rw [hμ0_eq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) (xChar j0)
  have hξDerived :
      Section1.supportedOn ξ
        ((derivedSubgroup M : Subgroup M) : Set M) := by
    rcases (hS ξ).mp hξS with ⟨θ, _hθirr, _hθne, hξeq⟩
    rw [hξeq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ
  have hμ0Class : Section1.IsClassFunction (muColumn μ j0) := by
    rw [hμ0_eq]
    exact Section1.inducedCF_isClassFunction (derivedSubgroup M) (xChar j0)
  have hξClass : Section1.IsClassFunction ξ := by
    rcases (hS ξ).mp hξS with ⟨θ, _hθirr, _hθne, hξeq⟩
    rw [hξeq]
    exact Section1.inducedCF_isClassFunction (derivedSubgroup M) θ
  have hαClass : Section1.IsClassFunction (muColumn μ j0 - ξ) := by
    intro x g
    simp [Pi.sub_apply, hμ0Class x g, hξClass x g]
  have hbaseDegree : ∀ i, Section1.degree (μ i j0) = 1 := by
    rcases hFull with ⟨σM, _xCharFull, _H_A, _H_A0, hFull46, _hGalois⟩
    rcases hFull46 with
      ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨hωFull, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
    exact Section4.proposition_4_4_baseColumn_degree_one
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (I := I)
      (J := J)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (deltaSign := fun j => (δSign j : ℂ))
      h46.1 hωFull h43b h43c
  have hIcardNat : Fintype.card I = Nat.card W1 := by
    calc
      Fintype.card I = Nat.card (W1.subgroupOf M) := hω.card_left
      _ = Nat.card W1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1M).toEquiv
  have hIcard : (Fintype.card I : ℂ) = (Nat.card W1 : ℂ) := by
    exact_mod_cast hIcardNat
  have hμ0_one : muColumn μ j0 1 = (Nat.card W1 : ℂ) := by
    calc
      muColumn μ j0 1 = ∑ i : I, μ i j0 1 := by simp [muColumn]
      _ = ∑ _i : I, (1 : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simpa [Section1.degree] using hbaseDegree i
      _ = (Nat.card W1 : ℂ) := by simp [hIcard]
  have hξ_one : ξ 1 = (Nat.card W1 : ℂ) := by
    simpa [Section1.degree] using hξDegree
  refine ⟨hαClass, ?_⟩
  intro x hxA0book
  by_cases hx1 : x = 1
  · subst x
    simp [Pi.sub_apply, hμ0_one, hξ_one]
  · have hxNotDerived : x ∉ ((derivedSubgroup M : Subgroup M) : Set M) := by
      intro hxDerived
      have hxpre : x ∈ Section8.section8SubgroupSetPreimage M A0book :=
        hDerivedSub ⟨hxDerived, by simpa using hx1⟩
      exact hxA0book (by
        simpa [Section8.section8SubgroupSetPreimage] using hxpre)
    have hμ0_zero : muColumn μ j0 x = 0 :=
      (Section1.supportedOn_iff.mp hμ0Derived) x hxNotDerived
    have hξ_zero : ξ x = 0 :=
      (Section1.supportedOn_iff.mp hξDerived) x hxNotDerived
    simp [Pi.sub_apply, hμ0_zero, hξ_zero]

/-- Two equal-degree members of the derived induced family have a difference
supported on the source PF `(8.10)` carrier `A₀(M)`. -/
public theorem derivedInducedFamily_sub_CFon_A0book_of_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {MFsrc Ms : Subgroup G}
    {Abook A0book A1book : Set G}
    {ξ η : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hNotationSrc :
      Section8.notation_8_10_source_data M MFsrc Ms Abook A0book A1book)
    (hξS : ξ ∈ S)
    (hηS : η ∈ S)
    (hdegree : Section1.degree ξ = Section1.degree η) :
    Section2.CFOn M A0book (ξ - η) := by
  classical
  rcases h10 with
    ⟨_hM, hType, hS, _hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hMFsrc_eq : MFsrc = MF := by
    rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
    exact section16MFSubgroup_unique hNotationSrc.2.1 hP.1
  have hNotationOuter :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book := by
    simpa [hMFsrc_eq] using hNotationSrc
  have hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF :=
    theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hA_eq_A1 : Abook = A1book :=
    theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data
      hNotationOuter hTail
  have hA1_eq_derived :
      A1book = section16NonidentityElements
        (ambientDerivedSubgroup M : Set G) :=
    theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
      hNotationOuter hTail
  have hA_subset_A0 : Abook ⊆ A0book :=
    theorem_10_7_A_subset_A0_of_notation_8_10_source_data hNotationOuter
  have hDerivedSub :
      ((derivedSubgroup M : Subgroup M) : Set M) \ {1} ⊆
        Section8.section8SubgroupSetPreimage M A0book := by
    intro x hx
    have hxDsub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hx.1
    have hxDG : (x : G) ∈ ambientDerivedSubgroup M := hxDsub
    have hxGne : (x : G) ≠ 1 := by
      intro hxG
      exact hx.2 (Subtype.ext hxG)
    have hxA1 : (x : G) ∈ A1book := by
      rw [hA1_eq_derived]
      exact ⟨hxDG, hxGne⟩
    have hxA : (x : G) ∈ Abook := by
      rw [hA_eq_A1]
      exact hxA1
    have hxA0 : (x : G) ∈ A0book := hA_subset_A0 hxA
    simpa [Section8.section8SubgroupSetPreimage] using hxA0
  have hξDerived :
      Section1.supportedOn ξ ((derivedSubgroup M : Subgroup M) : Set M) := by
    rcases (hS ξ).mp hξS with ⟨θ, _hθirr, _hθne, hξeq⟩
    rw [hξeq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ
  have hηDerived :
      Section1.supportedOn η ((derivedSubgroup M : Subgroup M) : Set M) := by
    rcases (hS η).mp hηS with ⟨θ, _hθirr, _hθne, hηeq⟩
    rw [hηeq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ
  have hξClass : Section1.IsClassFunction ξ := by
    rcases (hS ξ).mp hξS with ⟨θ, _hθirr, _hθne, hξeq⟩
    rw [hξeq]
    exact Section1.inducedCF_isClassFunction (derivedSubgroup M) θ
  have hηClass : Section1.IsClassFunction η := by
    rcases (hS η).mp hηS with ⟨θ, _hθirr, _hθne, hηeq⟩
    rw [hηeq]
    exact Section1.inducedCF_isClassFunction (derivedSubgroup M) θ
  refine ⟨?_, ?_⟩
  · intro x g
    simp [Pi.sub_apply, hξClass x g, hηClass x g]
  · intro x hxA0book
    by_cases hx1 : x = 1
    · subst x
      simpa [Section1.degree] using sub_eq_zero.mpr hdegree
    · have hxNotDerived : x ∉ ((derivedSubgroup M : Subgroup M) : Set M) := by
        intro hxDerived
        have hxpre : x ∈ Section8.section8SubgroupSetPreimage M A0book :=
          hDerivedSub ⟨hxDerived, by simpa using hx1⟩
        exact hxA0book (by
          simpa [Section8.section8SubgroupSetPreimage] using hxpre)
      have hξzero : ξ x = 0 :=
        (Section1.supportedOn_iff.mp hξDerived) x hxNotDerived
      have hηzero : η x = 0 :=
        (Section1.supportedOn_iff.mp hηDerived) x hxNotDerived
      simp [Pi.sub_apply, hξzero, hηzero]

public theorem theorem_10_9_one_lt_card_W1_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    1 < Nat.card W1 := by
  rcases h10 with
    ⟨_hM, hType, _hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10,
      _h52⟩
  rcases hType with ⟨_hV, _U, hP, _hCases⟩
  rcases hP with ⟨_hMF, _hCyc, hW1ne, _hRest⟩
  exact (Subgroup.one_lt_card_iff_ne_bot W1).2 hW1ne

public theorem theorem_10_9_mu_entry_muColumn_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (i : I) (j k : J) :
    Section1.scalarProduct M (μ i j) (muColumn μ k) =
      if j = k then 1 else 0 := by
  classical
  rcases hnotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, hFull⟩
  rcases hFull with ⟨_σM, _xChar, _H_A, _H_A0, hFull46, _hGalois⟩
  rcases hFull46 with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  unfold muColumn
  have hsum :
      ((∑ p : I, μ p k : Section1.ClassFunction M)) =
        fun x => ∑ p : I, μ p k x := by
    ext x
    simp
  rw [hsum, Section1.scalarProduct_fintype_sum_right]
  by_cases hjk : j = k
  · subst k
    calc
      (∑ p : I, Section1.scalarProduct M (μ i j) (μ p j)) =
          ∑ p : I, if p = i then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            by_cases hpi : p = i
            · subst p
              simpa using scalarProduct_irreducible_self (hirr i j)
            · simpa [hpi] using
                scalarProduct_irreducible_ne (hirr i j) (hirr p j)
                  (hdistinct (i, j) (p, j) (by
                    intro hEq
                    exact hpi (congrArg Prod.fst hEq).symm))
      _ = if j = j then (1 : ℂ) else 0 := by
            simp
  · calc
      (∑ p : I, Section1.scalarProduct M (μ i j) (μ p k)) =
          ∑ _p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            simpa using
              scalarProduct_irreducible_ne (hirr i j) (hirr p k)
                (hdistinct (i, j) (p, k) (by
                  intro hEq
                  exact hjk (congrArg Prod.snd hEq)))
        _ = if j = k then (1 : ℂ) else 0 := by
              simp [hjk]

public theorem theorem_10_9_base_character_eq_principal_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ) :
    μ i0 j0 = Section1.principalCharacter M := by
  rcases hnotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, hFull⟩
  rcases hFull with ⟨σM, _xChar, _H_A, _H_A0, hFull46, _hGalois⟩
  rcases hFull46 with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  exact
    (Section4.proposition_4_4_base (W1.subgroupOf M) (W2.subgroupOf M) W
      I J i0 j0 ω σM μ (fun j => (δSign j : ℂ)) hω h43b).2

public theorem theorem_10_9_muColumn_base_principal_scalarProduct_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ) :
    Section1.scalarProduct M (muColumn μ j0) (Section1.principalCharacter M) = 1 := by
  have hbase := theorem_10_9_base_character_eq_principal_supported hnotation
  have hentry :
      Section1.scalarProduct M (Section1.principalCharacter M) (muColumn μ j0) = 1 := by
    simpa [hbase] using
      theorem_10_9_mu_entry_muColumn_supported hnotation i0 j0 j0
  simpa [Section1.scalarProduct_star_swap] using congrArg star hentry

public theorem theorem_10_9_xi_principal_scalarProduct_eq_zero_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section1.scalarProduct M ξ (Section1.principalCharacter M) = 0 := by
  have hW1gt : 1 < Nat.card W1 := theorem_10_9_one_lt_card_W1_supported h10
  have hξ_ne : ξ ≠ Section1.principalCharacter M := by
    intro hξeq
    have hdegEq := congrArg Section1.degree hξeq
    have hprincipalDegree :
        Section1.degree (Section1.principalCharacter M) = 1 := by
      simp [Section1.degree, Section1.principalCharacter]
    have hcardEqC : (Nat.card W1 : ℂ) = 1 := by
      calc
        (Nat.card W1 : ℂ) = Section1.degree ξ := hξDegree.symm
        _ = Section1.degree (Section1.principalCharacter M) := hdegEq
        _ = 1 := hprincipalDegree
    have hcardEq : Nat.card W1 = 1 := by
      exact_mod_cast hcardEqC
    exact (ne_of_gt hW1gt) hcardEq
  exact scalarProduct_irreducible_ne hξIrr
    (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := M)) hξ_ne

public theorem theorem_10_9_source_principal_coefficient_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section1.scalarProduct M (μ0 - ξ) (Section1.principalCharacter M) = 1 := by
  rw [hμ0, Section5.scalarProduct_sub_left]
  rw [theorem_10_9_muColumn_base_principal_scalarProduct_supported hnotation,
    theorem_10_9_xi_principal_scalarProduct_eq_zero_supported h10 hξIrr hξDegree]
  norm_num

public theorem theorem_10_9_tau_diff_sigma_omega_base_coefficient_of_CFon
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    {M : Subgroup G}
    {W : Subgroup M}
    {A0book : Set G}
    {H_A0 : G → Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (hA0M : Section2.Hypothesis2 A0book M H_A0)
    (hτDade :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M A0book α →
          τ α = Section2.dadeTransform H_A0 hA0M.subset_L α)
    (hωbase : ω i0 j0 = Section1.principalCharacter W)
    (hσprincipal :
      σ (Section1.principalCharacter W) = Section1.principalCharacter G)
    (hsource :
      Section1.scalarProduct M (μ0 - ξ) (Section1.principalCharacter M) = 1)
    (hCFOn : Section2.CFOn M A0book (μ0 - ξ)) :
    Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i0 j0)) = 1 := by
  classical
  have hσbase : σ (ω i0 j0) = Section1.principalCharacter G := by
    rw [hωbase]
    exact hσprincipal
  rw [hσbase]
  let α : Section1.ClassFunction M := μ0 - ξ
  have hCFOnα : Section2.CFOn M A0book α := by
    simpa [α] using hCFOn
  have hprinGClass :
      Section1.IsClassFunction (Section1.principalCharacter G) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprinMClass :
      Section1.IsClassFunction (Section1.principalCharacter M) := by
    intro x g
    simp [Section1.principalCharacter]
  have havg :
      ∀ ⦃a : G⦄, (ha : a ∈ A0book) →
        Section1.principalCharacter M ⟨a, hA0M.subset_L a ha⟩ =
          Section2.dadeAveragingFunction M H_A0
            (Section1.principalCharacter G) ⟨a, hA0M.subset_L a ha⟩ := by
    intro a ha
    simp [Section2.dadeAveragingFunction, Section1.principalCharacter]
    have hcard_eq :
        @Fintype.card (H_A0 a)
          (Fintype.ofFinite (H_A0 ↑(⟨a, hA0M.subset_L a ha⟩ : M))) =
          Fintype.card (H_A0 a) := by
      rw [← @Nat.card_eq_fintype_card (H_A0 a)
        (Fintype.ofFinite (H_A0 ↑(⟨a, hA0M.subset_L a ha⟩ : M)))]
      rw [← Nat.card_eq_fintype_card (α := H_A0 a)]
    rw [hcard_eq]
    have hcard_ne :
        ((Fintype.card (H_A0 a) : ℂ)) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (H_A0 a) ≠ 0)
    exact (inv_mul_cancel₀ hcard_ne).symm
  have hconst :
      Section2.constantOnDadeCosets A0book H_A0
        (Section1.principalCharacter G) := by
    intro a h ha hh
    simp [Section1.principalCharacter]
  have htransfer :
      Section1.scalarProduct G
          (Section2.dadeTransform H_A0 hA0M.subset_L α)
          (Section1.principalCharacter G) =
        Section1.scalarProduct M α
          (Section1.subgroupRestriction M (Section1.principalCharacter G)) := by
    exact
      ((Section2.proposition_2_7 (A := A0book) (L := M) (H := H_A0)
          hA0M hA0M.subset_L α (Section1.principalCharacter G) hCFOnα
          hprinGClass (Section1.principalCharacter M) hprinMClass havg).2 hconst)
  have hresPrincipal :
      Section1.subgroupRestriction M (Section1.principalCharacter G) =
        Section1.principalCharacter M := by
    ext m
    simp [Section1.subgroupRestriction, Section1.principalCharacter]
  calc
    Section1.scalarProduct G (τ (μ0 - ξ)) (Section1.principalCharacter G) =
        Section1.scalarProduct G
          (Section2.dadeTransform H_A0 hA0M.subset_L α)
          (Section1.principalCharacter G) := by
      rw [hτDade α hCFOnα]
    _ = Section1.scalarProduct M α
          (Section1.subgroupRestriction M (Section1.principalCharacter G)) :=
      htransfer
    _ = Section1.scalarProduct M α (Section1.principalCharacter M) := by
      rw [hresPrincipal]
    _ = 1 := by
      simpa [α] using hsource

public theorem theorem_10_9_tau_diff_sigma_omega_base_coefficient_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i0 j0)) = 1 := by
  classical
  have hnotationData := hnotation
  rcases hnotationData with
    ⟨_MFsrc, _Ms, _Abook, A0book, _A1book, hSource,
      _hW, _hA0, _h46, hω, _hIso, _hVirt, hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  rcases hSource with ⟨_hApre, _hA0sub, _h810, H_A0, hA0M, hτDade⟩
  have hsource :
      Section1.scalarProduct M (μ0 - ξ) (Section1.principalCharacter M) = 1 :=
    theorem_10_9_source_principal_coefficient_supported
      h10 hnotation hμ0 hξIrr hξDegree
  have hCFOn :
      Section2.CFOn M A0book (μ0 - ξ) := by
    rw [hμ0]
    exact theorem_10_9_baseColumnMinusXi_CFOn_A0book_of_supported
      h10 hnotation
      ⟨_hApre, _hA0sub, _h810, H_A0, hA0M, hτDade⟩
      hξS hξDegree
  exact theorem_10_9_tau_diff_sigma_omega_base_coefficient_of_CFon
    hA0M hτDade hω.principal hPrin hsource hCFOn


public theorem theorem_10_9_tau_diff_sigma_omega_single_column_core
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {i0 : I}
    {j0 : J}
    (a : I → J → ℂ)
    (hrect : ∀ i i' k k', a i k + a i' k' = a i k' + a i' k)
    (hcount_lt_two : Section3.coefficientNonzeroCount a < 2 * Fintype.card I)
    (hoddI : Odd (Fintype.card I))
    (hoddJ : Odd (Fintype.card J))
    (hltIJ : Fintype.card I < Fintype.card J)
    (hI3 : 3 ≤ Fintype.card I)
    (hcount_le_I_succ :
      Section3.coefficientNonzeroCount a ≤ Fintype.card I + 1)
    (hbase : a i0 j0 = 1) :
    ∀ i j, a i j = if j = j0 then 1 else 0 := by
  classical
  have hshape :
      (∀ i k, a i k = 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ k : J,
          ∀ i q, a i q = if q = k then c else 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
          ∀ p q, a p q = if p = i then c else 0) :=
    Section3.coefficient_rectangle_small_shape a hrect hcount_lt_two hoddI hoddJ
      hltIJ hI3
  have hI_succ_lt_J : Fintype.card I + 1 < Fintype.card J := by
    rcases hoddI with ⟨m, hm⟩
    rcases hoddJ with ⟨n, hn⟩
    omega
  have hcount_lt_J : Section3.coefficientNonzeroCount a < Fintype.card J := by
    omega
  rcases hshape with hzero | hshape
  · exfalso
    have h0 := hzero i0 j0
    rw [hbase] at h0
    norm_num at h0
  · rcases hshape with hcol | hrow
    · rcases hcol with ⟨c, _hc, k, hcol⟩
      have hj0k : j0 = k := by
        by_contra hne
        have h0 : a i0 j0 = 0 := by
          simpa [hne] using hcol i0 j0
        rw [hbase] at h0
        norm_num at h0
      subst k
      have hc1 : c = 1 := by
        have hcolbase := hcol i0 j0
        rw [hbase] at hcolbase
        simpa using hcolbase.symm
      intro i j
      have hij := hcol i j
      rw [hc1] at hij
      simpa using hij
    · rcases hrow with ⟨c, hc, irow, hrow⟩
      exfalso
      have hcount_eq : Section3.coefficientNonzeroCount a = Fintype.card J :=
        Section3.coefficientNonzeroCount_eq_card_right_of_single_row a c irow hc hrow
      omega

public theorem theorem_10_9_tau_diff_sigma_omega_single_column_supported_of_bounds
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hW1ltW2 : Nat.card W1 < Nat.card W2)
    (hYvirt : IsVirtualCharacter (τ (μ0 - ξ)))
    (hnorm :
      Section5.cfNormSq (τ (μ0 - ξ)) = (Nat.card W1 : ℝ) + 1)
    (hcount_lt_two :
      Section3.coefficientNonzeroCount
          (fun i k =>
            Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i k))) <
        2 * Fintype.card I)
    (hrect :
      let Y : Section1.ClassFunction G := τ (μ0 - ξ)
      let a : I → J → ℂ := fun i k =>
        Section1.scalarProduct G Y (σ (ω i k))
      ∀ i i' k k', a i k + a i' k' = a i k' + a i' k)
    (hbase :
      Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i0 j0)) = 1) :
    ∀ i j,
      Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i j)) =
        if j = j0 then 1 else 0 := by
  classical
  let Y : Section1.ClassFunction G := τ (μ0 - ξ)
  let a : I → J → ℂ := fun i k =>
    Section1.scalarProduct G Y (σ (ω i k))
  have hnotationData := hnotation
  rcases hnotationData with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource, _hW, _hA0, h46, hω,
      _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _hTauA0, _hfull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hIcard : Fintype.card I = Nat.card W1 := by
    have hI : Nat.card I = Nat.card W1 :=
      uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data h10 hnotation
    simpa [Nat.card_eq_fintype_card] using hI
  have hJcard : Fintype.card J = Nat.card W2 := by
    have hJ : Nat.card J = Nat.card W2 :=
      uniformMu_card_J_eq_card_W2_of_hypothesis_10_1_supported_data h10 hnotation
    simpa [Nat.card_eq_fintype_card] using hJ
  have hltIJ : Fintype.card I < Fintype.card J := by
    rw [hIcard, hJcard]
    exact hW1ltW2
  have hI3 : 3 ≤ Fintype.card I := by
    rw [hω.card_left]
    exact Section3.natCard_left_ge_three_of_hypothesis_3_1 h31
  have hoddI : Odd (Fintype.card I) := by
    rw [hω.card_left]
    exact Section3.odd_natCard_left_of_hypothesis_3_1 h31
  have hoddJ : Odd (Fintype.card J) := by
    rw [hω.card_right]
    exact Section3.odd_natCard_right_of_hypothesis_3_1 h31
  have hcountR :
      (Section3.coefficientNonzeroCount a : ℝ) ≤ Section5.cfNormSq Y := by
    dsimp [a, Y]
    exact coefficientNonzeroCount_sigma_omega_le_cfNormSq_pf109_supported
      hnotation hYvirt
  have hcount_le_I_succ :
      Section3.coefficientNonzeroCount a ≤ Fintype.card I + 1 := by
    have hcount_le_I_succ_real :
        (Section3.coefficientNonzeroCount a : ℝ) ≤
          (Fintype.card I : ℝ) + 1 := by
      rw [hnorm] at hcountR
      simpa [Y, hIcard] using hcountR
    exact_mod_cast hcount_le_I_succ_real
  have hbase' : a i0 j0 = 1 := by
    simpa [a, Y] using hbase
  have hrect' : ∀ i i' k k', a i k + a i' k' = a i k' + a i' k := by
    simpa [a, Y] using hrect
  have hcount_lt_two' :
      Section3.coefficientNonzeroCount a < 2 * Fintype.card I := by
    simpa [a, Y] using hcount_lt_two
  have hcoeff :=
    theorem_10_9_tau_diff_sigma_omega_single_column_core a hrect'
      hcount_lt_two' hoddI hoddJ hltIJ hI3 hcount_le_I_succ hbase'
  intro i j
  simpa [a, Y] using hcoeff i j


public theorem theorem_10_10_3_tauOne_sOne_scalarProduct_eq_ite
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {χ η : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J}
    {μcol : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hχ : χ ∈ S₁)
    (hη : η ∈ S₁) :
    Section1.scalarProduct G (τ₁ χ) (τ₁ η) =
      if χ = η then (1 : ℂ) else 0 := by
  classical
  rcases hτ₁ with ⟨_hcoh, hIso, _hVirt, _hAgree⟩
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
  have hχspan : Section5.integerSpan S₁ χ :=
    Section5.integerSpan_of_mem S₁ hχ
  have hηspan : Section5.integerSpan S₁ η :=
    Section5.integerSpan_of_mem S₁ hη
  have hiso :
      Section1.scalarProduct G (τ₁ χ) (τ₁ η) =
        Section1.scalarProduct M χ η :=
    hIso χ η hχspan hηspan
  by_cases hχη : χ = η
  · subst χ
    rw [hiso]
    simp [scalarProduct_irreducible_self ((hS1irr η hη).1)]
  · have hχirr : Section1.IsIrreducibleCharacterOnGroup χ := (hS1irr χ hχ).1
    have hηirr : Section1.IsIrreducibleCharacterOnGroup η := (hS1irr η hη).1
    rw [hiso]
    simp [hχη, scalarProduct_irreducible_ne hχirr hηirr hχη]

public theorem theorem_10_10_3_tauOne_sOne_sum_scalarProduct
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {η : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J}
    {μcol : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hη : η ∈ S₁) :
    Section1.scalarProduct G (Finset.sum S₁ fun χ => τ₁ χ) (τ₁ η) = 1 := by
  classical
  have hpair :
      ∀ χ ∈ S₁,
        Section1.scalarProduct G (τ₁ χ) (τ₁ η) =
          if χ = η then (1 : ℂ) else 0 := by
    intro χ hχ
    by_cases hχη : χ = η
    · subst χ
      simpa using
        theorem_10_10_3_tauOne_sOne_scalarProduct_eq_ite
          hcount hτ₁ hη hη
    · simpa [hχη] using
        theorem_10_10_3_tauOne_sOne_scalarProduct_eq_ite
          hcount hτ₁ hχ hη
  calc
    Section1.scalarProduct G (Finset.sum S₁ fun χ => τ₁ χ) (τ₁ η)
        = Section1.scalarProduct G
            (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) (τ₁ η) := by
          congr 1
          rw [← Finset.sum_attach]
          simp [Finset.univ_eq_attach]
    _ = Section1.scalarProduct G
            (fun g => ∑ χ : {χ // χ ∈ S₁}, (τ₁ χ.1) g) (τ₁ η) := by
          congr 1
          ext g
          simp
    _ = ∑ χ : {χ // χ ∈ S₁}, Section1.scalarProduct G (τ₁ χ.1) (τ₁ η) := by
          rw [Section1.scalarProduct_fintype_sum_left]
    _ = ∑ χ : {χ // χ ∈ S₁}, if χ.1 = η then (1 : ℂ) else 0 := by
          exact Finset.sum_congr rfl (fun χ _hχ => hpair χ.1 χ.2)
    _ = 1 := by
          rw [Finset.sum_eq_single (⟨η, hη⟩ : {χ // χ ∈ S₁})]
          · simp
          · intro χ _hχ hχne
            have hne : χ.1 ≠ η := by
              intro hEq
              exact hχne (Subtype.ext hEq)
            simp [hne]
          · intro hηnot
            exact False.elim (hηnot (Finset.mem_univ _))


public theorem theorem_10_10_3_tauOne_sOne_sum_scalarProduct_self
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J}
    {μcol : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁) :
    Section1.scalarProduct G
        (Finset.sum S₁ fun χ => τ₁ χ)
        (Finset.sum S₁ fun χ => τ₁ χ) =
      (S₁.card : ℂ) := by
  classical
  let Y : Section1.ClassFunction G := Finset.sum S₁ fun χ => τ₁ χ
  have hsum_repr :
      Y = (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) := by
    dsimp [Y]
    rw [← Finset.sum_attach]
  have hsum_fun :
      (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) =
        (fun g => ∑ χ : {χ // χ ∈ S₁}, (τ₁ χ.1) g) := by
    ext g
    simp
  change Section1.scalarProduct G Y Y = (S₁.card : ℂ)
  calc
    Section1.scalarProduct G Y Y
        = Section1.scalarProduct G Y
            (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) := by
          rw [hsum_repr]
    _ = Section1.scalarProduct G Y
          (fun g => ∑ χ : {χ // χ ∈ S₁}, (τ₁ χ.1) g) := by
          rw [← hsum_fun]
    _ = ∑ χ : {χ // χ ∈ S₁}, Section1.scalarProduct G Y (τ₁ χ.1) := by
          rw [Section1.scalarProduct_fintype_sum_right]
    _ = ∑ _χ : {χ // χ ∈ S₁}, (1 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro χ _hχ
          dsimp [Y]
          exact theorem_10_10_3_tauOne_sOne_sum_scalarProduct hcount hτ₁ χ.2
    _ = (S₁.card : ℂ) := by
          simp


public theorem isVirtualCharacter_intCast_smul_sec10
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (n : ℤ)
    (hχ : IsVirtualCharacter χ) :
    IsVirtualCharacter ((n : ℂ) • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

public theorem isVirtualCharacter_natCast_smul_sec10
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (n : ℕ)
    (hχ : IsVirtualCharacter χ) :
    IsVirtualCharacter ((n : ℂ) • χ) := by
  simpa using isVirtualCharacter_intCast_smul_sec10 (G := G) (χ := χ) (n : ℤ) hχ

public theorem theorem_10_10_3_tauOne_sOne_isVirtualCharacter
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁) :
    IsVirtualCharacter (τ₁ ζ) := by
  rcases hτ₁ with ⟨_hcoh, _hIso, hVirt, _hagrees⟩
  exact hVirt ζ (Section5.integerSpan_of_mem S₁ hζ)


public theorem theorem_10_10_3_tauOne_projection_cfNormSq
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J}
    {μcol : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁)
    (a : ℤ) :
    Section5.cfNormSq
        ((a : ℂ) • (Finset.sum S₁ fun χ => τ₁ χ) - (n : ℂ) • τ₁ ζ) =
      (S₁.card : ℝ) * (a : ℝ) ^ 2 -
        2 * (a : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 := by
  let T : Section1.ClassFunction G := Finset.sum S₁ fun χ => τ₁ χ
  have hTT : Section1.scalarProduct G T T = (S₁.card : ℂ) := by
    dsimp [T]
    exact theorem_10_10_3_tauOne_sOne_sum_scalarProduct_self hcount hτ₁
  have hTζ : Section1.scalarProduct G T (τ₁ ζ) = 1 := by
    dsimp [T]
    exact theorem_10_10_3_tauOne_sOne_sum_scalarProduct hcount hτ₁ hζ
  have hζT : Section1.scalarProduct G (τ₁ ζ) T = 1 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hTζ
  have hζζ : Section1.scalarProduct G (τ₁ ζ) (τ₁ ζ) = 1 := by
    simpa using theorem_10_10_3_tauOne_sOne_scalarProduct_eq_ite hcount hτ₁ hζ hζ
  unfold Section5.cfNormSq
  change
    Complex.re
        (Section1.scalarProduct G
          ((a : ℂ) • T - (n : ℂ) • τ₁ ζ)
          ((a : ℂ) • T - (n : ℂ) • τ₁ ζ)) =
      (S₁.card : ℝ) * (a : ℝ) ^ 2 -
        2 * (a : ℝ) * (n : ℝ) + (n : ℝ) ^ 2
  rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
    Section5.scalarProduct_sub_right]
  repeat rw [Section1.scalarProduct_smul_left]
  repeat rw [Section1.scalarProduct_smul_right]
  rw [hTT, hTζ, hζT, hζζ]
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  ring


public theorem classFunction_eq_of_norm_eq_and_sub_orthogonal
    {G : Type u} [Group G] [Finite G]
    {Y Z : Section1.ClassFunction G}
    (hYnorm : Section5.cfNormSq Y = Section5.cfNormSq Z)
    (hYZ : Section1.scalarProduct G (Y - Z) Z = 0)
    (hZY : Section1.scalarProduct G Z (Y - Z) = 0) :
    Y = Z := by
  let R : Section1.ClassFunction G := Y - Z
  have hRZ : Section1.scalarProduct G R Z = 0 := by
    dsimp [R]
    exact hYZ
  have hZR : Section1.scalarProduct G Z R = 0 := by
    dsimp [R]
    exact hZY
  have hdecomp : Y = R + Z := by
    dsimp [R]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm :
      Section5.cfNormSq Y = Section5.cfNormSq R + Section5.cfNormSq Z := by
    rw [hdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hRZ hZR
  have hRnorm : Section5.cfNormSq R = 0 := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  have hRzero : R = 0 := Section5.cfNormSq_eq_zero hRnorm
  change Y - Z = 0 at hRzero
  exact sub_eq_zero.mp hRzero

public theorem classFunction_eq_signed_sub_of_norm_two_and_residual_orthogonal
    {G : Type u} [Group G] [Finite G]
    {Y φ ψ : Section1.ClassFunction G}
    {δ : ℤ}
    (hδnorm : Complex.normSq (δ : ℂ) = 1)
    (hφφ : Section1.scalarProduct G φ φ = 1)
    (hψψ : Section1.scalarProduct G ψ ψ = 1)
    (hφψ : Section1.scalarProduct G φ ψ = 0)
    (hψφ : Section1.scalarProduct G ψ φ = 0)
    (hYnorm : Section5.cfNormSq Y = 2)
    (hRφ : Section1.scalarProduct G (Y - (δ : ℂ) • (φ - ψ)) φ = 0)
    (hRψ : Section1.scalarProduct G (Y - (δ : ℂ) • (φ - ψ)) ψ = 0) :
    Y = (δ : ℂ) • (φ - ψ) := by
  let Z : Section1.ClassFunction G := (δ : ℂ) • (φ - ψ)
  have hdiffnorm : Section5.cfNormSq (φ - ψ) = 2 := by
    unfold Section5.cfNormSq
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [hφφ, hφψ, hψφ, hψψ]
    norm_num
  have hZnorm : Section5.cfNormSq Z = 2 := by
    dsimp [Z]
    rw [Section5.cfNormSq_smul, hdiffnorm, hδnorm]
    norm_num
  have hRZ : Section1.scalarProduct G (Y - Z) Z = 0 := by
    dsimp [Z]
    rw [Section1.scalarProduct_smul_right, Section5.scalarProduct_sub_right]
    rw [hRφ, hRψ]
    simp
  have hZR : Section1.scalarProduct G Z (Y - Z) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRZ
  exact classFunction_eq_of_norm_eq_and_sub_orthogonal
    (Y := Y) (Z := Z) (by rw [hYnorm, hZnorm]) hRZ hZR


public theorem theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁) :
    ∀ i j, Section1.scalarProduct G (τ₁ ζ) (σ (ω i j)) = 0 := by
  classical
  let : Fintype M := Fintype.ofFinite M
  intro i j
  have hζS : ζ ∈ S := typeVCharacterCount_sOne_subset hcount hζ
  have hζIrr : Section1.IsIrreducibleCharacterOnGroup ζ := by
    rcases hcount with ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact (hS1irr ζ hζ).1
  rcases derivedSupportedFourSixData_of_hypothesis_10_1_supported_data
      h10 hnotation with
    ⟨σM, xChar, H_A, _H_A0, hSupported⟩
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σL := σM)
      (σ := σ)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ)
      (H_A := H_A)
      hSupported
  have hRpack :=
    Section5.theorem_5_3_b_core
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σL := σM)
      (σ := σ)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ)
      (S := S)
      hCtx
      ⟨ζ, hζS⟩
      (hypothesis_5_2_a_of_hypothesis_10_1_supported_data h10)
      (inducedFromNonkernelFamily_of_hypothesis_10_1_supported_data h10)
  rcases hRpack with
    ⟨R, hsetup, h52a, h52b, h52c, h52d, h52e, hExtra⟩
  let X : S := ⟨ζ, hζS⟩
  have hζbarS₁ :
      Section1.conjugateCharacter ζ ∈ S₁ :=
    typeVCharacterCount_sOne_conjugate_mem_supported hred h10 hcount ζ hζ
  have hpairSubset :
      ({(X : Section1.ClassFunction M),
        Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
        Finset (Section1.ClassFunction M)) ⊆ S₁ := by
    intro χ hχ
    simp at hχ
    rcases hχ with rfl | rfl
    · exact hζ
    · simpa [X] using hζbarS₁
  rcases hτ₁ with ⟨hcoh, hIso, hVirt, hagree⟩
  have hτ₁' : typeVCoherentSubfamilyData M S₁ τ τ₁ :=
    ⟨hcoh, hIso, hVirt, hagree⟩
  have hpairIso :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSubset hIso
  have hpairVirt :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSubset hVirt
  have hagreeX :
      τ₁ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) =
        τ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) := by
    simpa [X] using
      typeVCoherentSubfamilyData_agreesOn_sub hcount hτ₁' hζ hζbarS₁
  have hsubset :
      Section5.isSubsetSumOf (R X) (τ₁ ζ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X) (τ₁ (X : Section1.ClassFunction M)) :=
      Section5.theorem_5_5 S τ R
        hsetup h52a h52b h52c h52d h52e X τ₁ hpairIso hpairVirt hagreeX
    simpa [X] using hsubsetX
  have horth :
      Section5.orthogonalFinsets (R X)
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
    hExtra X hζIrr
  have homega :
      σ (ω i j) ∈
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) := by
    exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩
  exact scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets hsubset horth homega

public theorem one_le_normSq_intCast_of_ne_zero
    (z : ℤ) (hz : (z : ℂ) ≠ 0) :
    (1 : ℝ) ≤ Complex.normSq (z : ℂ) := by
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hz
    simp [hz0]
  have hzz : (1 : ℤ) ≤ z * z := by
    have hpos : 0 < z * z := (mul_self_pos).2 hz0
    omega
  have hreal : (1 : ℝ) ≤ (z : ℝ) * (z : ℝ) := by
    exact_mod_cast hzz
  simpa [Complex.normSq, pow_two] using hreal

public theorem cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (w : ι → ℂ) (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0) :
    Section5.cfNormSq (Section1.weightedFamilySum w χ) =
      ∑ i : ι, Complex.normSq (w i) := by
  classical
  have hself :
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ) =
        ∑ i : ι, star (w i) * w i := by
    calc
      Section1.scalarProduct G (Section1.weightedFamilySum w χ)
          (Section1.weightedFamilySum w χ)
          = ∑ i : ι, star (w i) *
              Section1.scalarProduct G (Section1.weightedFamilySum w χ) (χ i) := by
            rw [Section1.scalarProduct_weightedFamilySum_right]
      _ = ∑ i : ι, star (w i) * w i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i]
  unfold Section5.cfNormSq
  rw [hself, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hnorm : star (w i) * w i = ((Complex.normSq (w i) : ℝ) : ℂ) := by
    simp [Complex.normSq_eq_conj_mul_self]
  rw [hnorm]
  simp


public theorem finite_orthonormal_virtual_coeff_support_card_le_two
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (hχvirt : ∀ i, IsVirtualCharacter (χ i))
    {Y : Section1.ClassFunction G}
    (hYvirt : IsVirtualCharacter Y)
    (hYnorm : Section5.cfNormSq Y = 2) :
    Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} ≤ 2 := by
  classical
  let nz : Finset ι :=
    Finset.univ.filter fun i : ι => Section1.scalarProduct G Y (χ i) ≠ 0
  let w : ι → ℂ := fun i =>
    if Section1.scalarProduct G Y (χ i) = 0 then 0
    else Section1.scalarProduct G Y (χ i)
  let P : Section1.ClassFunction G := Section1.weightedFamilySum w χ
  let R : Section1.ClassFunction G := Y - P
  have hPχ : ∀ i : ι, Section1.scalarProduct G P (χ i) = w i := by
    intro i
    dsimp [P]
    exact Section1.scalarProduct_weightedFamilySum_left_orthonormal w χ horth i
  have hRχ : ∀ i : ι, Section1.scalarProduct G R (χ i) = 0 := by
    intro i
    dsimp [R]
    rw [Section5.scalarProduct_sub_left, hPχ i]
    dsimp [w]
    by_cases hzero : Section1.scalarProduct G Y (χ i) = 0
    · simp [hzero]
    · simp [hzero]
  have hRP : Section1.scalarProduct G R P = 0 := by
    dsimp [P]
    rw [Section1.scalarProduct_weightedFamilySum_right]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    rw [hRχ i]
    simp
  have hPR : Section1.scalarProduct G P R = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hRP
  have hdecomp : Y = R + P := by
    dsimp [R, P]
    ext g
    simp [Pi.sub_apply, Pi.add_apply]
  have hnorm_decomp :
      Section5.cfNormSq Y = Section5.cfNormSq R + Section5.cfNormSq P := by
    rw [hdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hRP hPR
  have hPnorm_le : Section5.cfNormSq P ≤ 2 := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    rw [hYnorm] at hnorm_decomp
    nlinarith
  have hPnorm :
      Section5.cfNormSq P = ∑ i : ι, Complex.normSq (w i) := by
    dsimp [P]
    exact cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq w χ horth
  have hterms : ∀ i ∈ nz, (1 : ℝ) ≤ Complex.normSq (w i) := by
    intro i hi
    have hi_ne : Section1.scalarProduct G Y (χ i) ≠ 0 := by
      change i ∈
        Finset.univ.filter
          (fun i : ι => Section1.scalarProduct G Y (χ i) ≠ 0) at hi
      exact (Finset.mem_filter.mp hi).2
    rcases Section3.scalarProduct_isVirtualCharacter_eq_int
        hYvirt (hχvirt i) with
      ⟨z, hz⟩
    have hz_ne : (z : ℂ) ≠ 0 := by
      intro hz0
      exact hi_ne (by simpa [hz] using hz0)
    dsimp [w]
    rw [if_neg hi_ne, hz]
    exact one_le_normSq_intCast_of_ne_zero z hz_ne
  have hcard_le_sum_nz :
      (nz.card : ℝ) ≤ ∑ i ∈ nz, Complex.normSq (w i) := by
    calc
      (nz.card : ℝ) = ∑ _i ∈ nz, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ nz, Complex.normSq (w i) := by
          exact Finset.sum_le_sum (fun i hi => hterms i hi)
  have hsum_nz_le_univ :
      ∑ i ∈ nz, Complex.normSq (w i) ≤
        ∑ i : ι, Complex.normSq (w i) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro i hi; simp)
      (by intro i _hiuniv _hinz; exact Complex.normSq_nonneg (w i))
  have hcard_real_le_two : (nz.card : ℝ) ≤ 2 := by
    rw [← hPnorm] at hsum_nz_le_univ
    nlinarith
  have hcard_nat : nz.card ≤ 2 := by
    exact_mod_cast hcard_real_le_two
  have hcard_eq :
      Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} =
        nz.card := by
    dsimp [nz]
    rw [Fintype.card_subtype]
  simpa [hcard_eq]


public theorem exists_two_ne_of_card_ge_three
    {I : Type*} [Fintype I] [DecidableEq I]
    (i0 : I) (hI3 : 3 ≤ Fintype.card I) :
    ∃ i1 i2 : I, i1 ≠ i0 ∧ i2 ≠ i0 ∧ i2 ≠ i1 := by
  classical
  let rows : Finset I := Finset.univ.erase i0
  have hrows_card : rows.card = Fintype.card I - 1 := by
    dsimp [rows]
    rw [Finset.card_erase_of_mem (by simp : i0 ∈ (Finset.univ : Finset I))]
    simp
  have hrows_two : 2 ≤ rows.card := by
    rw [hrows_card]
    omega
  have hrows_pos : 0 < rows.card := by omega
  rcases Finset.card_pos.mp hrows_pos with ⟨i1, hi1rows⟩
  let rows' : Finset I := rows.erase i1
  have hrows'_card : rows'.card = rows.card - 1 := by
    dsimp [rows']
    exact Finset.card_erase_of_mem hi1rows
  have hrows'_pos : 0 < rows'.card := by
    rw [hrows'_card]
    omega
  rcases Finset.card_pos.mp hrows'_pos with ⟨i2, hi2rows'⟩
  have hi1_ne : i1 ≠ i0 := (Finset.mem_erase.mp hi1rows).1
  have hi2_ne_i1 : i2 ≠ i1 := (Finset.mem_erase.mp hi2rows').1
  have hi2rows : i2 ∈ rows := (Finset.mem_erase.mp hi2rows').2
  have hi2_ne_i0 : i2 ≠ i0 := (Finset.mem_erase.mp hi2rows).1
  exact ⟨i1, i2, hi1_ne, hi2_ne_i0, hi2_ne_i1⟩

public theorem three_le_coefficientNonzeroCount_of_three_nonzero_cells
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (p q r : I × J)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : a p.1 p.2 ≠ 0) (hq : a q.1 q.2 ≠ 0)
    (hr : a r.1 r.2 ≠ 0) :
    3 ≤ Section3.coefficientNonzeroCount a := by
  classical
  let s : Finset (I × J) := {p, q, r}
  have hs : ∀ x ∈ s, a x.1 x.2 ≠ 0 := by
    intro x hx
    simp [s] at hx
    rcases hx with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hcard : s.card = 3 := by
    simp [s, hpq, hpr, hqr]
  rw [← hcard]
  exact Section3.finset_card_le_coefficientNonzeroCount a s hs

public theorem coefficientNonzeroCount_ge_card_left_of_active_row_choice
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) {i0 : I} {jActive jChoice k : J}
    (hactive : a i0 jActive ≠ 0)
    (hrow : ∀ i : I, i ≠ i0 → a i k ≠ 0 ∨ a i jChoice ≠ 0) :
    Fintype.card I ≤ Section3.coefficientNonzeroCount a := by
  classical
  let rows : Finset I := Finset.univ.erase i0
  let pick : I → I × J := fun i => if a i k = 0 then (i, jChoice) else (i, k)
  let sRows : Finset (I × J) := rows.image pick
  let s : Finset (I × J) := {(i0, jActive)} ∪ sRows
  have hpick_fst : ∀ i : I, (pick i).1 = i := by
    intro i
    dsimp [pick]
    by_cases hik : a i k = 0 <;> simp [hik]
  have hs : ∀ p ∈ s, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp0 | hpRows
    · have hp_eq : p = (i0, jActive) := by simpa [s] using hp0
      simpa [hp_eq] using hactive
    · rcases Finset.mem_image.mp hpRows with ⟨i, hirows, rfl⟩
      have hi_ne : i ≠ i0 := (Finset.mem_erase.mp hirows).1
      dsimp [pick]
      by_cases hik : a i k = 0
      · have hij : a i jChoice ≠ 0 := by
          rcases hrow i hi_ne with hik_ne | hij_ne
          · exact False.elim (hik_ne hik)
          · exact hij_ne
        simp [hik, hij]
      · simp [hik]
  have hdisj : Disjoint ({(i0, jActive)} : Finset (I × J)) sRows := by
    rw [Finset.disjoint_left]
    intro p hp0 hpRows
    have hp_eq : p = (i0, jActive) := by simpa using hp0
    rcases Finset.mem_image.mp hpRows with ⟨i, hirows, hpi⟩
    have hi_ne : i ≠ i0 := (Finset.mem_erase.mp hirows).1
    have hi_eq : i = i0 := by
      have hfst := congrArg Prod.fst hpi
      exact (hpick_fst i).symm.trans (hfst.trans (by simp [hp_eq]))
    exact hi_ne hi_eq
  have hsRows_card : sRows.card = rows.card := by
    dsimp [sRows]
    rw [Finset.card_image_iff.mpr]
    intro x _hx y _hy hxy
    exact (hpick_fst x).symm.trans ((congrArg Prod.fst hxy).trans (hpick_fst y))
  have hrows_card : rows.card = Fintype.card I - 1 := by
    dsimp [rows]
    rw [Finset.card_erase_of_mem (by simp : i0 ∈ (Finset.univ : Finset I))]
    simp
  have hnotmem : (i0, jActive) ∉ sRows := by
    intro hmem
    exact (Finset.disjoint_left.mp hdisj) (by simp) hmem
  have hs_card : s.card = Fintype.card I := by
    dsimp [s]
    simp [hnotmem, hsRows_card, hrows_card]
    have hpos : 0 < Fintype.card I := by
      have _ : Nonempty I := ⟨i0⟩
      exact Fintype.card_pos
    omega
  rw [← hs_card]
  exact Section3.finset_card_le_coefficientNonzeroCount a s hs

public theorem coefficientNonzeroCount_row_outside_contradiction
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) {i0 : I} {j j0 : J}
    (hj : j ≠ j0)
    (hJ5 : 5 ≤ Fintype.card J)
    (ha : Section3.coefficientNonzeroCount a ≤ 2)
    (hrow : ∀ k : J, k ≠ j → k ≠ j0 → a i0 k ≠ 0) :
    False := by
  classical
  let cols : Finset J := (Finset.univ.erase j).erase j0
  let s : Finset (I × J) := cols.image fun k => (i0, k)
  have hs : ∀ p ∈ s, a p.1 p.2 ≠ 0 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, hkcols, rfl⟩
    have hk_ne_j0 : k ≠ j0 := (Finset.mem_erase.mp hkcols).1
    have hk_ne_j : k ≠ j :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hkcols).2).1
    exact hrow k hk_ne_j hk_ne_j0
  have hs_card : s.card = Fintype.card J - 2 := by
    dsimp [s, cols]
    rw [Finset.card_image_iff.mpr]
    · exact Section3.card_univ_erase_erase (I := J) (r := j) (i := j0)
        (fun h => hj h.symm)
    · intro x _hx y _hy hxy
      exact congrArg Prod.snd hxy
  have hthree : 3 ≤ Section3.coefficientNonzeroCount a := by
    have hscard3 : 3 ≤ s.card := by
      rw [hs_card]
      omega
    exact le_trans hscard3 (Section3.finset_card_le_coefficientNonzeroCount a s hs)
  omega

public theorem rectangle_two_cell_update_base_row_vanish
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a b : I → J → ℂ) {i0 : I} {j j0 : J} {δ : ℂ}
    (hj : j ≠ j0)
    (hδ : δ ≠ 0)
    (hI3 : 3 ≤ Fintype.card I)
    (hJ5 : 5 ≤ Fintype.card J)
    (ha : Section3.coefficientNonzeroCount a ≤ 2)
    (hrect : ∀ i i' k k', b i k + b i' k' = b i k' + b i' k)
    (hupdate_j : a i0 j = b i0 j + δ)
    (hupdate_j0 : a i0 j0 = b i0 j0 - δ)
    (hupdate_other : ∀ i k, (i, k) ≠ (i0, j) → (i, k) ≠ (i0, j0) →
      a i k = b i k) :
    b i0 j = 0 ∧ b i0 j0 = 0 := by
  classical
  have htwoδ : δ + δ ≠ 0 := by
    intro h
    have hhalf : δ = 0 := by
      linear_combination (1 / 2 : ℂ) * h
    exact hδ hhalf
  have hmain :
      ∀ {jA jB : J} {ε : ℂ},
        jA ≠ jB →
        ε ≠ 0 →
        (∀ k : J, k ≠ jA → k ≠ jB →
          (i0, k) ≠ (i0, j) ∧ (i0, k) ≠ (i0, j0)) →
        a i0 jA = b i0 jA + ε →
        a i0 jB = b i0 jB - ε →
        b i0 jA = 0 := by
    intro jA jB ε hjAB hε hcells hupdateA hupdateB
    have htwoε : ε + ε ≠ 0 := by
      intro h
      have hhalf : ε = 0 := by
        linear_combination (1 / 2 : ℂ) * h
      exact hε hhalf
    by_contra hbA
    by_cases hzeroOutside :
        ∃ k : J, k ≠ jA ∧ k ≠ jB ∧ b i0 k = 0
    · rcases hzeroOutside with ⟨k0, hk0A, hk0B, hb0⟩
      have ha_other : ∀ i k, i ≠ i0 → a i k = b i k := by
        intro i k hi
        exact hupdate_other i k
          (by intro hp; exact hi (congrArg Prod.fst hp))
          (by intro hp; exact hi (congrArg Prod.fst hp))
      have hrow_or : ∀ i : I, i ≠ i0 → a i k0 ≠ 0 ∨ a i jA ≠ 0 := by
        intro i hi
        have hrect_i := hrect i i0 jA k0
        have hbijA : b i jA = b i k0 + b i0 jA := by
          rw [hb0] at hrect_i
          simpa [add_comm, add_left_comm, add_assoc] using hrect_i
        by_cases hik : a i k0 = 0
        · right
          have hbik : b i k0 = 0 := by
            simpa [ha_other i k0 hi] using hik
          have hbijA_ne : b i jA ≠ 0 := by
            rw [hbijA, hbik]
            simpa using hbA
          simpa [ha_other i jA hi] using hbijA_ne
        · exact Or.inl hik
      by_cases hactiveA : a i0 jA ≠ 0
      · have hcount_ge :=
          coefficientNonzeroCount_ge_card_left_of_active_row_choice
            a (i0 := i0) (jActive := jA) (jChoice := jA) (k := k0)
            hactiveA hrow_or
        have hthree : 3 ≤ Section3.coefficientNonzeroCount a :=
          le_trans hI3 hcount_ge
        omega
      · have hactiveB_or : a i0 jB ≠ 0 ∨ a i0 jB = 0 := by
          exact ne_or_eq _ _
        rcases hactiveB_or with hactiveB | hactiveB_zero
        · have hcount_ge :=
            coefficientNonzeroCount_ge_card_left_of_active_row_choice
              a (i0 := i0) (jActive := jB) (jChoice := jA) (k := k0)
              hactiveB hrow_or
          have hthree : 3 ≤ Section3.coefficientNonzeroCount a :=
            le_trans hI3 hcount_ge
          omega
        · rcases exists_two_ne_of_card_ge_three i0 hI3 with
            ⟨i1, i2, hi1, hi2, hi21⟩
          have hAeps : b i0 jA = -ε := by
            have hzero : b i0 jA + ε = 0 := by
              simpa [hupdateA] using hactiveA
            linear_combination hzero
          have hBeps : b i0 jB = ε := by
            have hzero : b i0 jB - ε = 0 := by
              simpa [hupdateB] using hactiveB_zero
            linear_combination hzero
          have hrow_two : ∀ i : I, i ≠ i0 →
              ∃ u v : J, u ≠ v ∧ a i u ≠ 0 ∧ a i v ≠ 0 := by
            intro i hi
            have hAeq : a i jA = a i k0 + b i0 jA := by
              have hrect_i := hrect i i0 jA k0
              have hb : b i jA = b i k0 + b i0 jA := by
                rw [hb0] at hrect_i
                simpa [add_comm, add_left_comm, add_assoc] using hrect_i
              rw [ha_other i jA hi, ha_other i k0 hi, hb]
            have hBeq : a i jB = a i k0 + b i0 jB := by
              have hrect_i := hrect i i0 jB k0
              have hb : b i jB = b i k0 + b i0 jB := by
                rw [hb0] at hrect_i
                simpa [add_comm, add_left_comm, add_assoc] using hrect_i
              rw [ha_other i jB hi, ha_other i k0 hi, hb]
            by_cases hk : a i k0 = 0
            · refine ⟨jA, jB, hjAB, ?_, ?_⟩
              · rw [hAeq, hk, hAeps]
                simpa using (neg_ne_zero.mpr hε)
              · rw [hBeq, hk, hBeps]
                simpa using hε
            · by_cases hAj : a i jA ≠ 0
              · exact ⟨k0, jA, hk0A, hk, hAj⟩
              · have hBj : a i jB ≠ 0 := by
                  intro hBj0
                  have hsumA : a i k0 + b i0 jA = 0 := by
                    simpa [hAeq] using hAj
                  have hsumB : a i k0 + b i0 jB = 0 := by
                    simpa [hBeq] using hBj0
                  have hBA : b i0 jA = b i0 jB := by
                    linear_combination hsumA - hsumB
                  have hcontr : ε + ε = 0 := by
                    rw [hAeps, hBeps] at hBA
                    calc
                      ε + ε = ε + (-ε) := by
                        nth_rewrite 2 [← hBA]
                        rfl
                      _ = 0 := by ring
                  exact htwoε hcontr
                exact ⟨k0, jB, hk0B, hk, hBj⟩
          rcases hrow_two i1 hi1 with ⟨u, v, huv, hu, hv⟩
          rcases hrow_two i2 hi2 with ⟨w, _w', _hww', hw, _hw'⟩
          have hpq : (i1, u) ≠ (i1, v) := by
            intro hp
            exact huv (congrArg Prod.snd hp)
          have hpr : (i1, u) ≠ (i2, w) := by
            intro hp
            exact hi21 (congrArg Prod.fst hp).symm
          have hqr : (i1, v) ≠ (i2, w) := by
            intro hp
            exact hi21 (congrArg Prod.fst hp).symm
          have hthree :=
            three_le_coefficientNonzeroCount_of_three_nonzero_cells
              a (i1, u) (i1, v) (i2, w) hpq hpr hqr hu hv hw
          omega
    · have hrow_nonzero : ∀ k : J, k ≠ jA → k ≠ jB → a i0 k ≠ 0 := by
        intro k hkA hkB
        have hbk : b i0 k ≠ 0 := by
          intro hbk
          exact hzeroOutside ⟨k, hkA, hkB, hbk⟩
        have hcellA : (i0, k) ≠ (i0, j) := (hcells k hkA hkB).1
        have hcellB : (i0, k) ≠ (i0, j0) := (hcells k hkA hkB).2
        simpa [hupdate_other i0 k hcellA hcellB] using hbk
      exact coefficientNonzeroCount_row_outside_contradiction
        a (i0 := i0) (j := jA) (j0 := jB) hjAB hJ5 ha hrow_nonzero
  constructor
  · exact hmain hj hδ
      (by
        intro k hkj hkj0
        exact ⟨by intro hp; exact hkj (congrArg Prod.snd hp),
          by intro hp; exact hkj0 (congrArg Prod.snd hp)⟩)
      hupdate_j hupdate_j0
  · have hother_sym : ∀ i k, (i, k) ≠ (i0, j0) → (i, k) ≠ (i0, j) →
        a i k = b i k := by
      intro i k h1 h2
      exact hupdate_other i k h2 h1
    have hvanish :=
      hmain (jA := j0) (jB := j) (ε := -δ)
        (fun h => hj h.symm) (by simpa using (neg_ne_zero.mpr hδ))
        (by
          intro k hkj0 hkj
          exact ⟨by intro hp; exact hkj (congrArg Prod.snd hp),
            by intro hp; exact hkj0 (congrArg Prod.snd hp)⟩)
        (by
          rw [hupdate_j0]
          ring)
        (by
    rw [hupdate_j]
    ring)
    exact hvanish


public theorem theorem_10_10_4_tauOne_sOne_virtual
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S₁ : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (η : S₁) :
    IsVirtualCharacter (τ₁ (η : Section1.ClassFunction M)) := by
  rcases hτ₁ with ⟨_hcoh, _hIso, hVirt, _hAgree⟩
  exact hVirt (η : Section1.ClassFunction M)
    (Section5.integerSpan_of_mem S₁ η.2)

public theorem theorem_10_10_4_tauOne_sOne_gram
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S₁ : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (η ξ : S₁) :
    Section1.scalarProduct G
        (τ₁ (η : Section1.ClassFunction M))
        (τ₁ (ξ : Section1.ClassFunction M)) =
      Section1.scalarProduct M
        (η : Section1.ClassFunction M)
        (ξ : Section1.ClassFunction M) := by
  rcases hτ₁ with ⟨_hcoh, hIso, _hVirt, _hAgree⟩
  exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hIso η.2 ξ.2


public theorem theorem_10_10_4_sOne_mu_orthogonal_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M MF H H' W1 W2 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {j0 : J}
    {μ : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ)
    (η : S₁)
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M (η : Section1.ClassFunction M) (μ j) = 0 := by
  rcases hypothesis_5_2_of_hypothesis_10_1_supported_data h10 with
    ⟨_hSetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
  have hηS : (η : Section1.ClassFunction M) ∈ S :=
    typeVCharacterCount_sOne_subset hcount η.2
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, hmu, _hd, _hδ, _hn⟩
  have hμS : μ j ∈ S := (hmu j hj).1
  have hne : (η : Section1.ClassFunction M) ≠ μ j := by
    intro hEq
    have hdegEq : Section1.degree (η : Section1.ClassFunction M) =
        Section1.degree (μ j) := congrArg Section1.degree hEq
    have hηdeg : Section1.degree (η : Section1.ClassFunction M) =
        (Nat.card W1 : ℂ) := (hS1irr (η : Section1.ClassFunction M) η.2).2
    have hμdeg : Section1.degree (μ j) = (p * Nat.card W1 : ℂ) :=
      (hmu j hj).2
    have hnat_eq : Nat.card W1 = p * Nat.card W1 := by
      exact_mod_cast (hηdeg.symm.trans (hdegEq.trans hμdeg))
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    have hnat_eq_z :
        (Nat.card W1 : ℤ) = (p : ℤ) * (Nat.card W1 : ℤ) := by
      exact_mod_cast hnat_eq
    have hpgt : (1 : ℤ) < (p : ℤ) := by
      exact_mod_cast hpprime.one_lt
    have hwpos : (0 : ℤ) < (Nat.card W1 : ℤ) := by
      exact_mod_cast (lt_trans Nat.zero_lt_one hW1gt)
    nlinarith
  exact h52c hηS hμS hne

public theorem isVirtualCharacter_finset_sum_sec10
    {G : Type u}
    [Group G]
    [Finite G]
    {ι : Type*}
    (s : Finset ι)
    (χ : ι → Section1.ClassFunction G)
    (hχ : ∀ i ∈ s, IsVirtualCharacter (χ i)) :
    IsVirtualCharacter (Finset.sum s χ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero :
          IsVirtualCharacter ((0 : Section1.ClassFunction G)) := by
        simpa using
          (isVirtualCharacter_intCast_smul_sec10
            (G := G)
            (χ := Section1.principalCharacter G)
            0
            (Section3.isVirtualCharacter_principalCharacter (G := G)))
      simpa using hzero
  | @insert a s ha ih =>
      have ha' : IsVirtualCharacter (χ a) :=
        hχ a (Finset.mem_insert_self a s)
      have hs' : IsVirtualCharacter (Finset.sum s χ) := by
        exact ih (by
          intro i hi
          exact hχ i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'


public theorem theorem_10_10_4_omegaColumnSigma_virtual_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (j : J) :
    IsVirtualCharacter (Section4Scratch.omegaColumnSigma σ ω j) := by
  classical
  rcases hnotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, _hIso, hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  unfold Section4Scratch.omegaColumnSigma
  refine isVirtualCharacter_finset_sum_sec10
    (G := G) (s := Finset.univ) (χ := fun i : I => σ (ω i j)) ?_
  intro i _hi
  exact hVirt (ω i j)
    (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hω.irreducible i j))


public theorem scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (i : I) (j k : J) :
    Section1.scalarProduct G (σ (ω i j))
      (Section4Scratch.omegaColumnSigma σ ω k) =
      if j = k then 1 else 0 := by
  classical
  unfold Section4Scratch.omegaColumnSigma
  have hsumk :
      ((∑ p : I, σ (ω p k) : Section1.ClassFunction G)) =
        fun g => ∑ p : I, σ (ω p k) g := by
    ext g
    simp
  rw [hsumk, Section1.scalarProduct_fintype_sum_right]
  by_cases hjk : j = k
  · subst k
    calc
      (∑ p : I, Section1.scalarProduct G (σ (ω i j)) (σ (ω p j))) =
          ∑ p : I, if (i, j) = (p, j) then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            exact scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
              h i p j j
      _ = if j = j then (1 : ℂ) else 0 := by
            simp
  · calc
      (∑ p : I, Section1.scalarProduct G (σ (ω i j)) (σ (ω p k))) =
          ∑ p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            have hpair : (i, j) ≠ (p, k) := by
              intro hp
              exact hjk (congrArg Prod.snd hp)
            simpa [hpair] using
              scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
                h i p j k
      _ = if j = k then (1 : ℂ) else 0 := by
            simp [hjk]

public theorem theorem_10_10_4_omegaColumnSigma_gram_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (j k : J) :
    Section1.scalarProduct G
        (Section4Scratch.omegaColumnSigma σ ω j)
        (Section4Scratch.omegaColumnSigma σ ω k) =
      if j = k then (Fintype.card I : ℂ) else 0 := by
  classical
  have hsumj :
      ((∑ i : I, σ (ω i j) : Section1.ClassFunction G)) =
        fun g => ∑ i : I, σ (ω i j) g := by
    ext g
    simp
  change
    Section1.scalarProduct G (∑ i : I, σ (ω i j))
      (Section4Scratch.omegaColumnSigma σ ω k) =
      if j = k then (Fintype.card I : ℂ) else 0
  rw [hsumj, Section1.scalarProduct_fintype_sum_left]
  by_cases hjk : j = k
  · calc
      (∑ i : I,
          Section1.scalarProduct G (σ (ω i j))
            (Section4Scratch.omegaColumnSigma σ ω k)) =
          ∑ _i : I, (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [hjk] using
              scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
                hnotation i j k
      _ = if j = k then (Fintype.card I : ℂ) else 0 := by
            simp [hjk]
  · calc
      (∑ i : I,
          Section1.scalarProduct G (σ (ω i j))
            (Section4Scratch.omegaColumnSigma σ ω k)) =
          ∑ _i : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [hjk] using
              scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
                hnotation i j k
      _ = if j = k then (Fintype.card I : ℂ) else 0 := by
            simp [hjk]


public theorem theorem_10_10_4_tauOne_sOne_signed_omegaColumnSigma_orthogonal_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (η : S₁)
    (j : J) :
    Section1.scalarProduct G
        (τ₁ (η : Section1.ClassFunction M))
        ((δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω j) = 0 := by
  classical
  rw [Section1.scalarProduct_smul_right]
  unfold Section4Scratch.omegaColumnSigma
  have hsum :
      ((∑ i : I, σ (ω i j) : Section1.ClassFunction G)) =
        fun g => ∑ i : I, σ (ω i j) g := by
    ext g
    simp
  rw [hsum, Section1.scalarProduct_fintype_sum_right]
  have horth : ∀ i, Section1.scalarProduct G
      (τ₁ (η : Section1.ClassFunction M)) (σ (ω i j)) = 0 := by
    intro i
    exact theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
      hred h10 hcount hnotation η.2 hτ₁ i j
  simp [horth]


public theorem theorem_10_10_4_signed_omegaColumnSigma_gram_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {δ : ℤ}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hδ : δ = -1)
    (j k : J) :
    Section1.scalarProduct G
        ((δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω j)
        ((δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω k) =
      if j = k then (Fintype.card I : ℂ) else 0 := by
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    theorem_10_10_4_omegaColumnSigma_gram_supported hnotation j k, hδ]
  by_cases hjk : j = k <;> simp [hjk]


public theorem typeVReduction_kernelSubfamily_mem_iff_base_and_kernel_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    {χ : Section1.ClassFunction M} :
    χ ∈ Section6.inducedKernelFamilyOf
        (derivedSubgroup M) (H'.subgroupOf M) S ↔
      χ ∈ S ∧ Section1.subgroupInKernel' χ (H'.subgroupOf M) := by
  have hS₁ :
      Section6.inducedKernelFamily (derivedSubgroup M) (H'.subgroupOf M)
        (Section6.inducedKernelFamilyOf
          (derivedSubgroup M) (H'.subgroupOf M) S) :=
    Section6.inducedKernelFamilyOf_isFamily
      (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
      (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred)
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10
  have hS₁sub :
      Section6.inducedKernelFamilyOf
        (derivedSubgroup M) (H'.subgroupOf M) S ⊆ S :=
    Section6.inducedKernelFamily_subset_base
      (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
      (Section6.inducedKernelFamilyOf_isFamily
        (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
        (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred))
  have _ : (H'.subgroupOf M).Normal := typeVReduction_Hprime_subgroupOf_normal hred
  constructor
  · intro hχ
    rcases (hS₁.2 χ).mp hχ with ⟨θ, hθirr, hθker, _hθne, hχeq⟩
    refine ⟨hS₁sub hχ, ?_⟩
    rcases hθirr with ⟨n, ρ, _hρirr, hθeq⟩
    have hχker : Section1.subgroupInKernel'
        (Section1.inducedCF (derivedSubgroup M) ρ.character) (H'.subgroupOf M) :=
      (Section1.proposition_1_6_a (derivedSubgroup M) (H'.subgroupOf M)
        (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred) ρ).mp
        (by simpa [hθeq] using hθker)
    simpa [hχeq, hθeq] using hχker
  · rintro ⟨hχS, hχker⟩
    rcases (hSbot.2 χ).mp hχS with ⟨θ, hθirr, _hθbot, hθne, hχeq⟩
    rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
    have hθker : Section1.subgroupInKernel' θ
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) := by
      rw [hθeq]
      apply (Section1.proposition_1_6_a (derivedSubgroup M) (H'.subgroupOf M)
        (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred) ρ).mpr
      simpa [hχeq, hθeq] using hχker
    exact (hS₁.2 χ).mpr ⟨θ, ⟨n, ρ, hρirr, hθeq⟩, hθker, hθne, hχeq⟩

public theorem exists_irreducible_inducing_muColumn_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (j : J) :
    ∃ θ : Section1.ClassFunction (derivedSubgroup M),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        muColumn μ j = Section1.inducedCF (derivedSubgroup M) θ := by
  rcases h with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, h45, _h48, _hTauA0,
        _hFull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  refine ⟨xChar j, h45a.2.1 j, ?_⟩
  simpa [muColumn, Section4Scratch.piColumn] using (h45a.2.2 j).symm

/-- Every Section 10 column is induced from `M'`, hence is supported on `M'`. -/
public theorem muColumn_supportedOn_derived_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (j : J) :
    Section1.supportedOn (muColumn μ j)
      ((derivedSubgroup M : Subgroup M) : Set M) := by
  rcases exists_irreducible_inducing_muColumn_of_section10FourSixNotationSupportedData
      h j with ⟨θ, _hθIrr, hcol⟩
  rw [hcol]
  exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ

public theorem muColumn_mem_of_hypothesis_10_1_supported_and_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    muColumn μ j ∈ S := by
  rcases h10 with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  rcases exists_supportedFourSixData_of_section10FourSixNotationSupportedData
      hnotation with
    ⟨H, σM, xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have h47full :
      Section4Scratch.theorem_4_7_full_statement
        (derivedSubgroup M) H A j0 μ xChar :=
    Section4Scratch.theorem_4_7_full
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := H)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46 h45a hω h43b h43c
  have hnonker :
      ¬ Section1.subgroupInKernel' (xChar j)
        (H.subgroupOf (derivedSubgroup M)) :=
    (h47full.2 j hj).1
  have hxNePrincipal :
      xChar j ≠ Section1.principalCharacter (derivedSubgroup M) := by
    intro hx
    apply hnonker
    rw [hx]
    intro a
    simp [Section1.degree, Section1.principalCharacter]
  exact (hS (muColumn μ j)).mpr
    ⟨xChar j, h45a.2.1 j, hxNePrincipal, by
      simpa [muColumn, Section4Scratch.piColumn] using (h45a.2.2 j).symm⟩

public theorem typeVReduction_hypothesis_4_6_Hprime_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ) :
    Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      W
      (H'.subgroupOf M)
      A := by
  have h46 :=
    hypothesis_4_6_derived_of_section10FourSixNotationSupportedData_of_late
      hred.1 (Or.inr (Or.inr hred.2.1)) hnotation
  rcases h46 with ⟨h42, _hKnormal, _hW2leK, _hKleK, hUnionK, hAsub⟩
  refine ⟨h42, typeVReduction_Hprime_subgroupOf_normal hred, ?_,
    typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred, ?_, hAsub⟩
  · rw [typeVReduction_W2_subgroupOf_eq_Hprime_subgroupOf hred]
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨h, hxcentral⟩
    have hHleK := typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred
    let k : {k : derivedSubgroup M // (k : M) ≠ 1} :=
      ⟨⟨(h.1 : M), hHleK h.1.2⟩, by
        simpa using h.2⟩
    exact hUnionK (Set.mem_iUnion.mpr ⟨k, by simpa [k] using hxcentral⟩)

public theorem muColumn_not_mem_typeV_kernelSubfamily_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    muColumn μ j ∉
      Section6.inducedKernelFamilyOf (derivedSubgroup M) (H'.subgroupOf M) S := by
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨σM, xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have h46Hprime :=
    typeVReduction_hypothesis_4_6_Hprime_of_section10FourSixNotationSupportedData
      hred hnotation
  have h47full :
      Section4Scratch.theorem_4_7_full_statement
        (derivedSubgroup M) (H'.subgroupOf M) A j0 μ xChar :=
    Section4Scratch.theorem_4_7_full
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := H'.subgroupOf M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46Hprime h45a hω h43b h43c
  have hnotSource :
      ¬ Section1.subgroupInKernel' (xChar j)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
    (h47full.2 j hj).1
  intro hmemS₁
  have hker :
      Section1.subgroupInKernel' (muColumn μ j) (H'.subgroupOf M) :=
    ((typeVReduction_kernelSubfamily_mem_iff_base_and_kernel_supported hred h10).mp
      hmemS₁).2
  rcases h45a.2.1 j with ⟨n, ρ, hρirr, hxEq⟩
  have hInd :
      Section1.inducedCF (derivedSubgroup M) ρ.character = muColumn μ j := by
    rw [← hxEq]
    simpa [muColumn, Section4Scratch.piColumn] using h45a.2.2 j
  have hkerInd :
      Section1.subgroupInKernel'
        (Section1.inducedCF (derivedSubgroup M) ρ.character)
        (H'.subgroupOf M) := by
    rw [hInd]
    exact hker
  have _ : (H'.subgroupOf M).Normal :=
    typeVReduction_Hprime_subgroupOf_normal hred
  have hsourceKer :
      Section1.subgroupInKernel' ρ.character
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) := by
    exact
      (Section1.proposition_1_6_a (derivedSubgroup M) (H'.subgroupOf M)
        (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred) ρ).mpr hkerInd
  exact hnotSource (by simpa [hxEq] using hsourceKer)

public theorem degree_muColumn_eq_prime_mul_card_W1_of_typeV_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    Section1.degree (muColumn μ j) = (p * Nat.card W1 : ℂ) := by
  rcases exists_irreducible_inducing_muColumn_of_section10FourSixNotationSupportedData
      hnotation j with ⟨θ, hθirr, hμeq⟩
  have hθdeg_ne : Section1.degree θ ≠ 1 := by
    intro hdeg
    have _ : (H'.subgroupOf M).Normal :=
      typeVReduction_Hprime_subgroupOf_normal hred
    have hkerTheta :
        Section1.subgroupInKernel' θ
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      typeVReduction_source_degree_one_subgroupInKernel_Hprime hred hθirr hdeg
    rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
    have hkerSource :
        Section1.subgroupInKernel' ρ.character
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) := by
      simpa [hθeq] using hkerTheta
    have hkerInd :
        Section1.subgroupInKernel'
          (Section1.inducedCF (derivedSubgroup M) ρ.character)
          (H'.subgroupOf M) := by
      exact
        (Section1.proposition_1_6_a (derivedSubgroup M) (H'.subgroupOf M)
          (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred) ρ).mp
          hkerSource
    have hkerMu :
        Section1.subgroupInKernel' (muColumn μ j) (H'.subgroupOf M) := by
      simpa [hμeq, hθeq] using hkerInd
    exact
      (muColumn_not_mem_typeV_kernelSubfamily_supported hred h10 hnotation hj)
        ((typeVReduction_kernelSubfamily_mem_iff_base_and_kernel_supported hred h10).mpr
          ⟨muColumn_mem_of_hypothesis_10_1_supported_and_section10FourSixNotationSupportedData
              h10 hnotation hj,
            hkerMu⟩)
  have hθdeg : Section1.degree θ = (p : ℂ) :=
    typeVReduction_source_degree_eq_prime_of_ne_one hred hθirr hθdeg_ne
  rw [hμeq, Section1.degree_inducedClassFunction, hθdeg]
  rw [derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10]
  norm_num [Nat.cast_mul]
  ring

public theorem theorem_4_10_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    Section4Scratch.theorem_4_10_statement i0 j0 ω σ μ
      (fun j => (δSign j : ℂ)) τ := by
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData h with
    ⟨σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  exact Section4Scratch.theorem_4_10
    (W1 := W1.subgroupOf M)
    (W2 := W2.subgroupOf M)
    (i0 := i0)
    (j0 := j0)
    (ω := ω)
    (σL := σM)
    (σ := σ)
    (piChar := μ)
    (deltaSign := fun j => (δSign j : ℂ))
    (τ := τ)
    hω h43b hTauCyc

public theorem exists_conjugate_muColumn_index_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J,
      j' ≠ j0 ∧
        Section1.conjugateCharacter (muColumn μ j) = muColumn μ j' ∧
          muColumn μ j' ≠ muColumn μ j := by
  rcases exists_supportedFourSixData_of_section10FourSixNotationSupportedData
      h with
    ⟨H, σM, xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have h47 :
      Section4Scratch.theorem_4_7_statement
        (derivedSubgroup M) H A :=
    Section4Scratch.theorem_4_7
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := H)
      (A := A)
      h46
  have h49a :
      Section4Scratch.theorem_4_9_a_statement A j0 j μ :=
    Section4Scratch.theorem_4_9_a
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := H)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (k := j)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      h46 h45a hω h43b h43c h47
  have hjMem : j ∈ Section4Scratch.equalDegreeColumnSet μ j0 j := ⟨hj, rfl⟩
  rcases (h49a hj).1 j hjMem with ⟨j', hj'Mem, hconj, hne⟩
  exact ⟨j', hj'Mem.1,
    by simpa [muColumn, Section4Scratch.piColumn] using hconj,
    by simpa [muColumn, Section4Scratch.piColumn] using hne⟩

public theorem baseColumn_degree_one_of_section10FourSixNotationSupportedData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ) :
    ∀ i, Section1.degree (μ i j0) = 1 := by
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData h with
    ⟨σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  exact Section4.proposition_4_4_baseColumn_degree_one
    (K := derivedSubgroup M)
    (W1 := W1.subgroupOf M)
    (W2 := W2.subgroupOf M)
    (W := W)
    (I := I)
    (J := J)
    (i0 := i0)
    (j0 := j0)
    (ω := ω)
    (σ := σM)
    (piChar := μ)
    (deltaSign := fun j => (δSign j : ℂ))
    h46.1 hω h43b h43c

public theorem degree_mu_of_typeV_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    {i : I} {j : J} (hj : j ≠ j0) :
    Section1.degree (μ i j) = (p : ℂ) := by
  have hsame : ∀ k : I,
      Section1.degree (μ k j) = Section1.degree (μ i j) := by
    intro k
    have hdegEq : ∀ a : I,
        Section1.degree (μ a j) = Section1.degree (μ i0 j) := by
      intro a
      rcases hnotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
          _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, h45, _h48, _htauA0, _hfull⟩
      rcases h45 with ⟨xChar, h45a, _h45b⟩
      rcases h45a with ⟨hres, _hirrX, _hindX⟩
      have ha := congrFun (hres a j) 1
      have h0 := congrFun (hres i0 j) 1
      calc
        Section1.degree (μ a j) = Section1.degree (xChar j) := by
          simpa [Section1.degree, Section1.subgroupRestriction] using ha
        _ = Section1.degree (μ i0 j) := by
          simpa [Section1.degree, Section1.subgroupRestriction] using h0.symm
    exact (hdegEq k).trans (hdegEq i).symm
  have hcolSum :
      Section1.degree (muColumn μ j) =
        (Fintype.card I : ℂ) * Section1.degree (μ i j) :=
    degree_muColumn_eq_card_mul_of_degree_eq hsame
  have hcolCount :
      Section1.degree (muColumn μ j) = (p * Nat.card W1 : ℂ) :=
    degree_muColumn_eq_prime_mul_card_W1_of_typeV_supported
      hred h10 hnotation hj
  have hcardI : Nat.card I = Nat.card W1 :=
    uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data h10 hnotation
  have hcardIC : (Fintype.card I : ℂ) = (Nat.card W1 : ℂ) := by
    exact_mod_cast (by
      simpa [Nat.card_eq_fintype_card] using hcardI :
        Fintype.card I = Nat.card W1)
  have hmul :
      (Nat.card W1 : ℂ) * Section1.degree (μ i j) =
        (Nat.card W1 : ℂ) * (p : ℂ) := by
    calc
      (Nat.card W1 : ℂ) * Section1.degree (μ i j) =
          (Fintype.card I : ℂ) * Section1.degree (μ i j) := by
        rw [hcardIC]
      _ = Section1.degree (muColumn μ j) := hcolSum.symm
      _ = (p * Nat.card W1 : ℂ) := hcolCount
      _ = (Nat.card W1 : ℂ) * (p : ℂ) := by
        norm_num [Nat.cast_mul]
        ring
  have hwpos : 0 < Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    omega
  have hwne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hwpos)
  exact mul_left_cancel₀ hwne hmul

public theorem deltaSign_eq_neg_one_of_typeVCharacterCountData_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    {j : J} (hj : j ≠ j0) :
    δSign j = -1 := by
  have hdeg :
      Section1.degree (μ i0 j) = (p : ℂ) :=
    degree_mu_of_typeV_supported hred h10 hnotation hj
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hσisoFull, _hσvirtFull, _hmaps, _hprincipal,
      _h2A, htail⟩
  rcases htail with
    ⟨_hωfull, h43b, _h43c, h43d, _h45a, _h45b, _htauTI, _htauA0,
      _htauIso, _htauPunct, _htauVirt, _hPF39⟩
  rcases h43d i0 j with ⟨a, hcongRaw⟩
  have hcard : Fintype.card (W1.subgroupOf M) = Fintype.card W1 :=
    Fintype.card_congr (Subgroup.subgroupOfEquivOfLe hW1M).toEquiv
  have hcong :
      Section1.degree (μ i0 j) =
        (δSign j : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ)) := by
    simpa [Nat.card_eq_fintype_card, hcard] using hcongRaw
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  rcases hred with
    ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
      _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, hW1Odd, hW1gt,
      _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
  have hW1ge3 : 3 ≤ Nat.card W1 := by
    rcases hW1Odd with ⟨k, hk⟩
    omega
  have hEqC :
      (p : ℂ) = (δSign j : ℂ) + (a : ℂ) * (Nat.card W1 : ℂ) :=
    hdeg.symm.trans hcong
  have hEqZ :
      (p : ℤ) = δSign j + a * (Nat.card W1 : ℤ) := by
    exact_mod_cast hEqC
  have hpZ : (p : ℤ) = 2 * (Nat.card W1 : ℤ) - 1 := by
    rw [hpEq]
    have hle : 1 ≤ 2 * Nat.card W1 := by omega
    rw [Nat.cast_sub hle]
    norm_num [Nat.cast_mul]
  have hsignC : Section1.IsSign ((δSign j : ℂ)) := h43b.2.1 j
  rw [Section1.IsSign] at hsignC
  rcases hsignC with hδ | hδ
  · have hδZ : δSign j = 1 := by exact_mod_cast hδ
    rw [hδZ] at hEqZ
    have hdiv : (Nat.card W1 : ℤ) ∣ (2 : ℤ) := by
      use 2 - a
      nlinarith [hEqZ, hpZ]
    have hdivNat : Nat.card W1 ∣ 2 := by
      exact Int.natCast_dvd_natCast.mp hdiv
    have hle2 : Nat.card W1 ≤ 2 := Nat.le_of_dvd (by omega) hdivNat
    omega
  · exact_mod_cast hδ

public theorem typeVAlpha_supportedOn_a0_of_typeVCharacterCountData_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    {i : I} {j : J} (hj : j ≠ j0) :
    Section1.supportedOn (alphaChar μ ζ n δ j0 i j) A0 := by
  have hdegmu :
      Section1.degree (μ i j) = (p : ℂ) :=
    degree_mu_of_typeV_supported hred h10 hnotation hj
  have hbase : Section1.degree (μ i j0) = 1 :=
    baseColumn_degree_one_of_section10FourSixNotationSupportedData hnotation i
  rcases hcount with ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, hδ, hn⟩
  have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) :=
    (hS1irr ζ hζ).2
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  have hW1gt : 1 < Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    exact hW1gt
  have hpC : (p : ℂ) = (2 : ℂ) * (Nat.card W1 : ℂ) - 1 := by
    rw [hpEq]
    have hle : 1 ≤ 2 * Nat.card W1 := by omega
    rw [Nat.cast_sub hle]
    norm_num [Nat.cast_mul]
  have hαdeg :
      Section1.degree (alphaChar μ ζ n δ j0 i j) = 0 := by
    have hdegmu_apply : μ i j 1 = (p : ℂ) := by
      simpa [Section1.degree] using hdegmu
    have hbase_apply : μ i j0 1 = 1 := by
      simpa [Section1.degree] using hbase
    have hζ_apply : ζ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hζdeg
    unfold alphaChar Section1.degree
    simp [hdegmu_apply, hbase_apply, hζ_apply, hδ, hn, hpC]
  have h46 :=
    hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hnotation
  have hA0punct : Section4Scratch.puncturedSet ⊆ A0 := by
    rcases hnotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, hA0, _h46Selected, _h33, _hIso, _hVirt, _hPrin,
        _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull⟩
    intro x hx
    rw [hA0]
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46 hx
  exact supportedOn_of_degree_eq_zero_of_punctured_subset hA0punct hαdeg

public theorem typeVAlpha_supportedOn_primeDadeA0_of_typeVCharacterCountData_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    {i : I} {j : J} (hj : j ≠ j0) :
    Section1.supportedOn (alphaChar μ ζ n δ j0 i j)
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  have hdegmu : Section1.degree (μ i j) = (p : ℂ) :=
    degree_mu_of_typeV_supported hred h10 hnotation hj
  have hbase : Section1.degree (μ i j0) = 1 :=
    baseColumn_degree_one_of_section10FourSixNotationSupportedData hnotation i
  have hcountAll := hcount
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, hδ, hn⟩
  have hζIrr : Section1.IsIrreducibleCharacterOnGroup ζ := (hS1irr ζ hζ).1
  have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) := (hS1irr ζ hζ).2
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  have hpC : (p : ℂ) = (2 : ℂ) * (Nat.card W1 : ℂ) - 1 := by
    rw [hpEq]
    have hle : 1 ≤ 2 * Nat.card W1 := by
      rcases hred with
        ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
          _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
          _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
      omega
    rw [Nat.cast_sub hle]
    norm_num [Nat.cast_mul]
  have hαdeg : Section1.degree (alphaChar μ ζ n δ j0 i j) = 0 := by
    have hdegmu_apply : μ i j 1 = (p : ℂ) := by
      simpa [Section1.degree] using hdegmu
    have hbase_apply : μ i j0 1 = 1 := by
      simpa [Section1.degree] using hbase
    have hζ_apply : ζ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hζdeg
    unfold alphaChar Section1.degree
    simp [hdegmu_apply, hbase_apply, hζ_apply, hδ, hn, hpC]
  have hζS : ζ ∈ S := typeVCharacterCount_sOne_subset hcountAll hζ
  have hζDerived :=
    supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
      h10 hζS
  have hδSignJ : δSign j = -1 :=
    deltaSign_eq_neg_one_of_typeVCharacterCountData_supported
      hred h10 hcountAll hnotation hj
  have hδjZ : δSign j = δ := by
    rw [hδSignJ, hδ]
  have hδj : (δSign j : ℂ) = (δ : ℂ) := by
    exact_mod_cast hδjZ
  exact alphaChar_supportedOn_primeDadeA0_of_bridge_data
    hnotation
      (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hnotation)
      hζIrr hζDerived hαdeg hδj

public theorem theorem_10_10_4_muColumn_gram_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (j k : J) :
    Section1.scalarProduct M (muColumn μ j) (muColumn μ k) =
      if j = k then (Fintype.card I : ℂ) else 0 := by
  classical
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  unfold muColumn
  have hsumj :
      ((∑ i : I, μ i j : Section1.ClassFunction M)) =
        fun g => ∑ i : I, μ i j g := by
    ext g
    simp
  have hsumk :
      ((∑ i : I, μ i k : Section1.ClassFunction M)) =
        fun g => ∑ i : I, μ i k g := by
    ext g
    simp
  rw [hsumj, Section1.scalarProduct_fintype_sum_left]
  by_cases hjk : j = k
  · subst k
    calc
      ∑ i : I, Section1.scalarProduct M (μ i j) (∑ p : I, μ p j) =
          ∑ i : I, Section1.scalarProduct M (μ i j)
            (fun g => ∑ p : I, μ p j g) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hsumj]
      _ =
          ∑ i : I, ∑ p : I, Section1.scalarProduct M (μ i j) (μ p j) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
      _ =
          ∑ i : I, ∑ p : I, if i = p then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro p _hp
            by_cases hip : i = p
            · subst p
              simpa using scalarProduct_irreducible_self (hirr i j)
            · simpa [hip] using
                scalarProduct_irreducible_ne (hirr i j) (hirr p j)
                  (hdistinct (i, j) (p, j) (by
                    intro hEq
                    exact hip (congrArg Prod.fst hEq)))
      _ = if j = j then (Fintype.card I : ℂ) else 0 := by
            simp
  · calc
      ∑ i : I, Section1.scalarProduct M (μ i j) (∑ p : I, μ p k) =
          ∑ i : I, Section1.scalarProduct M (μ i j)
            (fun g => ∑ p : I, μ p k g) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hsumk]
      _ =
          ∑ i : I, ∑ p : I, Section1.scalarProduct M (μ i j) (μ p k) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [Section1.scalarProduct_fintype_sum_right]
      _ =
          ∑ i : I, ∑ p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            refine Finset.sum_congr rfl ?_
            intro p _hp
            simpa using
              scalarProduct_irreducible_ne (hirr i j) (hirr p k)
                (hdistinct (i, j) (p, k) (by
                  intro hEq
                  exact hjk (congrArg Prod.snd hEq)))
      _ = if j = k then (Fintype.card I : ℂ) else 0 := by
            simp [hjk]

public theorem theorem_10_10_4_mu_entry_muColumn_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (i : I) (j k : J) :
    Section1.scalarProduct M (μ i j) (muColumn μ k) =
      if j = k then 1 else 0 :=
  theorem_10_9_mu_entry_muColumn_supported hnotation i j k

public theorem theorem_10_10_4_nonbase_index_exists
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {j0 : J}
    {μ : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ)
    (η : S)
    (hη : (η : Section1.ClassFunction M) ∉ S₁) :
    ∃ j : J, j ≠ j0 ∧ (η : Section1.ClassFunction M) = μ j := by
  rcases hcount with ⟨_hJ, hdecomp, _hS1card, _hS1irr, _hmu, _hd, _hδ, _hn⟩
  rcases (hdecomp (η : Section1.ClassFunction M)).mp η.2 with hbase | hnonbase
  · exact False.elim (hη hbase)
  · exact hnonbase

public noncomputable def theorem_10_10_4_countImage
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {j0 : J}
    {μ : J → Section1.ClassFunction M}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ)
    (τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (target : J → Section1.ClassFunction G)
    (η : S) : Section1.ClassFunction G := by
  classical
  exact
    if hη : (η : Section1.ClassFunction M) ∈ S₁ then
      τ₁ (η : Section1.ClassFunction M)
    else
      target (Classical.choose
        (theorem_10_10_4_nonbase_index_exists hcount η hη))

public theorem theorem_10_10_4_map_evalCoeff
    {L : Type u}
    [Group L]
    {G : Type u}
    [Group G]
    {ι : Type*}
    [Fintype ι]
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (μ : ι → Section1.ClassFunction L)
    (v : Section1.CoeffVector ι) :
    T (Section1.evalCoeff μ v) =
      Section1.evalCoeff (fun i => T (μ i)) v := by
  ext g
  simp [Section1.evalCoeff, Finset.sum_apply]

public theorem theorem_10_10_4_agreesOnIntegerSpanOn_of_weighted_formula
    {G : Type u}
    [Group G]
    [Finite G]
    {J : Type*}
    [Fintype J]
    {M W1 : Subgroup G}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ τ₁ Tnew : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    {j0 : J}
    {μ : J → Section1.ClassFunction M}
    {target : J → Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μ p d n δ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hformula : ∀ j : J, j ≠ j0 →
      τ (μ j - (d : ℂ) • ζ) = target j - (d : ℂ) • τ₁ ζ)
    (hTnew : ∀ η : S,
      Tnew (η : Section1.ClassFunction M) =
        theorem_10_10_4_countImage hcount τ₁ target η) :
    Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ Tnew := by
  classical
  intro χ hχ
  rcases hχ with ⟨hχspan, hχon⟩
  rcases hχspan with ⟨v, hv⟩
  let μS : S → Section1.ClassFunction M :=
    fun η => (η : Section1.ClassFunction M)
  let q : S → ℂ :=
    fun η => if (η : Section1.ClassFunction M) ∈ S₁ then 1 else (d : ℂ)
  let B : Section1.ClassFunction G := τ₁ ζ - τ ζ
  let s : ℂ := ∑ η : S, (v η : ℂ) * q η
  have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hdegree_q :
      ∀ η : S,
        Section1.degree (η : Section1.ClassFunction M) =
          q η * (Nat.card W1 : ℂ) := by
    intro η
    by_cases hη : (η : Section1.ClassFunction M) ∈ S₁
    · rcases hcount with
        ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
      have hdeg :
          Section1.degree (η : Section1.ClassFunction M) =
            (Nat.card W1 : ℂ) :=
        (hS1irr (η : Section1.ClassFunction M) hη).2
      simp [q, hη, hdeg]
    · rcases theorem_10_10_4_nonbase_index_exists hcount η hη with
        ⟨j, hj, hηeq⟩
      rcases hcount with
        ⟨_hJ, _hdecomp, _hS1card, _hS1irr, hmu, hd, _hδ, _hn⟩
      have hdeg :
          Section1.degree (η : Section1.ClassFunction M) =
            (d : ℂ) * (Nat.card W1 : ℂ) := by
        calc
          Section1.degree (η : Section1.ClassFunction M) =
              Section1.degree (μ j) := by rw [hηeq]
          _ = (p * Nat.card W1 : ℂ) := (hmu j hj).2
          _ = (d : ℂ) * (Nat.card W1 : ℂ) := by
                rw [hd]
      simpa [q, hη] using hdeg
  have hdegχ : Section1.degree χ = 0 :=
    (Section5.supportedOn_puncturedSet_iff_degree_eq_zero χ).1 hχon
  have hdeg_eval :
      Section1.degree χ =
        ∑ η : S,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction M)) := by
    rw [hv, Section1.evalCoeff, Section1.degree_apply]
    simp [Section1.degree_apply]
  have hfactor :
      (∑ η : S,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction M))) =
        s * (Nat.card W1 : ℂ) := by
    calc
      (∑ η : S,
          ((v η : ℂ) *
            Section1.degree (η : Section1.ClassFunction M))) =
          ∑ η : S, ((v η : ℂ) * q η * (Nat.card W1 : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro η _hη
            rw [hdegree_q η]
            ring
      _ = s * (Nat.card W1 : ℂ) := by
            simp [s, Finset.sum_mul, mul_assoc]
  have hs0 : s = 0 := by
    have hs_mul : s * (Nat.card W1 : ℂ) = 0 := by
      rw [← hfactor, ← hdeg_eval, hdegχ]
    exact (mul_eq_zero.mp hs_mul).resolve_right hW1ne
  have hsplit :
      ∀ η : S,
        Tnew (η : Section1.ClassFunction M) =
          τ (η : Section1.ClassFunction M) + q η • B := by
    intro η
    by_cases hη : (η : Section1.ClassFunction M) ∈ S₁
    · have hT :
          Tnew (η : Section1.ClassFunction M) =
            τ₁ (η : Section1.ClassFunction M) := by
        simpa [theorem_10_10_4_countImage, hη] using hTnew η
      have hsub :
          τ₁ ((η : Section1.ClassFunction M) - ζ) =
            τ ((η : Section1.ClassFunction M) - ζ) :=
        typeVCoherentSubfamilyData_agreesOn_sub hcount hτ₁ hη hζ
      have hbase :
          τ₁ (η : Section1.ClassFunction M) =
            τ (η : Section1.ClassFunction M) + B := by
        ext g
        have hsub_g := congrArg (fun f : Section1.ClassFunction G => f g) hsub
        simp [B, Pi.sub_apply] at hsub_g ⊢
        calc
          τ₁ (η : Section1.ClassFunction M) g =
              (τ₁ (η : Section1.ClassFunction M) g - τ₁ ζ g) + τ₁ ζ g := by
                ring
          _ = (τ (η : Section1.ClassFunction M) g - τ ζ g) + τ₁ ζ g := by
                rw [hsub_g]
          _ = τ (η : Section1.ClassFunction M) g + (τ₁ ζ g - τ ζ g) := by
                ring
      rw [hT, hbase]
      simp [q, hη]
    · let jη : J :=
        Classical.choose (theorem_10_10_4_nonbase_index_exists hcount η hη)
      have hjη : jη ≠ j0 :=
        (Classical.choose_spec
          (theorem_10_10_4_nonbase_index_exists hcount η hη)).1
      have hηeq : (η : Section1.ClassFunction M) = μ jη :=
        (Classical.choose_spec
          (theorem_10_10_4_nonbase_index_exists hcount η hη)).2
      have hT :
          Tnew (η : Section1.ClassFunction M) = target jη := by
        simpa [theorem_10_10_4_countImage, hη, jη] using hTnew η
      have htarget :
          target jη =
            τ (η : Section1.ClassFunction M) + (d : ℂ) • B := by
        rw [hηeq]
        ext g
        have hformula_g :=
          congrArg (fun f : Section1.ClassFunction G => f g)
            (hformula jη hjη)
        simp [B, Pi.sub_apply, Pi.smul_apply] at hformula_g ⊢
        calc
          target jη g =
              (target jη g - (d : ℂ) * τ₁ ζ g) +
                (d : ℂ) * τ₁ ζ g := by
                ring
          _ = (τ (μ jη) g - (d : ℂ) * τ ζ g) +
                (d : ℂ) * τ₁ ζ g := by
                rw [← hformula_g]
          _ = τ (μ jη) g + (d : ℂ) * (τ₁ ζ g - τ ζ g) := by
                ring
      rw [hT, htarget]
      simp [q, hη]
  have htarget_eval :
      Section1.evalCoeff
          (fun η : S => Tnew (η : Section1.ClassFunction M)) v =
        Section1.evalCoeff
          (fun η : S => τ (η : Section1.ClassFunction M)) v + s • B := by
    have hsplit_eval :
        Section1.evalCoeff
            (fun η : S => Tnew (η : Section1.ClassFunction M)) v =
          Section1.evalCoeff
            (fun η : S =>
              τ (η : Section1.ClassFunction M) + q η • B) v := by
      congr 1
      funext η
      exact hsplit η
    rw [hsplit_eval]
    ext g
    simp [Section1.evalCoeff, s, Pi.add_apply, Pi.smul_apply,
      Finset.sum_add_distrib, mul_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro η _hη
    ring
  have hτeval :
      Section1.evalCoeff
          (fun η : S => τ (η : Section1.ClassFunction M)) v =
        τ χ := by
    rw [hv]
    exact (theorem_10_10_4_map_evalCoeff τ μS v).symm
  calc
    Tnew χ = Tnew (Section1.evalCoeff μS v) := by rw [hv]
    _ = Section1.evalCoeff
          (fun η : S => Tnew (η : Section1.ClassFunction M)) v := by
          exact theorem_10_10_4_map_evalCoeff Tnew μS v
    _ = Section1.evalCoeff
          (fun η : S => τ (η : Section1.ClassFunction M)) v + s • B := htarget_eval
    _ = τ χ + s • B := by rw [hτeval]
    _ = τ χ := by rw [hs0, zero_smul, add_zero]


public theorem theorem_10_10_4_nonbase_formula_from_base_and_alpha_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμcol : ∀ j, μcol j = muColumn μ j)
    (hbase : τ (μcol j0 - ζ) =
      Section4Scratch.omegaColumnSigma σ ω j0 - τ₁ ζ)
    (halpha : typeVAlphaFormulaData W A0 j0 μ ω σ ζ τ τ₁ n δ)
    {j : J}
    (hj : j ≠ j0) :
    τ (μcol j - (d : ℂ) • ζ) =
      (δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω j -
        (d : ℂ) • τ₁ ζ := by
  classical
  have hIcard : Nat.card I = Nat.card W1 :=
    uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data h10 hnotation
  have hIcardC : (Fintype.card I : ℂ) = (Nat.card W1 : ℂ) := by
    exact_mod_cast (by
      simpa [Nat.card_eq_fintype_card] using hIcard :
        Fintype.card I = Nat.card W1)
  have hdnC :
      (d : ℂ) = (n : ℂ) * (Fintype.card I : ℂ) + (δ : ℂ) := by
    have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, _hS1irr, _hmu, hd, hδ, hn⟩
    rw [hd, hn, hδ, hIcardC]
    rw [hpEq]
    have hle : 1 ≤ 2 * Nat.card W1 := by
      rcases hred with
        ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
          _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
          _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
      omega
    rw [Nat.cast_sub hle, Nat.cast_mul]
    norm_num
    ring
  have hsum_alpha :
      (∑ i : I, alphaChar μ ζ n δ j0 i j) =
        (μcol j - (d : ℂ) • ζ) -
          (δ : ℂ) • (μcol j0 - ζ) := by
    rw [hμcol j, hμcol j0]
    ext x
    simp [alphaChar, muColumn, Pi.sub_apply, Pi.smul_apply,
      Finset.sum_sub_distrib, hdnC]
    rw [← Finset.mul_sum]
    ring
  have hsum_tau :
      τ (∑ i : I, alphaChar μ ζ n δ j0 i j) =
        (δ : ℂ) •
            (Section4Scratch.omegaColumnSigma σ ω j -
              Section4Scratch.omegaColumnSigma σ ω j0) -
          ((Fintype.card I : ℂ) * (n : ℂ)) • τ₁ ζ := by
    calc
      τ (∑ i : I, alphaChar μ ζ n δ j0 i j)
          = ∑ i : I, τ (alphaChar μ ζ n δ j0 i j) := by
            rw [map_sum]
      _ = ∑ i : I,
          ((δ : ℂ) • (σ (ω i j) - σ (ω i j0)) -
            (n : ℂ) • τ₁ ζ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact (halpha i j hj).2
      _ = (δ : ℂ) •
            (Section4Scratch.omegaColumnSigma σ ω j -
              Section4Scratch.omegaColumnSigma σ ω j0) -
          ((Fintype.card I : ℂ) * (n : ℂ)) • τ₁ ζ := by
            unfold Section4Scratch.omegaColumnSigma
            ext x
            simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            rw [← Finset.mul_sum]
            rw [Finset.sum_sub_distrib]
            ring
  have hsource_tau :
      τ (∑ i : I, alphaChar μ ζ n δ j0 i j) =
        τ (μcol j - (d : ℂ) • ζ) -
          (δ : ℂ) • τ (μcol j0 - ζ) := by
    rw [hsum_alpha, map_sub, map_smul]
  have hsolve :
      τ (μcol j - (d : ℂ) • ζ) =
        τ (∑ i : I, alphaChar μ ζ n δ j0 i j) +
          (δ : ℂ) • τ (μcol j0 - ζ) := by
    rw [hsource_tau]
    abel
  rw [hsolve, hsum_tau, hbase]
  ext x
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hdnC]
  ring


public theorem theorem_10_10_4_image_family_from_supported_notation_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {μcol : J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0 μcol p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμcol : ∀ j, μcol j = muColumn μ j)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁)
    (hμformula : ∀ j : J, j ≠ j0 →
      τ (μcol j - (d : ℂ) • ζ) =
        (δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω j -
          (d : ℂ) • τ₁ ζ) :
    ∃ img : S → Section1.ClassFunction G,
      (∀ η : S, IsVirtualCharacter (img η)) ∧
        (∀ η ξ : S,
          Section1.scalarProduct G (img η) (img ξ) =
            Section1.scalarProduct M (η : Section1.ClassFunction M)
              (ξ : Section1.ClassFunction M)) ∧
        (∀ Tnew : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          (∀ η : S, Tnew (η : Section1.ClassFunction M) = img η) →
            Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ Tnew) := by
  classical
  let target : J → Section1.ClassFunction G :=
    fun j => (δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω j
  let img : S → Section1.ClassFunction G :=
    theorem_10_10_4_countImage hcount τ₁ target
  have hδ : δ = -1 := by
    rcases hcount with ⟨_hJ, _hdecomp, _hS1card, _hS1irr, _hmu, _hd, hδ, _hn⟩
    exact hδ
  refine ⟨img, ?_, ?_, ?_⟩
  · intro η
    by_cases hη : (η : Section1.ClassFunction M) ∈ S₁
    · let η₁ : S₁ := ⟨(η : Section1.ClassFunction M), hη⟩
      have himg : img η = τ₁ (η : Section1.ClassFunction M) := by
        simp [img, theorem_10_10_4_countImage, target, hη]
      rw [himg]
      exact theorem_10_10_4_tauOne_sOne_virtual hτ₁ η₁
    · let jη : J :=
        Classical.choose (theorem_10_10_4_nonbase_index_exists hcount η hη)
      have himg : img η = target jη := by
        simp [img, theorem_10_10_4_countImage, target, hη, jη]
      rw [himg]
      exact isVirtualCharacter_intCast_smul_sec10 δ (theorem_10_10_4_omegaColumnSigma_virtual_supported hnotation jη)
  · intro η ξ
    by_cases hη : (η : Section1.ClassFunction M) ∈ S₁
    · by_cases hξ : (ξ : Section1.ClassFunction M) ∈ S₁
      · let η₁ : S₁ := ⟨(η : Section1.ClassFunction M), hη⟩
        let ξ₁ : S₁ := ⟨(ξ : Section1.ClassFunction M), hξ⟩
        have himgη : img η = τ₁ (η : Section1.ClassFunction M) := by
          simp [img, theorem_10_10_4_countImage, target, hη]
        have himgξ : img ξ = τ₁ (ξ : Section1.ClassFunction M) := by
          simp [img, theorem_10_10_4_countImage, target, hξ]
        rw [himgη, himgξ]
        exact theorem_10_10_4_tauOne_sOne_gram hτ₁ η₁ ξ₁
      · let η₁ : S₁ := ⟨(η : Section1.ClassFunction M), hη⟩
        let jξ : J :=
          Classical.choose (theorem_10_10_4_nonbase_index_exists hcount ξ hξ)
        have hjξ : jξ ≠ j0 :=
          (Classical.choose_spec
            (theorem_10_10_4_nonbase_index_exists hcount ξ hξ)).1
        have hξeq : (ξ : Section1.ClassFunction M) = μcol jξ :=
          (Classical.choose_spec
            (theorem_10_10_4_nonbase_index_exists hcount ξ hξ)).2
        have himgη : img η = τ₁ (η : Section1.ClassFunction M) := by
          simp [img, theorem_10_10_4_countImage, target, hη]
        have himgξ : img ξ = target jξ := by
          simp [img, theorem_10_10_4_countImage, target, hξ, jξ]
        have htarget :
            Section1.scalarProduct G
                (τ₁ (η : Section1.ClassFunction M)) (target jξ) = 0 := by
          simpa [target] using
            theorem_10_10_4_tauOne_sOne_signed_omegaColumnSigma_orthogonal_supported
              hred h10 hcount hnotation hτ₁ η₁ jξ
        have hsource :
            Section1.scalarProduct M (η : Section1.ClassFunction M)
                (μcol jξ) = 0 :=
          theorem_10_10_4_sOne_mu_orthogonal_supported hred h10 hcount η₁ hjξ
        rw [himgη, himgξ, htarget]
        simpa [hξeq] using hsource.symm
    · by_cases hξ : (ξ : Section1.ClassFunction M) ∈ S₁
      · let ξ₁ : S₁ := ⟨(ξ : Section1.ClassFunction M), hξ⟩
        let jη : J :=
          Classical.choose (theorem_10_10_4_nonbase_index_exists hcount η hη)
        have hjη : jη ≠ j0 :=
          (Classical.choose_spec
            (theorem_10_10_4_nonbase_index_exists hcount η hη)).1
        have hηeq : (η : Section1.ClassFunction M) = μcol jη :=
          (Classical.choose_spec
            (theorem_10_10_4_nonbase_index_exists hcount η hη)).2
        have himgη : img η = target jη := by
          simp [img, theorem_10_10_4_countImage, target, hη, jη]
        have himgξ : img ξ = τ₁ (ξ : Section1.ClassFunction M) := by
          simp [img, theorem_10_10_4_countImage, target, hξ]
        have htargetForward :
            Section1.scalarProduct G
                (τ₁ (ξ : Section1.ClassFunction M)) (target jη) = 0 := by
          simpa [target] using
            theorem_10_10_4_tauOne_sOne_signed_omegaColumnSigma_orthogonal_supported
              hred h10 hcount hnotation hτ₁ ξ₁ jη
        have htarget :
            Section1.scalarProduct G (target jη)
                (τ₁ (ξ : Section1.ClassFunction M)) = 0 := by
          simpa [Section1.scalarProduct_star_swap] using congrArg star htargetForward
        have hsourceForward :
            Section1.scalarProduct M (ξ : Section1.ClassFunction M)
                (μcol jη) = 0 :=
          theorem_10_10_4_sOne_mu_orthogonal_supported hred h10 hcount ξ₁ hjη
        have hsource :
            Section1.scalarProduct M (μcol jη)
                (ξ : Section1.ClassFunction M) = 0 := by
          simpa [Section1.scalarProduct_star_swap] using congrArg star hsourceForward
        rw [himgη, himgξ, htarget]
        simpa [hηeq] using hsource.symm
      · let jη : J :=
          Classical.choose (theorem_10_10_4_nonbase_index_exists hcount η hη)
        let jξ : J :=
          Classical.choose (theorem_10_10_4_nonbase_index_exists hcount ξ hξ)
        have hηeq : (η : Section1.ClassFunction M) = μcol jη :=
          (Classical.choose_spec
            (theorem_10_10_4_nonbase_index_exists hcount η hη)).2
        have hξeq : (ξ : Section1.ClassFunction M) = μcol jξ :=
          (Classical.choose_spec
            (theorem_10_10_4_nonbase_index_exists hcount ξ hξ)).2
        have himgη : img η = target jη := by
          simp [img, theorem_10_10_4_countImage, target, hη, jη]
        have himgξ : img ξ = target jξ := by
          simp [img, theorem_10_10_4_countImage, target, hξ, jξ]
        rw [himgη, himgξ]
        calc
          Section1.scalarProduct G (target jη) (target jξ) =
              (if jη = jξ then (Fintype.card I : ℂ) else 0) := by
                simpa [target] using
                  theorem_10_10_4_signed_omegaColumnSigma_gram_supported
                    hnotation hδ jη jξ
          _ = Section1.scalarProduct M (η : Section1.ClassFunction M)
                (ξ : Section1.ClassFunction M) := by
                rw [hηeq, hξeq, hμcol jη, hμcol jξ]
                exact (theorem_10_10_4_muColumn_gram_supported hnotation jη jξ).symm
  · intro Tnew hTnew
    exact theorem_10_10_4_agreesOnIntegerSpanOn_of_weighted_formula
      hcount hζ hτ₁ hμformula hTnew


public theorem centralizer_derivedSubgroup_eq_W2_of_hypothesis_10_1_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    ∀ x : W1.subgroupOf M, x ≠ 1 →
      Section2.centralizerIn (derivedSubgroup M) (x : M) = W2.subgroupOf M := by
  intro x hx
  exact (hypothesis_4_2_of_hypothesis_10_1_supported_data h).2.2.2.2.2.2.1 x hx

public theorem typeVReduction_kernelSubfamily_degree_eq_card_W1_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    {χ : Section1.ClassFunction M}
    (hχ : χ ∈ Section6.inducedKernelFamilyOf
      (derivedSubgroup M) (H'.subgroupOf M) S) :
    Section1.degree χ = (Nat.card W1 : ℂ) := by
  have hnormal : (H'.subgroupOf M).Normal :=
    typeVReduction_Hprime_subgroupOf_normal hred
  have _ : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
    hnormal.subgroupOf (derivedSubgroup M)
  have hcomm : IsMulCommutative
      (derivedSubgroup M ⧸ (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) := by
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    exact le_rfl
  have hdeg :=
    Section6.inducedKernelFamily_degree_eq_relIndex_of_quotient_commutative
      (Section6.inducedKernelFamilyOf_isFamily
        (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
        (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred)) hnormal hcomm hχ
  rw [Subgroup.relIndex_top_right] at hdeg
  rw [derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10] at hdeg
  exact hdeg

public theorem typeVReduction_kernelSubfamily_source_degree_eq_one_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    {χ : Section1.ClassFunction M}
    (hχ : χ ∈ Section6.inducedKernelFamilyOf
      (derivedSubgroup M) (H'.subgroupOf M) S) :
    ∃ θ : Section1.ClassFunction (derivedSubgroup M),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.subgroupInKernel' θ
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) ∧
        θ ≠ Section1.principalCharacter (derivedSubgroup M) ∧
        χ = Section1.inducedCF (derivedSubgroup M) θ ∧
        Section1.degree θ = 1 := by
  classical
  have hS₁ :
      Section6.inducedKernelFamily (derivedSubgroup M) (H'.subgroupOf M)
        (Section6.inducedKernelFamilyOf
          (derivedSubgroup M) (H'.subgroupOf M) S) :=
    Section6.inducedKernelFamilyOf_isFamily
      (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
      (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred)
  rcases (hS₁.2 χ).mp hχ with ⟨θ, hθirr, hθker, hθne, hχeq⟩
  have hχdeg :
      Section1.degree (Section1.inducedCF (derivedSubgroup M) θ) =
        (Nat.card W1 : ℂ) := by
    simpa [hχeq] using
      typeVReduction_kernelSubfamily_degree_eq_card_W1_supported hred h10 hχ
  have hindDeg :
      Section1.degree (Section1.inducedCF (derivedSubgroup M) θ) =
        (Nat.card W1 : ℂ) * Section1.degree θ := by
    rw [Section1.degree_inducedClassFunction]
    rw [derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10]
  have hmul :
      (Nat.card W1 : ℂ) * Section1.degree θ =
        (Nat.card W1 : ℂ) * 1 := by
    rw [← hindDeg, hχdeg]
    simp
  have hwpos : 0 < Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    omega
  have hwne : (Nat.card W1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hwpos)
  exact ⟨θ, hθirr, hθker, hθne, hχeq, mul_left_cancel₀ hwne hmul⟩

public theorem typeVReduction_kernelSubfamily_mem_iff_exists_quotientCharacter_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    [((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal]
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    {χ : Section1.ClassFunction M} :
    χ ∈ Section6.inducedKernelFamilyOf
        (derivedSubgroup M) (H'.subgroupOf M) S ↔
      ∃ ψ : (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ,
        ψ ≠ 1 ∧
          χ = Section1.inducedCF (derivedSubgroup M)
            (Section1.quotientCharacterInflation (H'.subgroupOf M)
              (derivedSubgroup M) ψ) := by
  classical
  constructor
  · intro hχ
    rcases typeVReduction_kernelSubfamily_source_degree_eq_one_supported
        hred h10 hχ with
      ⟨θ, hθirr, hθker, hθne, hχeq, hθdeg⟩
    rcases exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
        (H'.subgroupOf M) (derivedSubgroup M) hθirr hθker hθdeg with
      ⟨ψ, hθψ⟩
    refine ⟨ψ, ?_, ?_⟩
    · intro hψone
      apply hθne
      rw [hθψ, hψone]
      ext x
      rfl
    · exact hχeq.trans (congrArg (Section1.inducedCF (derivedSubgroup M)) hθψ)
  · rintro ⟨ψ, hψne, rfl⟩
    have hS₁ :
        Section6.inducedKernelFamily (derivedSubgroup M) (H'.subgroupOf M)
          (Section6.inducedKernelFamilyOf
            (derivedSubgroup M) (H'.subgroupOf M) S) :=
      Section6.inducedKernelFamilyOf_isFamily
      (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
      (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred)
    refine (hS₁.2 _).mpr ?_
    exact ⟨Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) ψ,
      Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
        (H'.subgroupOf M) (derivedSubgroup M) ψ,
      Section6.subgroupInKernel'_quotientCharacterInflation
        (H'.subgroupOf M) (derivedSubgroup M) ψ,
      Section6.quotientCharacterInflation_ne_principal_of_ne_one
        (H'.subgroupOf M) (derivedSubgroup M) hψne,
      rfl⟩

public theorem typeVReduction_coprime_zpowers_W1_Hprime_subgroupOf_derived_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (a : W1.subgroupOf M) :
    Nat.Coprime (Nat.card (Subgroup.zpowers (a : M)))
      (Nat.card ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))) := by
  have hleW1M : Subgroup.zpowers (a : M) ≤ W1.subgroupOf M :=
    (Subgroup.zpowers_le).2 a.2
  have hdvdSub :
      Nat.card (Subgroup.zpowers (a : M)) ∣ Nat.card (W1.subgroupOf M) :=
    Subgroup.card_dvd_of_le hleW1M
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hcardW1Sub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hdvd : Nat.card (Subgroup.zpowers (a : M)) ∣ Nat.card W1 := by
    rw [← hcardW1Sub]
    exact hdvdSub
  have hcopW1p : Nat.Coprime (Nat.card W1) p :=
    typeVReduction_coprime_card_W1_prime hred
  have hcopSubP : Nat.Coprime (Nat.card (Subgroup.zpowers (a : M))) p :=
    Nat.Coprime.coprime_dvd_left hdvd hcopW1p
  have hcardH :
      Nat.card ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) = p :=
    typeVReduction_Hprime_subgroupOf_derived_card_eq_prime hred
  rwa [hcardH]

public theorem typeVReduction_kernelQuotient_fixedPointSubgroup_zpowers_eq_bot_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (a : W1.subgroupOf M) (ha : a ≠ 1) :
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinv :
        IsInvariant (Subgroup.zpowers (a : M)) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (Subgroup.zpowers (a : M))
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := Subgroup.zpowers (a : M))
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinv
    fixedPointSubgroup (Subgroup.zpowers (a : M))
      (derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) = ⊥ := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  let A : Subgroup M := Subgroup.zpowers (a : M)
  have hNinv : IsInvariant A (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := A) (G := derivedSubgroup M) N
  let _ : IsInvariant A (derivedSubgroup M) N := hNinv
  have hNcard : Nat.card N = p := by
    dsimp [N]
    exact typeVReduction_Hprime_subgroupOf_derived_card_eq_prime hred
  have _ : Fact p.Prime := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    exact ⟨hpprime⟩
  have _ : IsCyclic N := isCyclic_of_prime_card hNcard
  let : CommGroup N := IsCyclic.commGroup
  have hcop : Nat.Coprime (Nat.card A) (Nat.card N) := by
    dsimp [A, N]
    exact typeVReduction_coprime_zpowers_W1_Hprime_subgroupOf_derived_supported
      hred h10 a
  let : MulDistribMulAction A (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := derivedSubgroup M) N hNinv
  have hfixQuot :
      fixedPointSubgroup A (derivedSubgroup M ⧸ N) =
        (fixedPointSubgroup A (derivedSubgroup M)).map
          (QuotientGroup.mk' N) := by
    simpa using
      (fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative
        (G := derivedSubgroup M) (A := A) (H := N) (hH := hNinv) hcop)
  have hNorm : A ≤ Subgroup.normalizer (derivedSubgroup M) := by
    dsimp [A]
    exact (Subgroup.zpowers_le).2
      (Subgroup.le_normalizer_of_normal (H := derivedSubgroup M)
        (show (a : M) ∈ ⊤ by simp))
  have hfixedK :
      fixedPointSubgroup A (derivedSubgroup M) = N := by
    dsimp [A, N]
    have hfix := fixedPointSubgroup_zpowers_conj_eq_elementCentralizerIn
      (K := derivedSubgroup M) (a := (a : M)) hNorm
    have hcent :
        elementCentralizerIn (derivedSubgroup M) (a : M) = W2.subgroupOf M := by
      simpa [elementCentralizerIn, Section2.centralizerIn, Section2.elementCentralizer] using
        centralizer_derivedSubgroup_eq_W2_of_hypothesis_10_1_supported_data h10 a ha
    rw [hcent, typeVReduction_W2_subgroupOf_eq_Hprime_subgroupOf hred] at hfix
    simpa [derivedSubgroup] using hfix
  rw [hfixQuot, hfixedK]
  ext q
  constructor
  · intro hq
    rcases Subgroup.mem_map.mp hq with ⟨x, hxN, rfl⟩
    exact (QuotientGroup.eq_one_iff (N := N) x).2 hxN
  · intro hq
    rw [Subgroup.mem_bot] at hq
    rw [hq]
    exact ⟨1, N.one_mem, rfl⟩

public theorem typeVReduction_kernelQuotient_fixed_eq_one_of_W1_ne_one_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (a : W1.subgroupOf M) (ha : a ≠ 1) :
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinvW1
    ∀ q : derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M),
      a • q = q → q = 1 := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x hfix
  let A : Subgroup M := Subgroup.zpowers (a : M)
  have hNinvA : IsInvariant A (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := A) (G := derivedSubgroup M) N
  let _ : IsInvariant A (derivedSubgroup M) N := hNinvA
  let : MulDistribMulAction A (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := A) (G := derivedSubgroup M) N hNinvA
  have hgenFix :
      (⟨(a : M), Subgroup.mem_zpowers (a : M)⟩ : A) •
        ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) =
      ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) := by
    change
      ((⟨(a : M) * (x : M) * (a : M)⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) =
        ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N)
    change
      ((⟨(a : M) * (x : M) * (a : M)⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) =
        ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) at hfix
    exact hfix
  have hqmem :
      ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) ∈
        fixedPointSubgroup A (derivedSubgroup M ⧸ N) := by
    rw [FixedPoints.mem_subgroup]
    intro b
    have hb_mem :
        b ∈ Subgroup.zpowers
          (⟨(a : M), Subgroup.mem_zpowers (a : M)⟩ : A) := by
      rcases Subgroup.mem_zpowers_iff.mp b.2 with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa using hn⟩
    exact smul_eq_self_of_mem_zpowers
      (y := (⟨(a : M), Subgroup.mem_zpowers (a : M)⟩ : A)) hb_mem hgenFix
  have hfixBot :=
    typeVReduction_kernelQuotient_fixedPointSubgroup_zpowers_eq_bot_supported
      hred h10 a ha
  rw [hfixBot] at hqmem
  exact Subgroup.mem_bot.mp hqmem

public theorem typeVReduction_nonprincipalLinearCharacterOrbitQuotient_card_eq_div_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinvW1
    letI : MulDistribMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    Nat.card (nonidentityOrbitQuotient (W1.subgroupOf M)
      ((derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ)) =
        (p ^ 2 - 1) / Nat.card W1 := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
      (derivedSubgroup M ⧸ N)
  have hcomm : IsMulCommutative (derivedSubgroup M ⧸ N) := by
    dsimp [N]
    exact typeVReduction_kernelQuotient_isMulCommutative hred
  have _ : IsMulCommutative (derivedSubgroup M ⧸ N) := hcomm
  have hfreeChar :
      ∀ a : W1.subgroupOf M, a ≠ 1 →
        ∀ χ : (derivedSubgroup M ⧸ N) →* ℂˣ,
          a • χ = χ → χ = 1 := by
    intro a ha χ hfix
    have hainv : a⁻¹ ≠ 1 := inv_ne_one.mpr ha
    have hfreeInv : ∀ q : derivedSubgroup M ⧸ N, a⁻¹ • q = q → q = 1 := by
      dsimp [N]
      exact typeVReduction_kernelQuotient_fixed_eq_one_of_W1_ne_one_supported
        hred h10 a⁻¹ hainv
    have hχfix : ∀ q : derivedSubgroup M ⧸ N, χ (a⁻¹ • q) = χ q := by
      intro q
      have h := congrFun (congrArg DFunLike.coe hfix) q
      simpa [characterGroupContragredient_smul_apply] using h
    exact linearCharacter_eq_one_of_fixed_by_fixedPointFree a⁻¹ hfreeInv χ hχfix
  have horbit := nonidentityOrbitQuotient_card_eq_div
    (A := W1.subgroupOf M)
    (G := (derivedSubgroup M ⧸ N) →* ℂˣ) hfreeChar
  have hlinCard : Nat.card ((derivedSubgroup M ⧸ N) →* ℂˣ) = p ^ 2 := by
    dsimp [N]
    exact typeVReduction_kernelQuotient_linearCharacter_card_eq_sq
      (M := M) (H' := H') (p := p)
      (typeVReduction_kernelQuotient_card_eq_sq hred)
  have hcardW1Sub : Nat.card (W1.subgroupOf M) = Nat.card W1 := by
    rcases h10 with
      ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
        _hNotation10, _h52⟩
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  rw [hlinCard, hcardW1Sub] at horbit
  exact horbit

public theorem typeVReduction_orbitRel_of_inducedCF_quotientCharacterInflation_eq_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
      typeVReduction_kernelQuotientSubgroup_normal hred
    let hNchar :
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic := by
      rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
      infer_instance
    let : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic :=
      hNchar
    let hNinvW1 :
        IsInvariant (W1.subgroupOf M) (derivedSubgroup M)
          ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      isInvariant_of_characteristic
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
      quotientMulDistribMulAction (A := W1.subgroupOf M)
        (G := derivedSubgroup M)
        ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)) hNinvW1
    letI : MulDistribMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ) :=
      characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
        (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M))
    letI : MulAction (W1.subgroupOf M)
        {ψ : (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ // ψ ≠ 1} :=
      nonidentitySubMulAction (W1.subgroupOf M)
        ((derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ)
    ∀ ψ η : {ψ : (derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ // ψ ≠ 1},
      Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) ψ.1) =
        Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) η.1) →
      MulAction.orbitRel (W1.subgroupOf M)
        {ψ : (derivedSubgroup M ⧸
          (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ // ψ ≠ 1}
        ψ η := by
  classical
  dsimp only
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
      (derivedSubgroup M ⧸ N)
  let : MulAction (W1.subgroupOf M)
      {ψ : (derivedSubgroup M ⧸ N) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ)
  intro ψ η hInd
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (H'.subgroupOf M) (derivedSubgroup M) ψ.1 with
    ⟨_nψ, ρψ, hρψirr, hρψchar⟩
  rcases Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (H'.subgroupOf M) (derivedSubgroup M) η.1 with
    ⟨_nη, ρη, hρηirr, hρηchar⟩
  have hIndRep : Section1.inducedCF (derivedSubgroup M) ρψ.character =
      Section1.inducedCF (derivedSubgroup M) ρη.character := by
    have h := hInd
    rw [hρψchar, hρηchar] at h
    exact h
  rcases Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
      (derivedSubgroup M) ρψ ρη hρψirr hρηirr hIndRep with ⟨i, hi⟩
  revert hi
  refine Quotient.inductionOn i ?_
  intro g hi
  have hconj :
      Section1.quotientCharacterInflation (H'.subgroupOf M)
          (derivedSubgroup M) ψ.1 =
        Section1.conjugateOnNormal (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) η.1) g := by
    rw [hρψchar, hρηchar]
    simpa [Section1.conjugateOrbitConj, Section1.conjugateOrbitFiber] using hi
  have hsemi :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup M)
        (derivedSubgroup M) (W1.subgroupOf M) := by
    rcases h10 with
      ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, h46base, _hNotation10,
        _h52⟩
    rcases h46base with ⟨_A, h46A⟩
    exact h46A.1.1
  rcases hsemi.mul_surjective g (by trivial) with ⟨k0, hk0, a0, ha0, hg⟩
  let k : derivedSubgroup M := ⟨k0, hk0⟩
  let a : W1.subgroupOf M := ⟨a0, ha0⟩
  have hgka : g = (k : M) * (a : M) := by simpa [k, a] using hg
  have hconj_a :
      Section1.conjugateOnNormal (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) η.1) g =
        Section1.conjugateOnNormal (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) η.1) (a : M) := by
    subst g
    ext x
    let y : derivedSubgroup M := ⟨(a : M) * (x : M) * (a : M)⁻¹,
      (inferInstance : (derivedSubgroup M).Normal).conj_mem
        (x : M) x.2 (a : M)⟩
    have htriv := congrFun
      (typeVReduction_quotientCharacterInflation_conjugate_derived_eq
        (M := M) (H' := H') (hred := hred) k η.1) y
    change Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) η.1
        ⟨((k : M) * (a : M)) * (x : M) * ((k : M) * (a : M))⁻¹,
          (inferInstance : (derivedSubgroup M).Normal).conj_mem
            (x : M) x.2 ((k : M) * (a : M))⟩ =
      Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) η.1 y
    simpa [Section1.conjugateOnNormal, y, mul_assoc] using htriv
  have hsmul := typeVReduction_quotientCharacterInflation_smul_eq_conjugateOnNormal
    (M := M) (H' := H') (W1 := W1) (hred := hred) a⁻¹ η.1
  have hψeq : ψ.1 = (a⁻¹ : W1.subgroupOf M) • η.1 := by
    apply Section6.quotientCharacterInflation_injective
      (H'.subgroupOf M) (derivedSubgroup M)
    change Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) ψ.1 =
      Section1.quotientCharacterInflation (H'.subgroupOf M)
        (derivedSubgroup M) ((a⁻¹ : W1.subgroupOf M) • η.1)
    rw [hconj, hconj_a]
    simpa [inv_inv] using hsmul.symm
  rw [MulAction.orbitRel_apply]
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨a⁻¹, ?_⟩
  apply Subtype.ext
  have hproj : ((a⁻¹ • η :
      {ψ : (derivedSubgroup M ⧸ N) →* ℂˣ // ψ ≠ 1}).1) =
      (a⁻¹ : W1.subgroupOf M) • η.1 :=
    nonidentitySubMulAction_val
      (A := W1.subgroupOf M) (G := (derivedSubgroup M ⧸ N) →* ℂˣ)
      (a⁻¹ : W1.subgroupOf M) η
  rw [hproj]
  exact hψeq.symm

public theorem typeVReduction_kernelSubfamily_card_eq_div_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    (Section6.inducedKernelFamilyOf
      (derivedSubgroup M) (H'.subgroupOf M) S).card =
        (p ^ 2 - 1) / Nat.card W1 := by
  classical
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ) :=
    characterGroupContragredientMulDistribMulAction (W1.subgroupOf M)
      (derivedSubgroup M ⧸ N)
  let : MulAction (W1.subgroupOf M)
      {ψ : (derivedSubgroup M ⧸ N) →* ℂˣ // ψ ≠ 1} :=
    nonidentitySubMulAction (W1.subgroupOf M)
      ((derivedSubgroup M ⧸ N) →* ℂˣ)
  let S₁ : Finset (Section1.ClassFunction M) :=
    Section6.inducedKernelFamilyOf (derivedSubgroup M) (H'.subgroupOf M) S
  let β : Type u := {χ : Section1.ClassFunction M // χ ∈ S₁}
  let f :
      nonidentityOrbitQuotient (W1.subgroupOf M)
        ((derivedSubgroup M ⧸ N) →* ℂˣ) → β :=
    Quotient.lift
      (fun ψ : {ψ : (derivedSubgroup M ⧸ N) →* ℂˣ // ψ ≠ 1} =>
        (⟨Section1.inducedCF (derivedSubgroup M)
            (Section1.quotientCharacterInflation (H'.subgroupOf M)
              (derivedSubgroup M) ψ.1), by
          dsimp [S₁]
          exact (typeVReduction_kernelSubfamily_mem_iff_exists_quotientCharacter_supported
            (M := M) (H' := H') (W1 := W1)
            (χ := Section1.inducedCF (derivedSubgroup M)
              (Section1.quotientCharacterInflation (H'.subgroupOf M)
                (derivedSubgroup M) ψ.1)) hred h10).mpr
              ⟨ψ.1, ψ.2, rfl⟩⟩ : β))
      (by
        intro ψ η hrel
        apply Subtype.ext
        dsimp
        exact typeVReduction_inducedCF_quotientCharacterInflation_eq_of_orbitRel
          (M := M) (H' := H') (W1 := W1) (hred := hred) ψ η hrel)
  have hf_inj : Function.Injective f := by
    intro q r hqr
    revert hqr
    refine Quotient.inductionOn₂ q r ?_
    intro ψ η hψη
    apply Quotient.sound
    apply typeVReduction_orbitRel_of_inducedCF_quotientCharacterInflation_eq_supported
      (M := M) (H' := H') (W1 := W1) (S := S) (τ := τ) hred h10
    change Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) ψ.1) =
        Section1.inducedCF (derivedSubgroup M)
          (Section1.quotientCharacterInflation (H'.subgroupOf M)
            (derivedSubgroup M) η.1)
    exact congrArg Subtype.val hψη
  have hf_surj : Function.Surjective f := by
    intro χ
    have hχmem : (χ : Section1.ClassFunction M) ∈
        Section6.inducedKernelFamilyOf (derivedSubgroup M) (H'.subgroupOf M) S := by
      change (χ : Section1.ClassFunction M) ∈ S₁
      exact χ.2
    rcases (typeVReduction_kernelSubfamily_mem_iff_exists_quotientCharacter_supported
        (M := M) (H' := H') (W1 := W1)
        (χ := (χ : Section1.ClassFunction M)) hred h10).mp hχmem with
      ⟨ψ, hψne, hχeq⟩
    refine ⟨Quotient.mk''
      (⟨ψ, hψne⟩ : {ψ : (derivedSubgroup M ⧸ N) →* ℂˣ // ψ ≠ 1}), ?_⟩
    apply Subtype.ext
    dsimp [f]
    exact hχeq.symm
  have hcardEquiv :
      Nat.card (nonidentityOrbitQuotient (W1.subgroupOf M)
        ((derivedSubgroup M ⧸ N) →* ℂˣ)) = Nat.card β :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  have hβcard : Nat.card β = S₁.card := by
    dsimp [β]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe S₁
  have horbit := typeVReduction_nonprincipalLinearCharacterOrbitQuotient_card_eq_div_supported
    (M := M) (H' := H') (W1 := W1) (S := S) (τ := τ) hred h10
  dsimp only at horbit
  change S₁.card = (p ^ 2 - 1) / Nat.card W1
  rw [← hβcard, ← hcardEquiv]
  simpa [N] using horbit

public theorem typeVReduction_inducedCF_quotientCharacterInflation_isIrreducible_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    [((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal]
    [IsMulCommutative (derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M))]
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (χ : (derivedSubgroup M ⧸
      (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) →* ℂˣ)
    (hχne : χ ≠ 1) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF (derivedSubgroup M)
        (Section1.quotientCharacterInflation (H'.subgroupOf M)
          (derivedSubgroup M) χ)) := by
  classical
  let N : Subgroup (derivedSubgroup M) :=
    (H'.subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    exact typeVReduction_kernelQuotientSubgroup_normal hred
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    change ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Characteristic
    rw [typeVReduction_Hprime_subgroupOf_derived_eq hred]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  have hcomm : IsMulCommutative (derivedSubgroup M ⧸ N) := by
    dsimp [N]
    exact typeVReduction_kernelQuotient_isMulCommutative hred
  have _ : IsMulCommutative (derivedSubgroup M ⧸ N) := hcomm
  have hθirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.quotientCharacterInflation (H'.subgroupOf M)
          (derivedSubgroup M) χ) := by
    exact Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      (H'.subgroupOf M) (derivedSubgroup M) χ
  have hsemi :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup M)
        (derivedSubgroup M) (W1.subgroupOf M) := by
    rcases h10 with
      ⟨_hM, _hType, _hS, _hW1, _hW2, _hW12, _hDade, h46base, _hNotation10,
        _h52⟩
    rcases h46base with ⟨_A, h46A⟩
    exact h46A.1.1
  refine inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed
    (derivedSubgroup M) (W1.subgroupOf M) hsemi hθirr ?_
  intro g hgW hg1 hfix
  apply hχne
  let a : W1.subgroupOf M := ⟨g, hgW⟩
  have ha : a ≠ 1 := by
    intro ha
    apply hg1
    simpa [a] using congrArg Subtype.val ha
  have hfreea : ∀ q : derivedSubgroup M ⧸ N, a • q = q → q = 1 := by
    dsimp [N]
    exact typeVReduction_kernelQuotient_fixed_eq_one_of_W1_ne_one_supported
      hred h10 a ha
  have hχfix : ∀ q : derivedSubgroup M ⧸ N, χ (a • q) = χ q := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    apply Units.ext
    have hxfix := congrFun hfix x
    change
      ((χ ((⟨g * (x : M) * g⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) : ℂ) =
        (χ ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) : ℂ))
    change
      ((χ ((⟨g * (x : M) * g⁻¹, _⟩ : derivedSubgroup M) :
          derivedSubgroup M ⧸ N) : ℂ) =
        (χ ((x : derivedSubgroup M) : derivedSubgroup M ⧸ N) : ℂ)) at hxfix
    exact hxfix
  exact linearCharacter_eq_one_of_fixed_by_fixedPointFree a hfreea χ hχfix

public theorem typeVReduction_complement_source_degree_ne_one_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    {χ : Section1.ClassFunction M}
    (hχS : χ ∈ S)
    (hχnot : χ ∉ Section6.inducedKernelFamilyOf
      (derivedSubgroup M) (H'.subgroupOf M) S) :
    ∃ θ : Section1.ClassFunction (derivedSubgroup M),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        θ ≠ Section1.principalCharacter (derivedSubgroup M) ∧
        χ = Section1.inducedCF (derivedSubgroup M) θ ∧
        Section1.degree θ ≠ 1 := by
  have hS₁ :
      Section6.inducedKernelFamily (derivedSubgroup M) (H'.subgroupOf M)
        (Section6.inducedKernelFamilyOf
          (derivedSubgroup M) (H'.subgroupOf M) S) :=
    Section6.inducedKernelFamilyOf_isFamily
      (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
      (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred)
  rcases h10 with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  rcases (hS χ).mp hχS with ⟨θ, hθirr, hθne, hχeq⟩
  refine ⟨θ, hθirr, hθne, hχeq, ?_⟩
  intro hθdeg
  apply hχnot
  exact (hS₁.2 χ).mpr
    ⟨θ, hθirr,
      typeVReduction_source_degree_one_subgroupInKernel_Hprime hred hθirr hθdeg,
      hθne, hχeq⟩

public theorem theorem_10_10_2_kernelSubfamily_complement_index_bridge_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    ∃ J : Type u, ∃ _instJ : Fintype J,
      ∃ j0 : J,
      ∃ μ : J → Section1.ClassFunction M,
        Nat.card J = p ∧
          (∀ χ : Section1.ClassFunction M,
            χ ∈ S ↔
              χ ∈ Section6.inducedKernelFamilyOf
                (derivedSubgroup M) (H'.subgroupOf M) S ∨
                ∃ j : J, j ≠ j0 ∧ χ = μ j) ∧
          (∀ j : J, j ≠ j0 →
            μ j ∈ S ∧
              Section1.degree (μ j) = (p * Nat.card W1 : ℂ)) := by
  classical
  rcases typeVReduction_exists_source_degree_prime_family_count hred with
    ⟨ι, hι, hιdec, θ, hθirr, hθcomplete, _hθinj, hθcount⟩
  let : Fintype ι := hι
  let : DecidableEq ι := hιdec
  let α0 : Type := {i : ι // Section1.degree (θ i) = (p : ℂ)}
  let α : Type u := ULift α0
  let S₁ : Finset (Section1.ClassFunction M) :=
    Section6.inducedKernelFamilyOf (derivedSubgroup M) (H'.subgroupOf M) S
  let J : Type u := Option α
  let instJ : Fintype J := inferInstance
  let j0 : J := none
  let μ : J → Section1.ClassFunction M := fun j =>
    match j with
    | none => 0
    | some i => Section1.inducedCF (derivedSubgroup M) (θ i.down.1)
  have hpprime : Nat.Prime p := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, hpprime, _hW2card, _hpOdd, _hW1Odd, _hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hbound⟩
    exact hpprime
  have hSderived : derivedInducedFamily M S := by
    rcases h10 with
      ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10,
        _h52⟩
    exact hS
  have hα0card : Nat.card α0 = p - 1 := by
    dsimp [α0]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hθcount
  have hαcard : Nat.card α = p - 1 := by
    dsimp [α]
    rw [Nat.card_congr (Equiv.ulift : ULift α0 ≃ α0), hα0card]
  have hsource_ne_principal :
      ∀ i : α, θ i.down.1 ≠ Section1.principalCharacter (derivedSubgroup M) := by
    intro i hprincipal
    have hdeg_one : Section1.degree (θ i.down.1) = 1 := by
      simp [hprincipal, Section1.degree, Section1.principalCharacter]
    have hpC : (p : ℂ) = 1 := i.down.2.symm.trans hdeg_one
    exact hpprime.ne_one (by exact_mod_cast hpC)
  have hμ_mem_degree :
      ∀ j : J, j ≠ j0 →
        μ j ∈ S ∧ Section1.degree (μ j) = (p * Nat.card W1 : ℂ) := by
    intro j hj
    cases j with
    | none => exact (hj rfl).elim
    | some i =>
        have hμS : μ (some i) ∈ S := by
          dsimp [μ]
          exact (hSderived
            (Section1.inducedCF (derivedSubgroup M) (θ i.down.1))).mpr
            ⟨θ i.down.1, hθirr i.down.1, hsource_ne_principal i, rfl⟩
        have hμdegree :
            Section1.degree (μ (some i)) = (p * Nat.card W1 : ℂ) := by
          rw [show μ (some i) =
            Section1.inducedCF (derivedSubgroup M) (θ i.down.1) by rfl]
          rw [Section1.degree_inducedClassFunction]
          rw [derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data
            h10, i.down.2]
          norm_num [Nat.cast_mul]
          ring
        exact ⟨hμS, hμdegree⟩
  refine ⟨J, instJ, j0, μ, ?_, ?_, hμ_mem_degree⟩
  ·
    have hαfintype : Fintype.card α = p - 1 :=
      (Nat.card_eq_fintype_card (α := α)).symm.trans hαcard
    change Nat.card (Option α) = p
    rw [Nat.card_eq_fintype_card, Fintype.card_option, hαfintype]
    exact Nat.sub_add_cancel hpprime.pos
  · intro χ
    constructor
    · intro hχS
      by_cases hχS₁ : χ ∈ S₁
      · exact Or.inl hχS₁
      · rcases typeVReduction_complement_source_degree_ne_one_supported
            hred h10 hχS (by simpa [S₁] using hχS₁) with
          ⟨θχ, hθχirr, _hθχne, hχeq, hθχdeg_ne⟩
        rcases hθcomplete θχ hθχirr with ⟨i, hi⟩
        have hideg : Section1.degree (θ i) = (p : ℂ) := by
          rw [hi]
          exact typeVReduction_source_degree_eq_prime_of_ne_one
            hred hθχirr hθχdeg_ne
        refine Or.inr ⟨some (ULift.up (⟨i, hideg⟩ : α0) : α), ?_, ?_⟩
        · simp [j0]
        · dsimp [μ]
          rw [hi]
          exact hχeq
    · intro hχ
      rcases hχ with hχS₁ | hχcomp
      · exact Section6.inducedKernelFamily_subset_base
          (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
          (Section6.inducedKernelFamilyOf_isFamily
            (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
            (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred)) hχS₁
      · rcases hχcomp with ⟨j, hj, hχeq⟩
        rw [hχeq]
        exact (hμ_mem_degree j hj).1

public theorem theorem_10_10_2_kernelSubfamily_card_complement_bridge_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    ∃ J : Type u, ∃ _instJ : Fintype J,
      ∃ j0 : J,
      ∃ μ : J → Section1.ClassFunction M,
        Nat.card J = p ∧
          (∀ χ : Section1.ClassFunction M,
            χ ∈ S ↔
              χ ∈ Section6.inducedKernelFamilyOf
                (derivedSubgroup M) (H'.subgroupOf M) S ∨
                ∃ j : J, j ≠ j0 ∧ χ = μ j) ∧
          (Section6.inducedKernelFamilyOf
            (derivedSubgroup M) (H'.subgroupOf M) S).card =
              (p ^ 2 - 1) / Nat.card W1 ∧
          (∀ j : J, j ≠ j0 →
            μ j ∈ S ∧
              Section1.degree (μ j) = (p * Nat.card W1 : ℂ)) := by
  have hS₁card :
      (Section6.inducedKernelFamilyOf
        (derivedSubgroup M) (H'.subgroupOf M) S).card =
          (p ^ 2 - 1) / Nat.card W1 :=
    typeVReduction_kernelSubfamily_card_eq_div_supported hred h10
  rcases theorem_10_10_2_kernelSubfamily_complement_index_bridge_supported
      hred h10 with
    ⟨J, instJ, j0, μ, hJcard, hdecomp, hμ⟩
  exact ⟨J, instJ, j0, μ, hJcard, hdecomp, hS₁card, hμ⟩

public theorem theorem_10_10_2_kernelSubfamily_decomposition_bridge_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    ∃ J : Type u, ∃ _instJ : Fintype J,
      ∃ j0 : J,
      ∃ μ : J → Section1.ClassFunction M,
        Nat.card J = p ∧
          (∀ χ : Section1.ClassFunction M,
            χ ∈ S ↔
              χ ∈ Section6.inducedKernelFamilyOf
                (derivedSubgroup M) (H'.subgroupOf M) S ∨
                ∃ j : J, j ≠ j0 ∧ χ = μ j) ∧
          (Section6.inducedKernelFamilyOf
            (derivedSubgroup M) (H'.subgroupOf M) S).card =
              (p ^ 2 - 1) / Nat.card W1 ∧
          (∀ χ : Section1.ClassFunction M,
            χ ∈ Section6.inducedKernelFamilyOf
              (derivedSubgroup M) (H'.subgroupOf M) S →
              Section1.IsIrreducibleCharacterOnGroup χ ∧
                Section1.degree χ = (Nat.card W1 : ℂ)) := by
  have _ : ((H'.subgroupOf M).subgroupOf (derivedSubgroup M)).Normal :=
    typeVReduction_kernelQuotientSubgroup_normal _hred
  have _ : IsMulCommutative
      (derivedSubgroup M ⧸
        (H'.subgroupOf M).subgroupOf (derivedSubgroup M)) :=
    typeVReduction_kernelQuotient_isMulCommutative _hred
  have hkernelSubfamilyIrreducibleDegree :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ Section6.inducedKernelFamilyOf
          (derivedSubgroup M) (H'.subgroupOf M) S →
        Section1.IsIrreducibleCharacterOnGroup χ ∧
          Section1.degree χ = (Nat.card W1 : ℂ) := by
    intro χ hχ
    have hχiff :=
      typeVReduction_kernelSubfamily_mem_iff_exists_quotientCharacter_supported
        _hred _h10 (χ := χ)
    rcases hχiff.mp hχ with ⟨ψ, hψne, hχeq⟩
    refine ⟨?_, typeVReduction_kernelSubfamily_degree_eq_card_W1_supported
      _hred _h10 hχ⟩
    rw [hχeq]
    exact typeVReduction_inducedCF_quotientCharacterInflation_isIrreducible_supported
      _hred _h10 ψ hψne
  rcases theorem_10_10_2_kernelSubfamily_card_complement_bridge_supported
      _hred _h10 with
    ⟨J, instJ, j0, μ, hJcard, hdecomp, hS₁card, _hμ⟩
  exact ⟨J, instJ, j0, μ, hJcard, hdecomp, hS₁card,
    hkernelSubfamilyIrreducibleDegree⟩

public theorem theorem_10_10_4_supported_notation_count_package_bridge
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
      ∃ S₁ : Finset (Section1.ClassFunction M),
      ∃ d n : ℕ, ∃ δ : ℤ,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ ∧
          @typeVCharacterCountData G _ _ J instJ M S S₁ W1 j0
            (fun j => @muColumn M _ I J instI μ j) p d n δ := by
  classical
  rcases exists_section10FourSixNotationSupportedData_of_hypothesis_10_1_supported_data
      h10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign, ω, σ,
      hnotation⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  let S₁ : Finset (Section1.ClassFunction M) :=
    Section6.inducedKernelFamilyOf (derivedSubgroup M) (H'.subgroupOf M) S
  rcases theorem_10_10_2_kernelSubfamily_decomposition_bridge_supported_source
      hred h10 with
    ⟨Jany, instJany, j0any, μany, hJany, hdecompAny, hS₁card,
      hS₁char⟩
  let : Fintype Jany := instJany
  have hJcard : Nat.card J = p := by
    have hJW2 : Nat.card J = Nat.card W2 :=
      uniformMu_card_J_eq_card_W2_of_hypothesis_10_1_supported_data
        h10 hnotation
    have hW2p : Nat.card W2 = p := by
      rcases hred with
        ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
          _hW2, _hFrob, _hpprime, hW2card, _hpOdd, _hW1Odd, _hW1gt,
          _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
      exact hW2card
    exact hJW2.trans hW2p
  have hμ :
      ∀ j : J, j ≠ j0 →
        muColumn μ j ∈ S ∧
          Section1.degree (muColumn μ j) = (p * Nat.card W1 : ℂ) := by
    intro j hj
    exact ⟨
      muColumn_mem_of_hypothesis_10_1_supported_and_section10FourSixNotationSupportedData
        h10 hnotation hj,
      degree_muColumn_eq_prime_mul_card_W1_of_typeV_supported
        hred h10 hnotation hj⟩
  let C : Finset (Section1.ClassFunction M) := S \ S₁
  let T : Finset (Section1.ClassFunction M) :=
    (Finset.univ.erase j0).image (fun j : J => muColumn μ j)
  have hTsubC : T ⊆ C := by
    intro χ hχ
    rcases Finset.mem_image.mp hχ with ⟨j, hjmem, hχeq⟩
    have hj : j ≠ j0 := (Finset.mem_erase.mp hjmem).1
    rw [← hχeq]
    exact Finset.mem_sdiff.mpr
      ⟨(hμ j hj).1,
        muColumn_not_mem_typeV_kernelSubfamily_supported hred h10 hnotation hj⟩
  have hInj :
      Set.InjOn (fun j : J => muColumn μ j)
        ((Finset.univ.erase j0 : Finset J) : Set J) := by
    intro j _hj k _hk hEq
    by_contra hjk
    have hinnerEq :
        Section1.scalarProduct M (muColumn μ j) (muColumn μ j) =
          Section1.scalarProduct M (muColumn μ j) (muColumn μ k) :=
      congrArg (fun χ => Section1.scalarProduct M (muColumn μ j) χ) hEq
    have hself := theorem_10_10_4_muColumn_gram_supported hnotation j j
    have hcross := theorem_10_10_4_muColumn_gram_supported hnotation j k
    have hcardZero : (Fintype.card I : ℂ) = 0 := by
      calc
        (Fintype.card I : ℂ) =
            Section1.scalarProduct M (muColumn μ j) (muColumn μ j) := by
              simpa using hself.symm
        _ = Section1.scalarProduct M (muColumn μ j) (muColumn μ k) := hinnerEq
        _ = 0 := by simpa [hjk] using hcross
    have hIpos : 0 < Fintype.card I := by
      have hIcardNat : Nat.card I = Nat.card W1 :=
        uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
          h10 hnotation
      have hIcard : Fintype.card I = Nat.card W1 := by
        simpa [Nat.card_eq_fintype_card] using hIcardNat
      have hW1gt : 1 < Nat.card W1 := by
        rcases hred with
          ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
            _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
            _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
        exact hW1gt
      omega
    have hIne : (Fintype.card I : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hIpos)
    exact hIne hcardZero
  have hTcard : T.card = p - 1 := by
    calc
      T.card = (Finset.univ.erase j0 : Finset J).card := by
        dsimp [T]
        exact Finset.card_image_of_injOn hInj
      _ = Fintype.card J - 1 := by
        simp
      _ = Nat.card J - 1 := by
        rw [Nat.card_eq_fintype_card]
      _ = p - 1 := by rw [hJcard]
  let U : Finset (Section1.ClassFunction M) :=
    (Finset.univ.erase j0any).image μany
  have hCsubU : C ⊆ U := by
    intro χ hχC
    have hχS : χ ∈ S := (Finset.mem_sdiff.mp hχC).1
    have hχnotS₁ : χ ∉ S₁ := (Finset.mem_sdiff.mp hχC).2
    rcases (hdecompAny χ).mp hχS with hχS₁ | hχnonbase
    · exact False.elim (hχnotS₁ (by simpa [S₁] using hχS₁))
    · rcases hχnonbase with ⟨j, hj, hχeq⟩
      exact Finset.mem_image.mpr
        ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, by simp [hχeq]⟩
  have hUcardLe : U.card ≤ (Finset.univ.erase j0any : Finset Jany).card := by
    dsimp [U]
    exact Finset.card_image_le
  have hUeraseCard : (Finset.univ.erase j0any : Finset Jany).card = p - 1 := by
    have hJanyCard : Fintype.card Jany = p := by
      simpa [Nat.card_eq_fintype_card] using hJany
    simp [hJanyCard]
  have hCcardLe : C.card ≤ p - 1 := by
    exact (Finset.card_le_card hCsubU).trans (hUcardLe.trans (le_of_eq hUeraseCard))
  have hCcardLeT : C.card ≤ T.card := by
    simpa [hTcard] using hCcardLe
  have hTeqC : T = C :=
    Finset.eq_of_subset_of_card_le hTsubC hCcardLeT
  have hCsubT : C ⊆ T := by
    intro χ hχ
    rw [hTeqC]
    exact hχ
  have hdecomp :
      ∀ χ : Section1.ClassFunction M,
        χ ∈ S ↔ χ ∈ S₁ ∨ ∃ j : J, j ≠ j0 ∧ χ = muColumn μ j := by
    intro χ
    constructor
    · intro hχS
      by_cases hχS₁ : χ ∈ S₁
      · exact Or.inl hχS₁
      · have hχC : χ ∈ C := Finset.mem_sdiff.mpr ⟨hχS, hχS₁⟩
        have hχT : χ ∈ T := hCsubT hχC
        rcases Finset.mem_image.mp hχT with ⟨j, hjmem, hχeq⟩
        exact Or.inr ⟨j, (Finset.mem_erase.mp hjmem).1, hχeq.symm⟩
    · intro hχ
      rcases hχ with hχS₁ | hχnonbase
      · exact Section6.inducedKernelFamily_subset_base
          (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
          (Section6.inducedKernelFamilyOf_isFamily
            (inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10)
            (typeVReduction_Hprime_subgroupOf_le_derivedSubgroup hred))
          (by simpa [S₁] using hχS₁)
      · rcases hχnonbase with ⟨j, hj, rfl⟩
        exact (hμ j hj).1
  refine ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign, ω, σ,
    S₁, p, 2, -1, hnotation, ?_⟩
  refine ⟨hJcard, hdecomp, ?_, ?_, hμ, rfl, rfl, rfl⟩
  · simpa [S₁] using hS₁card
  · intro χ hχ
    exact hS₁char χ (by simpa [S₁] using hχ)


public theorem theorem_10_10_3_supported_alpha_scalarProduct_sOne_sub
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ η : Section1.ClassFunction M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hη : η ∈ S₁)
    (hηζ : η ≠ ζ)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) (ζ - η) =
      -(n : ℂ) := by
  have hμdeg :
      Section1.degree (μ i0 j) = (p : ℂ) :=
    degree_mu_of_typeV_supported hred h10 hnotation hj
  have hbaseDeg :
      Section1.degree (μ i0 j0) = 1 :=
    baseColumn_degree_one_of_section10FourSixNotationSupportedData hnotation i0
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  have hW1gt : 1 < Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    exact hW1gt
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
    exact h43b.2.2.1
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
  have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := (hS1irr ζ hζ).1
  have hηirr : Section1.IsIrreducibleCharacterOnGroup η := (hS1irr η hη).1
  have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) := (hS1irr ζ hζ).2
  have hηdeg : Section1.degree η = (Nat.card W1 : ℂ) := (hS1irr η hη).2
  have hpneW1 : (p : ℂ) ≠ (Nat.card W1 : ℂ) := by
    have hpneNat : p ≠ Nat.card W1 := by
      rw [hpEq]
      omega
    exact_mod_cast hpneNat
  have hOneNeW1 : (1 : ℂ) ≠ (Nat.card W1 : ℂ) := by
    have hOneNeNat : (1 : ℕ) ≠ Nat.card W1 := by omega
    exact_mod_cast hOneNeNat
  have hμζ_ne : μ i0 j ≠ ζ := by
    intro hEq
    have hdegEq := congrArg Section1.degree hEq
    rw [hμdeg, hζdeg] at hdegEq
    exact hpneW1 hdegEq
  have hμη_ne : μ i0 j ≠ η := by
    intro hEq
    have hdegEq := congrArg Section1.degree hEq
    rw [hμdeg, hηdeg] at hdegEq
    exact hpneW1 hdegEq
  have hbaseζ_ne : μ i0 j0 ≠ ζ := by
    intro hEq
    have hdegEq := congrArg Section1.degree hEq
    rw [hbaseDeg, hζdeg] at hdegEq
    exact hOneNeW1 hdegEq
  have hbaseη_ne : μ i0 j0 ≠ η := by
    intro hEq
    have hdegEq := congrArg Section1.degree hEq
    rw [hbaseDeg, hηdeg] at hdegEq
    exact hOneNeW1 hdegEq
  have hζη_ne : ζ ≠ η := by
    intro hEq
    exact hηζ hEq.symm
  have hα :
      alphaChar μ ζ n δ j0 i0 j =
        μ i0 j + (-(δ : ℂ)) • μ i0 j0 + (-(n : ℂ)) • ζ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hαζ :
      Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) ζ = -(n : ℂ) := by
    have hμζ :
        Section1.scalarProduct M (μ i0 j) ζ = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j) hζirr hμζ_ne
    have hbaseζ :
        Section1.scalarProduct M (μ i0 j0) ζ = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j0) hζirr hbaseζ_ne
    have hζself :
        Section1.scalarProduct M ζ ζ = 1 :=
      scalarProduct_irreducible_self hζirr
    rw [hα]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [hμζ, hbaseζ, hζself]
    ring
  have hαη :
      Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) η = 0 := by
    have hμη :
        Section1.scalarProduct M (μ i0 j) η = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j) hηirr hμη_ne
    have hbaseη :
        Section1.scalarProduct M (μ i0 j0) η = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j0) hηirr hbaseη_ne
    have hζη :
        Section1.scalarProduct M ζ η = 0 :=
      scalarProduct_irreducible_ne hζirr hηirr hζη_ne
    rw [hα]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [hμη, hbaseη, hζη]
    ring
  have hsub :
      Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) (ζ - η) =
        Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) ζ -
          Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) η := by
    unfold Section1.scalarProduct
    simp [Pi.sub_apply, sub_eq_add_neg, Finset.sum_add_distrib, mul_add]
  rw [hsub, hαζ, hαη]
  ring

public theorem theorem_10_10_3_supported_alpha_tau_scalarProduct_sOne_sub
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ η : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hη : η ∈ S₁)
    (hηζ : η ≠ ζ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j))
        (τ₁ (ζ - η)) =
      -(n : ℂ) := by
  have hτagree :
      τ₁ (ζ - η) = τ (ζ - η) :=
    typeVCoherentSubfamilyData_agreesOn_sub hcount hτ₁ hζ hη
  have hαA0 :
      Section1.supportedOn (alphaChar μ ζ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    typeVAlpha_supportedOn_primeDadeA0_of_typeVCharacterCountData_supported
      hred h10 hcount hnotation hζ hj
  have hηdiffA0 :
      Section1.supportedOn (ζ - η)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    have hζS : ζ ∈ S := typeVCharacterCount_sOne_subset hcount hζ
    have hηS : η ∈ S := typeVCharacterCount_sOne_subset hcount hη
    have hζDerived :=
      supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
        h10 hζS
    have hηDerived :=
      supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
        h10 hηS
    have hdiffDerived := supportedOn_sub_local hζDerived hηDerived
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    have hζClass : Section1.IsClassFunction ζ :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (hS1irr ζ hζ).1)
    have hηClass : Section1.IsClassFunction η :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (hS1irr η hη).1)
    have hdiffClass : Section1.IsClassFunction (ζ - η) := by
      intro x g
      simp [hζClass x g, hηClass x g]
    have hdeg : Section1.degree (ζ - η) = 0 := by
      have hζdeg : ζ 1 = (Nat.card W1 : ℂ) := by
        simpa [Section1.degree] using (hS1irr ζ hζ).2
      have hηdeg : η 1 = (Nat.card W1 : ℂ) := by
        simpa [Section1.degree] using (hS1irr η hη).2
      unfold Section1.degree
      simp [hζdeg, hηdeg]
    exact supportedOn_primeDadeA0_of_supportedOn_derivedSubgroup_degree_zero
      hnotation
        (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hnotation)
        hdiffClass hdiffDerived hdeg
  have hSupportedData :=
    supportedFourSixData_of_section10FourSixNotationSupportedData hnotation
  rcases hSupportedData with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) :=
    h43b.2.2.1
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hμirr i j))
  have hζClass : Section1.IsClassFunction ζ := by
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hS1irr ζ hζ).1)
  have hηClass : Section1.IsClassFunction η := by
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hS1irr η hη).1)
  have hαClass :
      Section1.IsClassFunction (alphaChar μ ζ n δ j0 i0 j) := by
    intro x g
    simp [alphaChar, hμClass i0 j x g, hμClass i0 j0 x g, hζClass x g]
  have hηdiffClass : Section1.IsClassFunction (ζ - η) := by
    intro x g
    simp [hζClass x g, hηClass x g]
  have hpair :
      Section1.scalarProduct G
          (τ (alphaChar μ ζ n δ j0 i0 j))
          (τ (ζ - η)) =
        Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) (ζ - η) :=
      hτiso (alphaChar μ ζ n δ j0 i0 j) (ζ - η) hαClass hηdiffClass hαA0
        hηdiffA0
  rw [hτagree, hpair]
  exact theorem_10_10_3_supported_alpha_scalarProduct_sOne_sub
    hred h10 hcount hnotation hζ hη hηζ hj

public theorem theorem_10_10_3_supported_corrected_alpha_orthogonal_sOne_sub
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ η : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hη : η ∈ S₁)
    (hηζ : η ≠ ζ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
        (τ₁ (ζ - η)) = 0 := by
  have htransfer :
      Section1.scalarProduct G
          (τ (alphaChar μ ζ n δ j0 i0 j))
          (τ₁ (ζ - η)) =
        -(n : ℂ) :=
    theorem_10_10_3_supported_alpha_tau_scalarProduct_sOne_sub
      hred h10 hcount hnotation hζ hη hηζ hτ₁ hj
  rcases hτ₁ with ⟨_hcoh, hIso, _hVirt, _hAgree⟩
  have hζspan : Section5.integerSpan S₁ ζ :=
    Section5.integerSpan_of_mem S₁ hζ
  have hηspan : Section5.integerSpan S₁ η :=
    Section5.integerSpan_of_mem S₁ hη
  have hdiffspan : Section5.integerSpan S₁ (ζ - η) :=
    Section5.integerSpan_sub hζspan hηspan
  have hτζdiff :
      Section1.scalarProduct G (τ₁ ζ) (τ₁ (ζ - η)) =
        Section1.scalarProduct M ζ (ζ - η) :=
    hIso ζ (ζ - η) hζspan hdiffspan
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
  have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := (hS1irr ζ hζ).1
  have hηirr : Section1.IsIrreducibleCharacterOnGroup η := (hS1irr η hη).1
  have hζη_ne : ζ ≠ η := by
    intro hEq
    exact hηζ hEq.symm
  have hζη :
      Section1.scalarProduct M ζ η = 0 :=
    scalarProduct_irreducible_ne hζirr hηirr hζη_ne
  have hζself : Section1.scalarProduct M ζ ζ = 1 :=
    scalarProduct_irreducible_self hζirr
  have hζdiff : Section1.scalarProduct M ζ (ζ - η) = 1 := by
    have hsub :
        Section1.scalarProduct M ζ (ζ - η) =
          Section1.scalarProduct M ζ ζ - Section1.scalarProduct M ζ η := by
      unfold Section1.scalarProduct
      simp [Pi.sub_apply, sub_eq_add_neg, Finset.sum_add_distrib, mul_add]
    rw [hsub, hζself, hζη]
    ring
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]
  rw [htransfer, hτζdiff, hζdiff]
  ring

public theorem theorem_10_10_3_supported_corrected_alpha_constant_pairing
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ η : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hη : η ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
        (τ₁ η) =
      Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
        (τ₁ ζ) := by
  classical
  by_cases hηζEq : η = ζ
  · subst η
    rfl
  · have horth :
        Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (τ₁ (ζ - η)) = 0 :=
      theorem_10_10_3_supported_corrected_alpha_orthogonal_sOne_sub
        hred h10 hcount hnotation hζ hη hηζEq hτ₁ hj
    have hsub :
        Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (τ₁ ζ - τ₁ η) =
          Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (τ₁ ζ) -
          Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (τ₁ η) := by
      unfold Section1.scalarProduct
      simp [Pi.sub_apply, sub_eq_add_neg, Finset.sum_add_distrib, mul_add]
    have horth' :
        Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (τ₁ ζ) -
          Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (τ₁ η) = 0 := by
      rw [← hsub]
      simpa [map_sub] using horth
    exact (sub_eq_zero.mp horth').symm

public theorem theorem_10_10_3_supported_corrected_alpha_projection_orthogonal_sOne
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ η : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hη : η ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G
        ((τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) -
          (Section1.scalarProduct G
              (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
              (τ₁ ζ)) • (Finset.sum S₁ fun χ => τ₁ χ))
        (τ₁ η) = 0 := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
  let c : ℂ := Section1.scalarProduct G Y (τ₁ ζ)
  change
    Section1.scalarProduct G
        (Y - c • (Finset.sum S₁ fun χ => τ₁ χ))
        (τ₁ η) = 0
  have hconst :
      Section1.scalarProduct G Y (τ₁ η) = c := by
    dsimp [Y, c]
    exact theorem_10_10_3_supported_corrected_alpha_constant_pairing
      hred h10 hcount hnotation hζ hη hτ₁ hj
  have hsum :
      Section1.scalarProduct G (Finset.sum S₁ fun χ => τ₁ χ) (τ₁ η) = 1 :=
    theorem_10_10_3_tauOne_sOne_sum_scalarProduct hcount hτ₁ hη
  have hsub :
      Section1.scalarProduct G
          (Y - c • (Finset.sum S₁ fun χ => τ₁ χ))
          (τ₁ η) =
        Section1.scalarProduct G Y (τ₁ η) -
          c * Section1.scalarProduct G (Finset.sum S₁ fun χ => τ₁ χ) (τ₁ η) := by
    have hrewrite :
        Y - c • (Finset.sum S₁ fun χ => τ₁ χ) =
          Y + (-c) • (Finset.sum S₁ fun χ => τ₁ χ) := by
      ext x
      simp [sub_eq_add_neg]
    rw [hrewrite, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]
    ring
  rw [hsub, hconst, hsum]
  ring

public theorem theorem_10_10_3_supported_corrected_alpha_projection_orthogonal_sOne_sum
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G
        ((τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) -
          (Section1.scalarProduct G
              (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
              (τ₁ ζ)) • (Finset.sum S₁ fun χ => τ₁ χ))
        (Finset.sum S₁ fun χ => τ₁ χ) = 0 := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
  let c : ℂ := Section1.scalarProduct G Y (τ₁ ζ)
  let X : Section1.ClassFunction G :=
    Y - c • (Finset.sum S₁ fun χ => τ₁ χ)
  change
    Section1.scalarProduct G X (Finset.sum S₁ fun χ => τ₁ χ) = 0
  have hsum_repr :
      (Finset.sum S₁ fun χ => τ₁ χ) =
        (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) := by
    rw [← Finset.sum_attach]
    apply Finset.sum_congr
    · ext χ
      simp
    · intro χ _hχ
      rfl
  have hsum_fun :
      (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) =
        (fun g => ∑ χ : {χ // χ ∈ S₁}, (τ₁ χ.1) g) := by
    ext g
    simp
  calc
    Section1.scalarProduct G X (Finset.sum S₁ fun χ => τ₁ χ)
        = Section1.scalarProduct G X
            (∑ χ : {χ // χ ∈ S₁}, τ₁ χ.1) := by
          rw [hsum_repr]
    _ = Section1.scalarProduct G X
          (fun g => ∑ χ : {χ // χ ∈ S₁}, (τ₁ χ.1) g) := by
          rw [← hsum_fun]
    _ = ∑ χ : {χ // χ ∈ S₁}, Section1.scalarProduct G X (τ₁ χ.1) := by
          rw [Section1.scalarProduct_fintype_sum_right]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro χ _hχ
          dsimp [X, Y, c]
          exact theorem_10_10_3_supported_corrected_alpha_projection_orthogonal_sOne
            hred h10 hcount hnotation hζ χ.2 hτ₁ hj

public theorem theorem_10_10_3_supported_alpha_tau_cfNormSq_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    Section5.cfNormSq (τ (alphaChar μ ζ n δ j0 i0 j)) =
      (2 : ℝ) + (n : ℝ) ^ 2 := by
  classical
  have hαA0 :
      Section1.supportedOn (alphaChar μ ζ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    typeVAlpha_supportedOn_primeDadeA0_of_typeVCharacterCountData_supported
      _hred _h10 _hcount _hnotation _hζ _hj
  have hSupportedData :=
    supportedFourSixData_of_section10FourSixNotationSupportedData _hnotation
  rcases hSupportedData with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) :=
    h43b.2.2.1
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hμirr i j))
  have hζClass : Section1.IsClassFunction ζ := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hS1irr ζ _hζ).1)
  have hαClass :
      Section1.IsClassFunction (alphaChar μ ζ n δ j0 i0 j) := by
    intro x g
    simp [alphaChar, hμClass i0 j x g, hμClass i0 j0 x g, hζClass x g]
  have hselfM :
      Section1.scalarProduct M
          (alphaChar μ ζ n δ j0 i0 j)
          (alphaChar μ ζ n δ j0 i0 j) =
        (2 : ℂ) + (n : ℂ) ^ 2 := by
    have hμdeg : Section1.degree (μ i0 j) = (p : ℂ) :=
      degree_mu_of_typeV_supported _hred _h10 _hnotation _hj
    have hbaseDeg : Section1.degree (μ i0 j0) = 1 :=
      baseColumn_degree_one_of_section10FourSixNotationSupportedData
        _hnotation i0
    have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one _hred).1
    have hW1gt : 1 < Nat.card W1 := by
      rcases _hred with
        ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
          _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
          _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
      exact hW1gt
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, hδ, _hn⟩
    have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := (hS1irr ζ _hζ).1
    have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) :=
      (hS1irr ζ _hζ).2
    have hpneW1 : (p : ℂ) ≠ (Nat.card W1 : ℂ) := by
      have hpneNat : p ≠ Nat.card W1 := by
        rw [hpEq]
        omega
      exact_mod_cast hpneNat
    have hOneNeW1 : (1 : ℂ) ≠ (Nat.card W1 : ℂ) := by
      have hOneNeNat : (1 : ℕ) ≠ Nat.card W1 := by omega
      exact_mod_cast hOneNeNat
    have hμζ_ne : μ i0 j ≠ ζ := by
      intro hEq
      have hdegEq := congrArg Section1.degree hEq
      rw [hμdeg, hζdeg] at hdegEq
      exact hpneW1 hdegEq
    have hbaseζ_ne : μ i0 j0 ≠ ζ := by
      intro hEq
      have hdegEq := congrArg Section1.degree hEq
      rw [hbaseDeg, hζdeg] at hdegEq
      exact hOneNeW1 hdegEq
    have hμbase_ne : μ i0 j ≠ μ i0 j0 := by
      intro hEq
      have hdegEq := congrArg Section1.degree hEq
      rw [hμdeg, hbaseDeg] at hdegEq
      have hpneOne : (p : ℂ) ≠ 1 := by
        have hpneOneNat : p ≠ 1 := by
          rw [hpEq]
          omega
        exact_mod_cast hpneOneNat
      exact hpneOne hdegEq
    have hα :
        alphaChar μ ζ n δ j0 i0 j =
          μ i0 j + (-(δ : ℂ)) • μ i0 j0 + (-(n : ℂ)) • ζ := by
      ext x
      simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      ring
    have hμself : Section1.scalarProduct M (μ i0 j) (μ i0 j) = 1 :=
      scalarProduct_irreducible_self (hμirr i0 j)
    have hbaseself : Section1.scalarProduct M (μ i0 j0) (μ i0 j0) = 1 :=
      scalarProduct_irreducible_self (hμirr i0 j0)
    have hζself : Section1.scalarProduct M ζ ζ = 1 :=
      scalarProduct_irreducible_self hζirr
    have hμbase : Section1.scalarProduct M (μ i0 j) (μ i0 j0) = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j) (hμirr i0 j0) hμbase_ne
    have hbaseμ : Section1.scalarProduct M (μ i0 j0) (μ i0 j) = 0 := by
      simpa [Section1.scalarProduct_star_swap] using congrArg star hμbase
    have hμζ : Section1.scalarProduct M (μ i0 j) ζ = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j) hζirr hμζ_ne
    have hζμ : Section1.scalarProduct M ζ (μ i0 j) = 0 := by
      simpa [Section1.scalarProduct_star_swap] using congrArg star hμζ
    have hbaseζ : Section1.scalarProduct M (μ i0 j0) ζ = 0 :=
      scalarProduct_irreducible_ne (hμirr i0 j0) hζirr hbaseζ_ne
    have hζbase : Section1.scalarProduct M ζ (μ i0 j0) = 0 := by
      simpa [Section1.scalarProduct_star_swap] using congrArg star hbaseζ
    rw [hα]
    simp only [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
      Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      hμself, hbaseself, hζself, hμbase, hbaseμ, hμζ, hζμ, hbaseζ, hζbase]
    rw [hδ]
    norm_num [pow_two]
  have hself :
      Section1.scalarProduct G
          (τ (alphaChar μ ζ n δ j0 i0 j))
          (τ (alphaChar μ ζ n δ j0 i0 j)) =
        (2 : ℂ) + (n : ℂ) ^ 2 := by
    rw [hτiso (alphaChar μ ζ n δ j0 i0 j)
      (alphaChar μ ζ n δ j0 i0 j) hαClass hαClass hαA0 hαA0]
    exact hselfM
  unfold Section5.cfNormSq
  rw [hself]
  simp [pow_two]

public theorem theorem_10_10_3_supported_alpha_tau_isVirtualCharacter
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    {j : J} (hj : j ≠ j0) :
    IsVirtualCharacter (τ (alphaChar μ ζ n δ j0 i0 j)) := by
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
    exact h43b.2.2.1
  have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := by
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact (hS1irr ζ hζ).1
  have hαvirt :
      IsVirtualCharacter (alphaChar μ ζ n δ j0 i0 j) := by
    have hμvirt :
        IsVirtualCharacter (μ i0 j) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμirr i0 j)
    have hbasevirt :
        IsVirtualCharacter (μ i0 j0) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμirr i0 j0)
    have hζvirt :
        IsVirtualCharacter ζ :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζirr
    have hδbase :
        IsVirtualCharacter ((δ : ℂ) • μ i0 j0) :=
      isVirtualCharacter_intCast_smul_sec10 δ hbasevirt
    have hnζ :
        IsVirtualCharacter ((n : ℂ) • ζ) :=
      isVirtualCharacter_natCast_smul_sec10 n hζvirt
    simpa [alphaChar] using
      Section3.isVirtualCharacter_sub
        (Section3.isVirtualCharacter_sub hμvirt hδbase) hnζ
  have hαA0 :
      Section1.supportedOn (alphaChar μ ζ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    typeVAlpha_supportedOn_primeDadeA0_of_typeVCharacterCountData_supported
      hred h10 hcount hnotation hζ hj
  have hTauVirt :
      Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hTauIso, _hTauPunct, hTauVirt, _hPF39⟩
    exact hTauVirt
  exact hTauVirt (alphaChar μ ζ n δ j0 i0 j) hαvirt hαA0

public theorem theorem_10_10_3_supported_corrected_alpha_pairing_integral
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁)
    {j : J} (hj : j ≠ j0) :
    ∃ a : ℤ,
      Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
        (τ₁ ζ) = (a : ℂ) := by
  have hατvirt :
      IsVirtualCharacter (τ (alphaChar μ ζ n δ j0 i0 j)) :=
    theorem_10_10_3_supported_alpha_tau_isVirtualCharacter
      hred h10 hcount hnotation hζ hj
  have hζτvirt :
      IsVirtualCharacter (τ₁ ζ) :=
    theorem_10_10_3_tauOne_sOne_isVirtualCharacter hτ₁ hζ
  have hYvirt :
      IsVirtualCharacter
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) :=
    Section3.isVirtualCharacter_add hατvirt
      (isVirtualCharacter_natCast_smul_sec10 n hζτvirt)
  exact Section3.scalarProduct_isVirtualCharacter_eq_int hYvirt hζτvirt

public theorem theorem_10_10_3_supported_tauOne_projection_cfNormSq_le_alpha_tau
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ a : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁)
    {j : J} (hj : j ≠ j0)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
        (τ₁ ζ) = (a : ℂ)) :
    Section5.cfNormSq
        ((a : ℂ) • (Finset.sum S₁ fun χ => τ₁ χ) - (n : ℂ) • τ₁ ζ) ≤
      Section5.cfNormSq (τ (alphaChar μ ζ n δ j0 i0 j)) := by
  let T : Section1.ClassFunction G := Finset.sum S₁ fun χ => τ₁ χ
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
  let X : Section1.ClassFunction G := Y - (a : ℂ) • T
  let P : Section1.ClassFunction G := (a : ℂ) • T - (n : ℂ) • τ₁ ζ
  have hXT : Section1.scalarProduct G X T = 0 := by
    dsimp [X, Y, T]
    simpa [ha] using
      theorem_10_10_3_supported_corrected_alpha_projection_orthogonal_sOne_sum
        hred h10 hcount hnotation hζ hτ₁ hj
  have hXζ : Section1.scalarProduct G X (τ₁ ζ) = 0 := by
    dsimp [X, Y, T]
    simpa [ha] using
      theorem_10_10_3_supported_corrected_alpha_projection_orthogonal_sOne
        hred h10 hcount hnotation hζ hζ hτ₁ hj
  have hXP : Section1.scalarProduct G X P = 0 := by
    dsimp [P]
    rw [Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_right]
    rw [hXT, hXζ]
    simp
  have hPX : Section1.scalarProduct G P X = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hXP
  have hdecomp : τ (alphaChar μ ζ n δ j0 i0 j) = X + P := by
    dsimp [X, P, Y, T]
    ext g
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have hnorm :
      Section5.cfNormSq (τ (alphaChar μ ζ n δ j0 i0 j)) =
        Section5.cfNormSq X + Section5.cfNormSq P := by
    rw [hdecomp]
    exact Section5.cfNormSq_add_eq_add_of_orthogonal hXP hPX
  have hXnonneg : 0 ≤ Section5.cfNormSq X := Section5.cfNormSq_nonneg X
  calc
    Section5.cfNormSq
        ((a : ℂ) • (Finset.sum S₁ fun χ => τ₁ χ) - (n : ℂ) • τ₁ ζ)
        = Section5.cfNormSq P := by rfl
    _ ≤ Section5.cfNormSq (τ (alphaChar μ ζ n δ j0 i0 j)) := by
        linarith

public theorem theorem_10_10_3_supported_corrected_alpha_pairing_eq_zero_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
        (τ₁ ζ) = 0 := by
  rcases theorem_10_10_3_supported_corrected_alpha_pairing_integral
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj with
    ⟨a, ha⟩
  have hle :=
    theorem_10_10_3_supported_tauOne_projection_cfNormSq_le_alpha_tau
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj ha
  have hproj :
      Section5.cfNormSq
          ((a : ℂ) • (Finset.sum S₁ fun χ => τ₁ χ) - (n : ℂ) • τ₁ ζ) =
        (S₁.card : ℝ) * (a : ℝ) ^ 2 -
          2 * (a : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 :=
    theorem_10_10_3_tauOne_projection_cfNormSq _hcount _hτ₁ _hζ a
  have halpha :
      Section5.cfNormSq (τ (alphaChar μ ζ n δ j0 i0 j)) =
        (2 : ℝ) + (n : ℝ) ^ 2 :=
    theorem_10_10_3_supported_alpha_tau_cfNormSq_source
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj
  have hineqR :
      (S₁.card : ℝ) * (a : ℝ) ^ 2 -
          2 * (a : ℝ) * (n : ℝ) - 2 ≤ 0 := by
    rw [hproj, halpha] at hle
    nlinarith
  have hineqZ :
      (S₁.card : ℤ) * a ^ 2 - 2 * a * (n : ℤ) - 2 ≤ 0 := by
    exact_mod_cast hineqR
  have ha0 : a = 0 :=
    typeVCharacterCount_integer_coefficient_eq_zero _hred _hcount hineqZ
  rw [ha0] at ha
  simpa using ha

public theorem theorem_10_10_3_supported_corrected_alpha_norm_two_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    Section5.cfNormSq
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) = 2 := by
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ζ n δ j0 i0 j)
  let Z : Section1.ClassFunction G := τ₁ ζ
  let Y : Section1.ClassFunction G := Aτ + (n : ℂ) • Z
  have hYZ : Section1.scalarProduct G Y Z = 0 := by
    dsimp [Y, Z, Aτ]
    exact theorem_10_10_3_supported_corrected_alpha_pairing_eq_zero_source
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj
  have hZY : Section1.scalarProduct G Z Y = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hYZ
  have hY_nZ : Section1.scalarProduct G Y ((n : ℂ) • Z) = 0 := by
    rw [Section1.scalarProduct_smul_right, hYZ]
    simp
  have hnZ_Y : Section1.scalarProduct G ((n : ℂ) • Z) Y = 0 := by
    rw [Section1.scalarProduct_smul_left, hZY]
    simp
  have hAeq : Aτ = Y - (n : ℂ) • Z := by
    dsimp [Aτ, Y, Z]
    ext g
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  have hdecomp :
      Section5.cfNormSq Aτ =
        Section5.cfNormSq Y + Section5.cfNormSq ((n : ℂ) • Z) := by
    rw [hAeq]
    exact Section5.cfNormSq_sub_eq_add_of_orthogonal hY_nZ hnZ_Y
  have hAτnorm : Section5.cfNormSq Aτ = (2 : ℝ) + (n : ℝ) ^ 2 := by
    dsimp [Aτ]
    exact theorem_10_10_3_supported_alpha_tau_cfNormSq_source
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj
  have hZZ : Section1.scalarProduct G Z Z = 1 := by
    dsimp [Z]
    simpa using theorem_10_10_3_tauOne_sOne_scalarProduct_eq_ite
      _hcount _hτ₁ _hζ _hζ
  have hZnorm : Section5.cfNormSq Z = 1 := by
    unfold Section5.cfNormSq
    rw [hZZ]
    simp
  have hnZnorm : Section5.cfNormSq ((n : ℂ) • Z) = (n : ℝ) ^ 2 := by
    rw [Section5.cfNormSq_smul, hZnorm]
    simp [pow_two]
  change Section5.cfNormSq Y = 2
  nlinarith

public theorem coefficientNonzeroCount_sigma_omega_le_two_of_virtual_norm_two_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    {Y : Section1.ClassFunction G}
    (hYvirt : IsVirtualCharacter Y)
    (hYnorm : Section5.cfNormSq Y = 2) :
    Section3.coefficientNonzeroCount
        (fun i j => Section1.scalarProduct G Y (σ (ω i j))) ≤ 2 := by
  classical
  let χ : I × J → Section1.ClassFunction G := fun p => σ (ω p.1 p.2)
  have horth : ∀ p q : I × J,
      Section1.scalarProduct G (χ p) (χ q) = if p = q then 1 else 0 := by
    intro p q
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    dsimp [χ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        hnotation i i' j j'
  have hχvirt : ∀ p : I × J, IsVirtualCharacter (χ p) := by
    intro p
    rcases hnotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, _h46, hω, _hIso, hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    exact hVirt (ω p.1 p.2)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible p.1 p.2))
  have hcount :=
    finite_orthonormal_virtual_coeff_support_card_le_two
      χ horth hχvirt hYvirt hYnorm
  simpa [Section3.coefficientNonzeroCount, χ] using hcount

public theorem theorem_10_10_3_supported_corrected_alpha_sigma_omega_count_le_two
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    Section3.coefficientNonzeroCount
        (fun i k =>
          Section1.scalarProduct G
            (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ)
            (σ (ω i k))) ≤ 2 := by
  have hAvirt :
      IsVirtualCharacter
        (τ (alphaChar μ ζ n δ j0 i0 j)) :=
    theorem_10_10_3_supported_alpha_tau_isVirtualCharacter
      hred h10 hcount hnotation hζ hj
  have hζvirt : IsVirtualCharacter (τ₁ ζ) :=
    theorem_10_10_3_tauOne_sOne_isVirtualCharacter hτ₁ hζ
  have hYvirt :
      IsVirtualCharacter
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) :=
    Section3.isVirtualCharacter_add hAvirt
      (isVirtualCharacter_natCast_smul_sec10 n hζvirt)
  have hYnorm :
      Section5.cfNormSq
        (τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) = 2 :=
    theorem_10_10_3_supported_corrected_alpha_norm_two_source
      hred h10 hnotation hcount hτ₁ hζ hj
  exact coefficientNonzeroCount_sigma_omega_le_two_of_virtual_norm_two_supported
    hnotation hYvirt hYnorm

public theorem theorem_10_10_3_supported_alpha_fourTenTerm_pairing_eq_signed_rectangle_pairing
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    {j : J} (hj : j ≠ j0)
    (i : I) (k : J) :
    let B : Section1.ClassFunction M :=
      (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let R : Section1.ClassFunction G :=
      (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
    Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) B =
      Section1.scalarProduct G Z R := by
  classical
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let R : Section1.ClassFunction G :=
    (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
  have hSupportedData :=
    supportedFourSixData_of_section10FourSixNotationSupportedData hnotation
  rcases hSupportedData with
    ⟨σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) :=
    h43b.2.2.1
  have hμdistinct :
      ∀ p q : I × J, p ≠ q → μ p.1 p.2 ≠ μ q.1 q.2 :=
    h43b.2.2.2.1
  have hμorth : ∀ a b c e,
      Section1.scalarProduct M (μ a b) (μ c e) =
        if (a, b) = (c, e) then (1 : ℂ) else 0 := by
    intro a b c e
    by_cases hp : (a, b) = (c, e)
    · have hac : a = c := congrArg Prod.fst hp
      have hbe : b = e := congrArg Prod.snd hp
      subst c
      subst e
      simp [scalarProduct_irreducible_self (hμirr a b)]
    · have hne : μ a b ≠ μ c e := hμdistinct (a, b) (c, e) hp
      simp [hp, scalarProduct_irreducible_ne (hμirr a b) (hμirr c e) hne]
  have hcountCopy := hcount
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, hδ, _hn⟩
  have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := (hS1irr ζ hζ).1
  have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) := (hS1irr ζ hζ).2
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  have hW1gt : 1 < Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    exact hW1gt
  have hpneW1 : (p : ℂ) ≠ (Nat.card W1 : ℂ) := by
    have hpneNat : p ≠ Nat.card W1 := by
      rw [hpEq]
      omega
    exact_mod_cast hpneNat
  have hOneNeW1 : (1 : ℂ) ≠ (Nat.card W1 : ℂ) := by
    have hOneNeNat : (1 : ℕ) ≠ Nat.card W1 := by omega
    exact_mod_cast hOneNeNat
  have hζ_ne_μ : ∀ a b, ζ ≠ μ a b := by
    intro a b hEq
    have hdegEq := congrArg Section1.degree hEq
    by_cases hb : b = j0
    · subst b
      have hbase : Section1.degree (μ a j0) = 1 :=
        baseColumn_degree_one_of_section10FourSixNotationSupportedData
          hnotation a
      rw [hζdeg, hbase] at hdegEq
      exact hOneNeW1 hdegEq.symm
    · have hdeg : Section1.degree (μ a b) = (p : ℂ) :=
        degree_mu_of_typeV_supported hred h10 hnotation hb
      rw [hζdeg, hdeg] at hdegEq
      exact hpneW1 hdegEq.symm
  have hζμ : ∀ a b, Section1.scalarProduct M ζ (μ a b) = 0 := by
    intro a b
    exact scalarProduct_irreducible_ne hζirr (hμirr a b) (hζ_ne_μ a b)
  have hμζ : ∀ a b, Section1.scalarProduct M (μ a b) ζ = 0 := by
    intro a b
    simpa [Section1.scalarProduct_star_swap] using congrArg star (hζμ a b)
  have hδj : (δSign j : ℂ) = (δ : ℂ) := by
    have hsignj : δSign j = -1 :=
      deltaSign_eq_neg_one_of_typeVCharacterCountData_supported
        hred h10 hcountCopy hnotation hj
    rw [hsignj, hδ]
  have hδ0 : (δSign j0 : ℂ) = (1 : ℂ) := by
    exact (Section4.proposition_4_4_base
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (I := I)
      (J := J)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σ := σM)
      (piChar := μ)
      (deltaSign := fun j => (δSign j : ℂ))
      hω h43b).1
  have hσorth : ∀ a b c e,
      Section1.scalarProduct G (σ (ω a b)) (σ (ω c e)) =
        if (a, b) = (c, e) then (1 : ℂ) else 0 := by
    intro a b c e
    exact scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
      hnotation a c b e
  have hα :
      alphaChar μ ζ n δ j0 i0 j =
        μ i0 j + (-(δ : ℂ)) • μ i0 j0 + (-(n : ℂ)) • ζ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hB :
      B =
        (δSign k : ℂ) • μ i k + (-(δSign k : ℂ)) • μ i0 k +
          (-1 : ℂ) • μ i j0 + μ i0 j0 := by
    ext x
    simp [B, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hZ :
      Z = (δ : ℂ) • σ (ω i0 j) + (-(δ : ℂ)) • σ (ω i0 j0) := by
    ext x
    simp [Z, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hR :
      R =
        σ (ω i k) + (-1 : ℂ) • σ (ω i0 k) +
          (-1 : ℂ) • σ (ω i j0) + σ (ω i0 j0) := by
    ext x
    simp [R, Pi.sub_apply, Pi.add_apply]
    ring
  change
    Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) B =
      Section1.scalarProduct G Z R
  rw [hα, hB, hZ, hR]
  simp only [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
    Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    hμorth, hζμ, hσorth]
  by_cases hkj : k = j
  · subst k
    have hj' : j0 ≠ j := fun h => hj h.symm
    by_cases hi : i0 = i
    · simp [hδj, hj, hj', hi]
    · simp [hδj, hj, hj', hi]
  · by_cases hk0 : k = j0
    · subst k
      simp [hδ0, hj]
    · simp [hj]
      have hjk : j ≠ k := fun h => hkj h.symm
      have hj0k : j0 ≠ k := fun h => hk0 h.symm
      simp [hjk, hj0k]


public theorem theorem_10_10_3_supported_corrected_alpha_residual_sigma_omega_base_rectangle
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0)
    (i : I) (k : J) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let R : Section1.ClassFunction G :=
      (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
    Section1.scalarProduct G (Y - Z) R = 0 := by
  classical
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ζ n δ j0 i0 j)
  let Y : Section1.ClassFunction G := Aτ + (n : ℂ) • τ₁ ζ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let R : Section1.ClassFunction G :=
    (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  have hτ₁R : Section1.scalarProduct G (τ₁ ζ) R = 0 := by
    have h1 : Section1.scalarProduct G (τ₁ ζ) (σ (ω i k)) = 0 :=
      theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
        hred h10 hcount hnotation hζ hτ₁ i k
    have h2 : Section1.scalarProduct G (τ₁ ζ) (σ (ω i0 k)) = 0 :=
      theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
        hred h10 hcount hnotation hζ hτ₁ i0 k
    have h3 : Section1.scalarProduct G (τ₁ ζ) (σ (ω i j0)) = 0 :=
      theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
        hred h10 hcount hnotation hζ hτ₁ i j0
    have h4 : Section1.scalarProduct G (τ₁ ζ) (σ (ω i0 j0)) = 0 :=
      theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
        hred h10 hcount hnotation hζ hτ₁ i0 j0
    dsimp [R]
    rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, h1, h2, h3, h4]
    simp
  have hαA0 :
      Section1.supportedOn (alphaChar μ ζ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    typeVAlpha_supportedOn_primeDadeA0_of_typeVCharacterCountData_supported
      hred h10 hcount hnotation hζ hj
  have hBA0 :
      Section1.supportedOn B
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    simpa [B] using
      fourTenTerm_supportedOn_primeDadeA0_of_section10FourSixNotationSupportedData
        hnotation
          (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hnotation)
          i k
  have hμIrr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hμIrr i j))
  have hζClass : Section1.IsClassFunction ζ := by
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hS1irr ζ hζ).1)
  have hαClass :
      Section1.IsClassFunction (alphaChar μ ζ n δ j0 i0 j) := by
    intro x g
    simp [alphaChar, hμClass i0 j x g, hμClass i0 j0 x g, hζClass x g]
  have hBClass : Section1.IsClassFunction B := by
    intro x g
    simp [B, hμClass i k x g, hμClass i0 k x g, hμClass i j0 x g,
      hμClass i0 j0 x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hRτB : τ B = R := by
    have h410 := theorem_4_10_of_section10FourSixNotationSupportedData
      hnotation i k
    simpa [B, R] using h410
  have hAτR : Section1.scalarProduct G Aτ R = Section1.scalarProduct G Z R := by
    have hsource :=
      theorem_10_10_3_supported_alpha_fourTenTerm_pairing_eq_signed_rectangle_pairing
        hred h10 hcount hnotation hζ hj i k
    calc
      Section1.scalarProduct G Aτ R =
          Section1.scalarProduct G (τ (alphaChar μ ζ n δ j0 i0 j)) (τ B) := by
        simp [Aτ, hRτB]
      _ = Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) B := by
        exact hτiso (alphaChar μ ζ n δ j0 i0 j) B hαClass hBClass hαA0 hBA0
      _ = Section1.scalarProduct G Z R := by
        simpa [B, Z, R] using hsource
  change Section1.scalarProduct G (Y - Z) R = 0
  have hYR : Section1.scalarProduct G Y R = Section1.scalarProduct G Z R := by
    dsimp [Y]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hAτR, hτ₁R]
    simp
  rw [Section5.scalarProduct_sub_left, hYR]
  simp

public theorem theorem_10_10_3_supported_corrected_alpha_residual_sigma_omega_rectangle_relation
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let b : I → J → ℂ := fun i k =>
      Section1.scalarProduct G (Y - Z) (σ (ω i k))
    ∀ i i' k k', b i k + b i' k' = b i k' + b i' k := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let b : I → J → ℂ := fun i k =>
    Section1.scalarProduct G (Y - Z) (σ (ω i k))
  have hbase : ∀ i k, b i k = b i0 k + b i j0 - b i0 j0 := by
    intro i k
    have hzero :=
      theorem_10_10_3_supported_corrected_alpha_residual_sigma_omega_base_rectangle
        hred h10 hcount hnotation hζ hτ₁ hj i k
    change
      Section1.scalarProduct G (Y - Z)
        ((σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))) = 0
        at hzero
    rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right] at hzero
    dsimp [b] at hzero ⊢
    rw [sub_eq_zero] at hzero
    calc
      Section1.scalarProduct G (Y - Z) (σ (ω i k)) =
          Section1.scalarProduct G (Y - Z) (σ (ω i0 k)) +
            (Section1.scalarProduct G (Y - Z) (σ (ω i k)) -
              Section1.scalarProduct G (Y - Z) (σ (ω i0 k))) := by
            ring
      _ = Section1.scalarProduct G (Y - Z) (σ (ω i0 k)) +
            (Section1.scalarProduct G (Y - Z) (σ (ω i j0)) -
              Section1.scalarProduct G (Y - Z) (σ (ω i0 j0))) := by
            rw [hzero]
      _ = Section1.scalarProduct G (Y - Z) (σ (ω i0 k)) +
            Section1.scalarProduct G (Y - Z) (σ (ω i j0)) -
            Section1.scalarProduct G (Y - Z) (σ (ω i0 j0)) := by
            ring
  change ∀ i i' k k', b i k + b i' k' = b i k' + b i' k
  intro i i' k k'
  rw [hbase i k, hbase i' k', hbase i k', hbase i' k]
  ring

public theorem theorem_10_10_3_supported_corrected_alpha_residual_base_row_coefficients_vanish
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    {j : J} (hj : j ≠ j0) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let b : I → J → ℂ := fun i k =>
      Section1.scalarProduct G (Y - Z) (σ (ω i k))
    b i0 j = 0 ∧ b i0 j0 = 0 := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let a : I → J → ℂ := fun i k =>
    Section1.scalarProduct G Y (σ (ω i k))
  let b : I → J → ℂ := fun i k =>
    Section1.scalarProduct G (Y - Z) (σ (ω i k))
  have hW1ge3 : 3 ≤ Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    rcases hW1Odd with ⟨k, hk⟩
    omega
  have hI3 : 3 ≤ Fintype.card I := by
    have hIcard :
        Nat.card I = Nat.card W1 :=
      uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
        h10 hnotation
    have hI3Nat : 3 ≤ Nat.card I := by
      rw [hIcard]
      exact hW1ge3
    simpa [Nat.card_eq_fintype_card] using hI3Nat
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  have hJcard : Nat.card J = p := by
    rcases hcount with
      ⟨hJ, _hdecomp, _hS1card, _hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact hJ
  have hJ5 : 5 ≤ Fintype.card J := by
    have hJ5Nat : 5 ≤ Nat.card J := by
      rw [hJcard, hpEq]
      omega
    simpa [Nat.card_eq_fintype_card] using hJ5Nat
  have hδeq : δ = -1 := by
    rcases hcount with
      ⟨_hJ, _hdecomp, _hS1card, _hS1irr, _hmu, _hd, hδ, _hn⟩
    exact hδ
  have hδne : (δ : ℂ) ≠ 0 := by
    rw [hδeq]
    norm_num
  have ha : Section3.coefficientNonzeroCount a ≤ 2 := by
    dsimp [a, Y]
    exact theorem_10_10_3_supported_corrected_alpha_sigma_omega_count_le_two
      hred h10 hcount hnotation hζ hτ₁ hj
  have hrect : ∀ i i' k k', b i k + b i' k' = b i k' + b i' k := by
    simpa [Y, Z, b] using
      theorem_10_10_3_supported_corrected_alpha_residual_sigma_omega_rectangle_relation
        hred h10 hcount hnotation hζ hτ₁ hj
  have hZ_j :
      Section1.scalarProduct G Z (σ (ω i0 j)) = (δ : ℂ) := by
    have hφφ : Section1.scalarProduct G (σ (ω i0 j)) (σ (ω i0 j)) = 1 := by
      simpa using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
          hnotation i0 i0 j j
    have hψφ :
        Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i0 j)) = 0 := by
      have hj' : j0 ≠ j := fun h => hj h.symm
      simpa [hj'] using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
          hnotation i0 i0 j0 j
    dsimp [Z]
    rw [Section1.scalarProduct_smul_left, Section5.scalarProduct_sub_left,
      hφφ, hψφ]
    ring
  have hZ_j0 :
      Section1.scalarProduct G Z (σ (ω i0 j0)) = -(δ : ℂ) := by
    have hφψ : Section1.scalarProduct G (σ (ω i0 j)) (σ (ω i0 j0)) = 0 := by
      simpa [hj] using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
          hnotation i0 i0 j j0
    have hψψ :
        Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i0 j0)) = 1 := by
      simpa using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
          hnotation i0 i0 j0 j0
    dsimp [Z]
    rw [Section1.scalarProduct_smul_left, Section5.scalarProduct_sub_left,
      hφψ, hψψ]
    ring
  have hupdate_j : a i0 j = b i0 j + (δ : ℂ) := by
    dsimp [a, b]
    rw [Section5.scalarProduct_sub_left, hZ_j]
    ring
  have hupdate_j0 : a i0 j0 = b i0 j0 - (δ : ℂ) := by
    dsimp [a, b]
    rw [Section5.scalarProduct_sub_left, hZ_j0]
    ring
  have hupdate_other : ∀ i k, (i, k) ≠ (i0, j) → (i, k) ≠ (i0, j0) →
      a i k = b i k := by
    intro i k hcell hcell0
    have hZik : Section1.scalarProduct G Z (σ (ω i k)) = 0 := by
      have hleft :
          Section1.scalarProduct G (σ (ω i0 j)) (σ (ω i k)) = 0 := by
        have hnot : ¬ (i0 = i ∧ j = k) := by
          rintro ⟨hi, hk⟩
          exact hcell (by simp [hi, hk])
        simpa [hnot] using
          scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
            hnotation i0 i j k
      have hright :
          Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i k)) = 0 := by
        have hnot : ¬ (i0 = i ∧ j0 = k) := by
          rintro ⟨hi, hk⟩
          exact hcell0 (by simp [hi, hk])
        simpa [hnot] using
          scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
            hnotation i0 i j0 k
      dsimp [Z]
      rw [Section1.scalarProduct_smul_left, Section5.scalarProduct_sub_left,
        hleft, hright]
      simp
    dsimp [a, b]
    rw [Section5.scalarProduct_sub_left, hZik]
    simp
  simpa [Y, Z, b] using
    rectangle_two_cell_update_base_row_vanish
      a b hj hδne hI3 hJ5 ha hrect hupdate_j hupdate_j0 hupdate_other

public theorem theorem_10_10_3_supported_alpha_tau_residual_baseRow_coefficients_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) -
          (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)))
        (σ (ω i0 j)) = 0 ∧
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j) -
          (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)))
        (σ (ω i0 j0)) = 0 := by
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ζ n δ j0 i0 j)
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  have hcorr :=
    theorem_10_10_3_supported_corrected_alpha_residual_base_row_coefficients_vanish
      _hred _h10 _hcount _hnotation _hζ _hτ₁ _hj
  have hcorrj :
      Section1.scalarProduct G ((Aτ + (n : ℂ) • τ₁ ζ) - Z)
          (σ (ω i0 j)) = 0 := by
    simpa [Aτ, Z] using hcorr.1
  have hcorrj0 :
      Section1.scalarProduct G ((Aτ + (n : ℂ) • τ₁ ζ) - Z)
          (σ (ω i0 j0)) = 0 := by
    simpa [Aτ, Z] using hcorr.2
  have hζj : Section1.scalarProduct G (τ₁ ζ) (σ (ω i0 j)) = 0 :=
    theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
      _hred _h10 _hcount _hnotation _hζ _hτ₁ i0 j
  have hζj0 : Section1.scalarProduct G (τ₁ ζ) (σ (ω i0 j0)) = 0 :=
    theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
      _hred _h10 _hcount _hnotation _hζ _hτ₁ i0 j0
  constructor
  · change Section1.scalarProduct G (Aτ - Z) (σ (ω i0 j)) = 0
    have hsplit :
        (Aτ + (n : ℂ) • τ₁ ζ) - Z =
          (Aτ - Z) + (n : ℂ) • τ₁ ζ := by
      ext x
      simp [Aτ, Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hsplit, Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left, hζj] at hcorrj
    simpa using hcorrj
  · change Section1.scalarProduct G (Aτ - Z) (σ (ω i0 j0)) = 0
    have hsplit :
        (Aτ + (n : ℂ) • τ₁ ζ) - Z =
          (Aτ - Z) + (n : ℂ) • τ₁ ζ := by
      ext x
      simp [Aτ, Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hsplit, Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left, hζj0] at hcorrj0
    simpa using hcorrj0

public theorem theorem_10_10_3_supported_residual_baseRow_coefficients_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    Section1.scalarProduct G
        ((τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) -
          (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)))
        (σ (ω i0 j)) = 0 ∧
      Section1.scalarProduct G
        ((τ (alphaChar μ ζ n δ j0 i0 j) + (n : ℂ) • τ₁ ζ) -
          (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)))
        (σ (ω i0 j0)) = 0 := by
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ζ n δ j0 i0 j)
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  have hAZ :=
    theorem_10_10_3_supported_alpha_tau_residual_baseRow_coefficients_source
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj
  have hAZj : Section1.scalarProduct G (Aτ - Z) (σ (ω i0 j)) = 0 := by
    simpa [Aτ, Z] using hAZ.1
  have hAZj0 :
      Section1.scalarProduct G (Aτ - Z) (σ (ω i0 j0)) = 0 := by
    simpa [Aτ, Z] using hAZ.2
  have hζj : Section1.scalarProduct G (τ₁ ζ) (σ (ω i0 j)) = 0 :=
    theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
      _hred _h10 _hcount _hnotation _hζ _hτ₁ i0 j
  have hζj0 : Section1.scalarProduct G (τ₁ ζ) (σ (ω i0 j0)) = 0 :=
    theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
      _hred _h10 _hcount _hnotation _hζ _hτ₁ i0 j0
  constructor
  · change
      Section1.scalarProduct G ((Aτ + (n : ℂ) • τ₁ ζ) - Z)
          (σ (ω i0 j)) = 0
    have hsplit :
        (Aτ + (n : ℂ) • τ₁ ζ) - Z =
          (Aτ - Z) + (n : ℂ) • τ₁ ζ := by
      ext x
      simp [Aτ, Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hsplit, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hAZj, hζj]
    simp
  · change
      Section1.scalarProduct G ((Aτ + (n : ℂ) • τ₁ ζ) - Z)
          (σ (ω i0 j0)) = 0
    have hsplit :
        (Aτ + (n : ℂ) • τ₁ ζ) - Z =
          (Aτ - Z) + (n : ℂ) • τ₁ ζ := by
      ext x
      simp [Aτ, Z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hsplit, Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hAZj0, hζj0]
    simp

public theorem theorem_10_10_3_supported_baseRow_alpha_formula_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    τ (alphaChar μ ζ n δ j0 i0 j) =
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) - (n : ℂ) • τ₁ ζ := by
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ζ n δ j0 i0 j)
  let Zζ : Section1.ClassFunction G := τ₁ ζ
  let φ : Section1.ClassFunction G := σ (ω i0 j)
  let ψ : Section1.ClassFunction G := σ (ω i0 j0)
  have hδ : δ = -1 := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, _hS1irr, _hmu, _hd, hδ, _hn⟩
    exact hδ
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by
    rw [hδ]
    norm_num
  have hφφ : Section1.scalarProduct G φ φ = 1 := by
    dsimp [φ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        _hnotation i0 i0 j j
  have hψψ : Section1.scalarProduct G ψ ψ = 1 := by
    dsimp [ψ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        _hnotation i0 i0 j0 j0
  have hφψ : Section1.scalarProduct G φ ψ = 0 := by
    dsimp [φ, ψ]
    simpa [_hj] using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        _hnotation i0 i0 j j0
  have hψφ : Section1.scalarProduct G ψ φ = 0 := by
    have hj' : j0 ≠ j := fun hEq => _hj hEq.symm
    dsimp [φ, ψ]
    simpa [hj'] using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        _hnotation i0 i0 j0 j
  have hYnorm :
      Section5.cfNormSq (Aτ + (n : ℂ) • Zζ) = 2 := by
    dsimp [Aτ, Zζ]
    exact theorem_10_10_3_supported_corrected_alpha_norm_two_source
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj
  rcases theorem_10_10_3_supported_residual_baseRow_coefficients_source
      _hred _h10 _hnotation _hcount _hτ₁ _hζ _hj with
    ⟨hRφ, hRψ⟩
  have hYeq :
      Aτ + (n : ℂ) • Zζ = (δ : ℂ) • (φ - ψ) :=
    classFunction_eq_signed_sub_of_norm_two_and_residual_orthogonal
      hδnorm hφφ hψψ hφψ hψφ hYnorm
      (by simpa [Aτ, Zζ, φ, ψ] using hRφ)
      (by simpa [Aτ, Zζ, φ, ψ] using hRψ)
  dsimp [Aτ, Zζ, φ, ψ] at hYeq
  rw [← hYeq]
  ext g
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

public theorem theorem_10_10_4_supported_alpha_formula_from_notation_count_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁) :
    typeVAlphaFormulaData W A0 j0 μ ω σ ζ τ τ₁ n δ := by
  intro i j hj
  refine ⟨?_, ?_⟩
  · exact typeVAlpha_supportedOn_a0_of_typeVCharacterCountData_supported
      hred h10 hcount hnotation hζ hj
  · have hbase :=
      theorem_10_10_3_supported_baseRow_alpha_formula_source
        hred h10 hnotation hcount hτ₁ hζ hj
    have hδ : δ = -1 := by
      rcases hcount with
        ⟨_hJ, _hdecomp, _hS1card, _hS1irr, _hmu, _hd, hδ, _hn⟩
      exact hδ
    have hδsq : ((δ : ℂ) * (δ : ℂ) = 1) := by
      rw [hδ]
      norm_num
    have hδj : δSign j = δ := by
      rw [hδ]
      exact deltaSign_eq_neg_one_of_typeVCharacterCountData_supported
        hred h10 hcount hnotation hj
    have h410 := theorem_4_10_of_section10FourSixNotationSupportedData hnotation
    have hfour :
        τ ((δ : ℂ) • μ i j - (δ : ℂ) • μ i0 j - μ i j0 + μ i0 j0) =
          (σ (ω i j) - σ (ω i0 j)) - (σ (ω i j0) - σ (ω i0 j0)) := by
      simpa [hδj] using h410 i j
    have hdiff_arg :
        alphaChar μ ζ n δ j0 i j - alphaChar μ ζ n δ j0 i0 j =
          (δ : ℂ) •
            ((δ : ℂ) • μ i j - (δ : ℂ) • μ i0 j - μ i j0 + μ i0 j0) :=
      alphaChar_sub_baseRow_eq_sign_smul_fourTenTerm μ ζ n δ j0 i i0 j hδsq
    have hdiff :
        τ (alphaChar μ ζ n δ j0 i j - alphaChar μ ζ n δ j0 i0 j) =
          (δ : ℂ) • ((σ (ω i j) - σ (ω i0 j)) -
            (σ (ω i j0) - σ (ω i0 j0))) := by
      rw [hdiff_arg, map_smul, hfour]
    have hadd :
        τ (alphaChar μ ζ n δ j0 i j) =
          τ (alphaChar μ ζ n δ j0 i j - alphaChar μ ζ n δ j0 i0 j) +
            τ (alphaChar μ ζ n δ j0 i0 j) := by
      rw [← map_add]
      congr 1
      abel
    rw [hadd, hdiff, hbase]
    ext x
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

public theorem degree_mu_congruent_mod_card_W1_of_hypothesis_10_1_supported_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hdata :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (i : I) (j : J) :
    ∃ a : ℤ,
      Section1.degree (μ i j) =
        (δSign j : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ)) := by
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hdata with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hσisoFull, _hσvirtFull, _hmaps, _hprincipal,
      _h2A, htail⟩
  rcases htail with
    ⟨_hωfull, _h43b, _h43c, h43d, _h45a, _h45b, _htauTI, _htauA0,
      _htauIso, _htauPunct, _htauVirt, _hPF39⟩
  rcases h43d i j with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hcard : Fintype.card (W1.subgroupOf M) = Fintype.card W1 :=
    Fintype.card_congr (Subgroup.subgroupOfEquivOfLe hW1M).toEquiv
  simpa [Nat.card_eq_fintype_card, hcard] using ha


public theorem theorem_10_9_candidate_supportedOn_primeDadeA0_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section1.supportedOn (μ0 - ξ)
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  classical
  have hμ0Derived :
      Section1.supportedOn μ0 ((derivedSubgroup M : Subgroup M) : Set M) := by
    rw [hμ0]
    rcases exists_irreducible_inducing_muColumn_of_section10FourSixNotationSupportedData
        hnotation j0 with ⟨θ, _hθIrr, hcol⟩
    rw [hcol]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ
  have hξDerived :=
    supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
      h10 hξS
  have hdiffDerived := supportedOn_sub_local hμ0Derived hξDerived
  have hμIrr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμIrr i j))
  have hμ0Class : Section1.IsClassFunction μ0 := by
    rw [hμ0]
    intro x g
    unfold muColumn
    simpa using Finset.sum_congr rfl (fun i _hi => hμClass i j0 x g)
  have hξClass : Section1.IsClassFunction ξ :=
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
  have hdiffClass : Section1.IsClassFunction (μ0 - ξ) := by
    intro x g
    simp [hμ0Class x g, hξClass x g]
  have hIcard : (Fintype.card I : ℂ) = (Nat.card W1 : ℂ) := by
    have hI : Nat.card I = Nat.card W1 :=
      uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
        h10 hnotation
    exact_mod_cast (by
      simpa [Nat.card_eq_fintype_card] using hI :
        Fintype.card I = Nat.card W1)
  have hμ0deg : Section1.degree μ0 = (Fintype.card I : ℂ) := by
    rw [hμ0]
    unfold muColumn Section1.degree
    calc
      ((∑ c : I, μ c j0 : Section1.ClassFunction M) 1) =
          ∑ c : I, μ c j0 1 := by simp
      _ = ∑ _c : I, (1 : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro c _hc
        simpa [Section1.degree] using
          baseColumn_degree_one_of_section10FourSixNotationSupportedData
            hnotation c
      _ = (Fintype.card I : ℂ) := by simp
  have hdeg : Section1.degree (μ0 - ξ) = 0 := by
    unfold Section1.degree
    have hμ01 : μ0 1 = (Fintype.card I : ℂ) := by
      simpa [Section1.degree] using hμ0deg
    have hξ1 : ξ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hξDegree
    simp [Pi.sub_apply, hμ01, hξ1, hIcard]
  exact supportedOn_primeDadeA0_of_supportedOn_derivedSubgroup_degree_zero
    hnotation
      (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hnotation)
      hdiffClass hdiffDerived hdeg

public theorem theorem_10_9_xi_orthogonal_mu_entries_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (i : I) (j : J) :
    Section1.scalarProduct M (μ i j) ξ = 0 ∧
      Section1.scalarProduct M ξ (μ i j) = 0 := by
  classical
  have hW1gt : 1 < Nat.card W1 := theorem_10_9_one_lt_card_W1_supported h10
  have hμirr : Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1 i j
  have hne : μ i j ≠ ξ := by
    intro hEq
    rcases degree_mu_congruent_mod_card_W1_of_hypothesis_10_1_supported_data
        h10 hnotation i j with ⟨a, haC⟩
    have hdegEq : Section1.degree (μ i j) = (Nat.card W1 : ℂ) := by
      rw [hEq, hξDegree]
    have hC :
        (Nat.card W1 : ℂ) =
          (δSign j : ℂ) + (a : ℂ) * (Nat.card W1 : ℂ) :=
      hdegEq.symm.trans haC
    have hZ :
        (Nat.card W1 : ℤ) =
          δSign j + a * (Nat.card W1 : ℤ) := by
      exact_mod_cast hC
    have hsign : Section1.IsSign ((δSign j : ℂ)) := by
      rcases supportedFourSixData_of_section10FourSixNotationSupportedData
          hnotation with
        ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
      rcases hSupported with
        ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
          hFullRest⟩
      rcases hFullRest with
        ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
          _hτiso, _hτpunct, _hτvirt, _hPF39⟩
      exact h43b.2.1 j
    rw [Section1.IsSign] at hsign
    rcases hsign with hδ | hδ
    · have hδZ : δSign j = 1 := by exact_mod_cast hδ
      have hdvd : (Nat.card W1 : ℤ) ∣ (1 : ℤ) := by
        use 1 - a
        rw [hδZ] at hZ
        calc
          (1 : ℤ) = (Nat.card W1 : ℤ) - a * (Nat.card W1 : ℤ) := by
            omega
          _ = (Nat.card W1 : ℤ) * (1 - a) := by
            ring
      have hle : (Nat.card W1 : ℤ) ≤ 1 :=
        Int.le_of_dvd (by norm_num) hdvd
      omega
    · have hδZ : δSign j = -1 := by exact_mod_cast hδ
      have hdvdNeg : (Nat.card W1 : ℤ) ∣ (-1 : ℤ) := by
        use 1 - a
        rw [hδZ] at hZ
        calc
          (-1 : ℤ) = (Nat.card W1 : ℤ) - a * (Nat.card W1 : ℤ) := by
            omega
          _ = (Nat.card W1 : ℤ) * (1 - a) := by
            ring
      have hdvd : (Nat.card W1 : ℤ) ∣ (1 : ℤ) :=
        dvd_neg.mp (by simpa using hdvdNeg)
      have hle : (Nat.card W1 : ℤ) ≤ 1 :=
        Int.le_of_dvd (by norm_num) hdvd
      omega
  have hleft : Section1.scalarProduct M (μ i j) ξ = 0 :=
    scalarProduct_irreducible_ne hμirr hξIrr hne
  have hright : Section1.scalarProduct M ξ (μ i j) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hleft
  exact ⟨hleft, hright⟩


public theorem theorem_10_9_base_column_sub_xi_fourTenTerm_pairing_eq_zero_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (i : I) (k : J) :
    Section1.scalarProduct M (muColumn μ j0 - ξ)
      ((δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0) = 0 := by
  classical
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  have hcolEntry :
      ∀ p q, Section1.scalarProduct M (muColumn μ j0) (μ p q) =
        if q = j0 then 1 else 0 := by
    intro p q
    have h :=
      theorem_10_9_mu_entry_muColumn_supported hnotation p q j0
    simpa [Section1.scalarProduct_star_swap] using congrArg star h
  have hξEntry :
      ∀ p q, Section1.scalarProduct M ξ (μ p q) = 0 := by
    intro p q
    exact (theorem_10_9_xi_orthogonal_mu_entries_supported
      h10 hnotation hξIrr hξDegree p q).2
  have hcolB : Section1.scalarProduct M (muColumn μ j0) B = 0 := by
    dsimp [B]
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_right]
    rw [hcolEntry i k, hcolEntry i0 k, hcolEntry i j0, hcolEntry i0 j0]
    by_cases hk : k = j0 <;> simp [hk]
  have hξB : Section1.scalarProduct M ξ B = 0 := by
    dsimp [B]
    rw [Section5.scalarProduct_add_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_right]
    rw [hξEntry i k, hξEntry i0 k, hξEntry i j0, hξEntry i0 j0]
    simp
  change Section1.scalarProduct M (muColumn μ j0 - ξ) B = 0
  rw [Section5.scalarProduct_sub_left, hcolB, hξB]
  simp

public theorem theorem_10_9_tau_diff_sigma_omega_base_rectangle_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (i : I) (k : J) :
    let Y : Section1.ClassFunction G := τ (μ0 - ξ)
    let R : Section1.ClassFunction G :=
      (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
    Section1.scalarProduct G Y R = 0 := by
  classical
  let Y : Section1.ClassFunction G := τ (μ0 - ξ)
  let R : Section1.ClassFunction G :=
    (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  have hdiffA0 :
      Section1.supportedOn (μ0 - ξ)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    theorem_10_9_candidate_supportedOn_primeDadeA0_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hBA0 :
      Section1.supportedOn B
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    simpa [B] using
      fourTenTerm_supportedOn_primeDadeA0_of_section10FourSixNotationSupportedData
        hnotation
          (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hnotation)
          i k
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (by
          rcases supportedFourSixData_of_section10FourSixNotationSupportedData
              hnotation with
            ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
          rcases hSupported with
            ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
              hFullRest⟩
          rcases hFullRest with
            ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
              _hτiso, _hτpunct, _hτvirt, _hPF39⟩
          exact h43b.2.2.1 i j))
  have hμ0Class : Section1.IsClassFunction μ0 := by
    rw [hμ0]
    intro x g
    unfold muColumn
    simpa using Finset.sum_congr rfl (fun i _hi => hμClass i j0 x g)
  have hξClass : Section1.IsClassFunction ξ :=
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
  have hdiffClass : Section1.IsClassFunction (μ0 - ξ) := by
    intro x g
    simp [hμ0Class x g, hξClass x g]
  have hBClass : Section1.IsClassFunction B := by
    intro x g
    simp [B, hμClass i k x g, hμClass i0 k x g, hμClass i j0 x g,
      hμClass i0 j0 x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hRτB : τ B = R := by
    have h410 := theorem_4_10_of_section10FourSixNotationSupportedData hnotation i k
    simpa [B, R] using h410
  have hsource :
      Section1.scalarProduct M (μ0 - ξ) B = 0 := by
    rw [hμ0]
    simpa [B] using
      theorem_10_9_base_column_sub_xi_fourTenTerm_pairing_eq_zero_supported
        h10 hnotation hξIrr hξDegree i k
  change Section1.scalarProduct G Y R = 0
  calc
    Section1.scalarProduct G Y R =
        Section1.scalarProduct G (τ (μ0 - ξ)) (τ B) := by
      simp [Y, hRτB]
    _ = Section1.scalarProduct M (μ0 - ξ) B := by
      exact hτiso (μ0 - ξ) B hdiffClass hBClass hdiffA0 hBA0
    _ = 0 := hsource

public theorem theorem_10_9_tau_diff_sigma_omega_rectangle_relation_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    let Y : Section1.ClassFunction G := τ (μ0 - ξ)
    let a : I → J → ℂ := fun i k =>
      Section1.scalarProduct G Y (σ (ω i k))
    ∀ i i' k k', a i k + a i' k' = a i k' + a i' k := by
  classical
  let Y : Section1.ClassFunction G := τ (μ0 - ξ)
  let a : I → J → ℂ := fun i k =>
    Section1.scalarProduct G Y (σ (ω i k))
  have hbase : ∀ i k, a i k = a i0 k + a i j0 - a i0 j0 := by
    intro i k
    have hzero :=
      theorem_10_9_tau_diff_sigma_omega_base_rectangle_supported
        h10 hnotation hμ0 hξS hξIrr hξDegree i k
    change
      Section1.scalarProduct G Y
        ((σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))) = 0
        at hzero
    rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right] at hzero
    dsimp [a] at hzero ⊢
    rw [sub_eq_zero] at hzero
    calc
      Section1.scalarProduct G Y (σ (ω i k)) =
          Section1.scalarProduct G Y (σ (ω i0 k)) +
            (Section1.scalarProduct G Y (σ (ω i k)) -
              Section1.scalarProduct G Y (σ (ω i0 k))) := by
            ring
      _ = Section1.scalarProduct G Y (σ (ω i0 k)) +
            (Section1.scalarProduct G Y (σ (ω i j0)) -
              Section1.scalarProduct G Y (σ (ω i0 j0))) := by
            rw [hzero]
      _ = Section1.scalarProduct G Y (σ (ω i0 k)) +
            Section1.scalarProduct G Y (σ (ω i j0)) -
            Section1.scalarProduct G Y (σ (ω i0 j0)) := by
            ring
  change ∀ i i' k k', a i k + a i' k' = a i k' + a i' k
  intro i i' k k'
  rw [hbase i k, hbase i' k', hbase i k', hbase i' k]
  ring

public theorem theorem_10_9_tau_diff_isVirtualCharacter_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    IsVirtualCharacter (τ (μ0 - ξ)) := by
  classical
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    intro i j
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1 i j
  have hμ0Virt : IsVirtualCharacter μ0 := by
    rw [hμ0]
    unfold muColumn
    refine isVirtualCharacter_finset_sum_sec10_base
      (G := M) (s := Finset.univ) (χ := fun i : I => μ i j0) ?_
    intro i _hi
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hμirr i j0)
  have hξVirt : IsVirtualCharacter ξ :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr
  have hdiffVirt : IsVirtualCharacter (μ0 - ξ) :=
    Section3.isVirtualCharacter_sub hμ0Virt hξVirt
  have hdiffA0 :
      Section1.supportedOn (μ0 - ξ)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    theorem_10_9_candidate_supportedOn_primeDadeA0_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hτvirt :
      Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, hτvirt, _hPF39⟩
    exact hτvirt
  exact hτvirt (μ0 - ξ) hdiffVirt hdiffA0

public theorem theorem_10_9_tau_diff_cfNormSq_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section5.cfNormSq (τ (μ0 - ξ)) = (Nat.card W1 : ℝ) + 1 := by
  classical
  have hdiffA0 :
      Section1.supportedOn (μ0 - ξ)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    theorem_10_9_candidate_supportedOn_primeDadeA0_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hμIrr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    intro i j
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1 i j
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hμIrr i j))
  have hμ0Class : Section1.IsClassFunction μ0 := by
    rw [hμ0]
    intro x g
    unfold muColumn
    simpa using Finset.sum_congr rfl (fun i _hi => hμClass i j0 x g)
  have hξClass : Section1.IsClassFunction ξ :=
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
  have hdiffClass : Section1.IsClassFunction (μ0 - ξ) := by
    intro x g
    simp [hμ0Class x g, hξClass x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hIcard : Fintype.card I = Nat.card W1 := by
    have hI : Nat.card I = Nat.card W1 :=
      uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
        h10 hnotation
    simpa [Nat.card_eq_fintype_card] using hI
  have hcolself :
      Section1.scalarProduct M (muColumn μ j0) (muColumn μ j0) =
        (Fintype.card I : ℂ) := by
    simpa using theorem_10_10_4_muColumn_gram_supported hnotation j0 j0
  have horthLeft : Section1.scalarProduct M (muColumn μ j0) ξ = 0 := by
    unfold muColumn
    have hsum :
        ((∑ i : I, μ i j0 : Section1.ClassFunction M)) =
          fun x => ∑ i : I, μ i j0 x := by
      ext x
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_left]
    simp [fun i => (theorem_10_9_xi_orthogonal_mu_entries_supported
      h10 hnotation hξIrr hξDegree i j0).1]
  have horthRight : Section1.scalarProduct M ξ (muColumn μ j0) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star horthLeft
  have hξself : Section1.scalarProduct M ξ ξ = 1 :=
    scalarProduct_irreducible_self hξIrr
  have hselfM :
      Section1.scalarProduct M (μ0 - ξ) (μ0 - ξ) =
        (Fintype.card I : ℂ) + 1 := by
    rw [hμ0]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    rw [hcolself, horthLeft, horthRight, hξself]
    ring
  have hselfG :
      Section1.scalarProduct G (τ (μ0 - ξ)) (τ (μ0 - ξ)) =
        (Fintype.card I : ℂ) + 1 := by
    rw [hτiso (μ0 - ξ) (μ0 - ξ) hdiffClass hdiffClass hdiffA0 hdiffA0]
    exact hselfM
  unfold Section5.cfNormSq
  rw [hselfG]
  norm_num [hIcard]

public theorem theorem_10_9_tau_diff_sigma_omega_count_lt_two_card_left_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    Section3.coefficientNonzeroCount
        (fun i k =>
          Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i k))) <
      2 * Fintype.card I := by
  classical
  have hYvirt :
      IsVirtualCharacter (τ (μ0 - ξ)) :=
    theorem_10_9_tau_diff_isVirtualCharacter_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hcountR :
      (Section3.coefficientNonzeroCount
          (fun i k =>
            Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i k))) : ℝ) ≤
        Section5.cfNormSq (τ (μ0 - ξ)) :=
    coefficientNonzeroCount_sigma_omega_le_cfNormSq_pf109_supported
      hnotation hYvirt
  have hnorm :
      Section5.cfNormSq (τ (μ0 - ξ)) = (Nat.card W1 : ℝ) + 1 :=
    theorem_10_9_tau_diff_cfNormSq_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hIcard : Fintype.card I = Nat.card W1 := by
    have hI : Nat.card I = Nat.card W1 :=
      uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
        h10 hnotation
    simpa [Nat.card_eq_fintype_card] using hI
  have hW1gt : 1 < Nat.card W1 := theorem_10_9_one_lt_card_W1_supported h10
  have hcount_lt_real :
      (Section3.coefficientNonzeroCount
          (fun i k =>
            Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i k))) : ℝ) <
        ((2 * Fintype.card I : ℕ) : ℝ) := by
    rw [hnorm] at hcountR
    rw [hIcard]
    exact lt_of_le_of_lt hcountR (by
      have hlt_nat : Nat.card W1 + 1 < 2 * Nat.card W1 := by omega
      exact_mod_cast hlt_nat)
  exact_mod_cast hcount_lt_real

public theorem theorem_10_9_omegaColumnSigma_cfNormSq_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ) :
    Section5.cfNormSq (Section4Scratch.omegaColumnSigma σ ω j0) =
      (Nat.card W1 : ℝ) := by
  classical
  have hIcard : Fintype.card I = Nat.card W1 := by
    have hI : Nat.card I = Nat.card W1 :=
      uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data
        h10 hnotation
    simpa [Nat.card_eq_fintype_card] using hI
  have hself :
      Section1.scalarProduct G
          (Section4Scratch.omegaColumnSigma σ ω j0)
          (Section4Scratch.omegaColumnSigma σ ω j0) =
        (Fintype.card I : ℂ) := by
    unfold Section4Scratch.omegaColumnSigma
    have hsum :
        ((∑ i : I, σ (ω i j0) : Section1.ClassFunction G)) =
          fun g => ∑ i : I, σ (ω i j0) g := by
      ext g
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_left]
    calc
      (∑ i : I, Section1.scalarProduct G (σ (ω i j0))
            (fun g => ∑ p : I, σ (ω p j0) g)) =
          ∑ i : I,
            Section1.scalarProduct G (σ (ω i j0))
              (Section4Scratch.omegaColumnSigma σ ω j0) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [← hsum]
            rfl
      _ = ∑ _i : I, (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa using
              scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
                hnotation i j0 j0
      _ = (Fintype.card I : ℂ) := by
            simp
  unfold Section5.cfNormSq
  rw [hself]
  norm_num [hIcard]

public theorem theorem_10_9_candidate_cfNormSq_of_orthogonal_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (horth :
      orthogonalToSigmaIrreducibles W σ
        (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ))) :
    Section5.cfNormSq
      (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)) = 1 := by
  classical
  let Ω0 : Section1.ClassFunction G := Section4Scratch.omegaColumnSigma σ ω j0
  let χ : Section1.ClassFunction G := Ω0 - τ (μ0 - ξ)
  have hΩnorm : Section5.cfNormSq Ω0 = (Nat.card W1 : ℝ) := by
    exact theorem_10_9_omegaColumnSigma_cfNormSq_supported h10 hnotation
  have hτnorm :
      Section5.cfNormSq (τ (μ0 - ξ)) = (Nat.card W1 : ℝ) + 1 :=
    theorem_10_9_tau_diff_cfNormSq_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hdecomp : τ (μ0 - ξ) = Ω0 - χ := by
    dsimp [χ, Ω0]
    exact theorem_10_9_candidate_decomposition_eq hμ0
  have hωdata : Section3.notation_3_3_statement
      (W1.subgroupOf M) (W2.subgroupOf M) W I J i0 j0 ω := by
    rcases hnotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, _h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    exact hω
  have hχΩ : Section1.scalarProduct G χ Ω0 = 0 := by
    dsimp [Ω0]
    unfold Section4Scratch.omegaColumnSigma
    have hsum :
        ((∑ i : I, σ (ω i j0) : Section1.ClassFunction G)) =
          fun g => ∑ i : I, σ (ω i j0) g := by
      ext g
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_right]
    refine Finset.sum_eq_zero ?_
    intro i _hi
    have hzero := horth (ω i j0) (hωdata.irreducible i j0)
    simpa [χ, Ω0] using hzero
  have hΩχ : Section1.scalarProduct G Ω0 χ = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hχΩ
  have hnormDecomp :
      Section5.cfNormSq (τ (μ0 - ξ)) =
        Section5.cfNormSq Ω0 + Section5.cfNormSq χ := by
    rw [hdecomp]
    exact Section5.cfNormSq_sub_eq_add_of_orthogonal hΩχ hχΩ
  rw [hτnorm, hΩnorm] at hnormDecomp
  have hχnorm : Section5.cfNormSq χ = 1 := by
    nlinarith
  simpa [χ, Ω0] using hχnorm

public theorem theorem_10_9_candidate_isVirtualCharacter_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ)) :
    IsVirtualCharacter
      (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)) := by
  classical
  have hτdiffVirt : IsVirtualCharacter (τ (μ0 - ξ)) :=
    theorem_10_9_tau_diff_isVirtualCharacter_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  have hΩvirt :
      IsVirtualCharacter (Section4Scratch.omegaColumnSigma σ ω j0) := by
    rcases hnotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, _h46, hω, _hIso, hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    unfold Section4Scratch.omegaColumnSigma
    refine isVirtualCharacter_finset_sum_sec10_base
      (G := G) (s := Finset.univ) (χ := fun i : I => σ (ω i j0)) ?_
    intro i _hi
    exact hVirt (ω i j0)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible i j0))
  exact Section3.isVirtualCharacter_sub hΩvirt hτdiffVirt

public theorem theorem_10_9_candidate_orthogonal_supported_of_base
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (hW1ltW2 : Nat.card W1 < Nat.card W2)
    (hbase :
      Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i0 j0)) = 1) :
    orthogonalToSigmaIrreducibles W σ
      (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)) := by
  classical
  have hcoeff :=
    theorem_10_9_tau_diff_sigma_omega_single_column_supported_of_bounds
      h10 hnotation hW1ltW2
      (theorem_10_9_tau_diff_isVirtualCharacter_supported
        h10 hnotation hμ0 hξS hξIrr hξDegree)
      (theorem_10_9_tau_diff_cfNormSq_supported
        h10 hnotation hμ0 hξS hξIrr hξDegree)
      (theorem_10_9_tau_diff_sigma_omega_count_lt_two_card_left_supported
        h10 hnotation hμ0 hξS hξIrr hξDegree)
      (theorem_10_9_tau_diff_sigma_omega_rectangle_relation_supported
        h10 hnotation hμ0 hξS hξIrr hξDegree)
      hbase
  have hnotationData := hnotation
  rcases hnotationData with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  intro ψ hψ
  rcases hω.all_irreducibles ψ hψ with ⟨i, j, rfl⟩
  have hΩ :
      Section1.scalarProduct G (Section4Scratch.omegaColumnSigma σ ω j0)
          (σ (ω i j)) =
        if j = j0 then 1 else 0 := by
    have hright :=
      scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
        hnotation i j j0
    simpa [Section1.scalarProduct_star_swap] using congrArg star hright
  have hY := hcoeff i j
  rw [Section5.scalarProduct_sub_left, hΩ, hY]
  simp

public theorem theorem_10_9_candidate_orthogonal_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (hW1ltW2 : Nat.card W1 < Nat.card W2) :
    orthogonalToSigmaIrreducibles W σ
      (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)) := by
  classical
  have hbase :
      Section1.scalarProduct G (τ (μ0 - ξ)) (σ (ω i0 j0)) = 1 :=
    theorem_10_9_tau_diff_sigma_omega_base_coefficient_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  exact theorem_10_9_candidate_orthogonal_supported_of_base
    h10 hnotation hμ0 hξS hξIrr hξDegree hW1ltW2 hbase

public theorem theorem_10_9_supported_decomposition_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (hW1ltW2 : Nat.card W1 < Nat.card W2) :
    ∃ χ : Section1.ClassFunction G,
      theorem_10_9_decompositionData W j0 ω σ τ μ0 ξ χ := by
  classical
  let χ : Section1.ClassFunction G :=
    Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · dsimp [χ]
    exact theorem_10_9_candidate_decomposition_eq hμ0
  · dsimp [χ]
    exact theorem_10_9_candidate_isVirtualCharacter_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  · dsimp [χ]
    exact theorem_10_9_candidate_orthogonal_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree hW1ltW2
  · dsimp [χ]
    exact theorem_10_9_candidate_cfNormSq_of_orthogonal_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
      (theorem_10_9_candidate_orthogonal_supported
        h10 hnotation hμ0 hξS hξIrr hξDegree hW1ltW2)

/-- The checked core of PF `(10.9)` after orthogonality of the residual has
already been established.  This is the form used in PF `(11.8.4)`, where the
orthogonality is the temporary contradiction hypothesis rather than a
consequence of the degree inequality from PF `(10.9)`. -/
public theorem theorem_10_9_supported_decomposition_of_orthogonal
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {ξ μ0 : Section1.ClassFunction M}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hμ0 : μ0 = muColumn μ j0)
    (hξS : ξ ∈ S)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ))
    (horth :
      orthogonalToSigmaIrreducibles W σ
        (Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ))) :
    ∃ χ : Section1.ClassFunction G,
      theorem_10_9_decompositionData W j0 ω σ τ μ0 ξ χ := by
  classical
  let χ : Section1.ClassFunction G :=
    Section4Scratch.omegaColumnSigma σ ω j0 - τ (μ0 - ξ)
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · dsimp [χ]
    exact theorem_10_9_candidate_decomposition_eq hμ0
  · dsimp [χ]
    exact theorem_10_9_candidate_isVirtualCharacter_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree
  · exact horth
  · dsimp [χ]
    exact theorem_10_9_candidate_cfNormSq_of_orthogonal_supported
      h10 hnotation hμ0 hξS hξIrr hξDegree horth


public theorem theorem_10_10_4_alpha_baseColumn_sub_sOne_scalarProduct_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {ζ : Section1.ClassFunction M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hζ : ζ ∈ S₁)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) (muColumn μ j0 - ζ) =
      -(δ : ℂ) + (n : ℂ) := by
  classical
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) :=
    h43b.2.2.1
  rcases hcount with
    ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
  have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := (hS1irr ζ hζ).1
  have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) := (hS1irr ζ hζ).2
  have hpEq := (typeVReduction_prime_eq_two_mul_card_sub_one hred).1
  have hW1gt : 1 < Nat.card W1 := by
    rcases hred with
      ⟨_hMF, _hTypeV, _hCommon, _hAlt, _hH, _hH', _hCenter, _hH'leH,
        _hW2, _hFrob, _hpprime, _hW2card, _hpOdd, _hW1Odd, hW1gt,
        _hH'card, _hpgroup, _hnoncomm, _hHcard, _hdiv, _hboundRel⟩
    exact hW1gt
  have hpneW1 : (p : ℂ) ≠ (Nat.card W1 : ℂ) := by
    have hpneNat : p ≠ Nat.card W1 := by
      rw [hpEq]
      omega
    exact_mod_cast hpneNat
  have hOneNeW1 : (1 : ℂ) ≠ (Nat.card W1 : ℂ) := by
    have hOneNeNat : (1 : ℕ) ≠ Nat.card W1 := by omega
    exact_mod_cast hOneNeNat
  have hζ_ne_μ : ∀ a b, ζ ≠ μ a b := by
    intro a b hEq
    have hdegEq := congrArg Section1.degree hEq
    by_cases hb : b = j0
    · subst b
      have hbase : Section1.degree (μ a j0) = 1 :=
        baseColumn_degree_one_of_section10FourSixNotationSupportedData hnotation a
      rw [hζdeg, hbase] at hdegEq
      exact hOneNeW1 hdegEq.symm
    · have hdeg : Section1.degree (μ a b) = (p : ℂ) :=
        degree_mu_of_typeV_supported hred h10 hnotation hb
      rw [hζdeg, hdeg] at hdegEq
      exact hpneW1 hdegEq.symm
  have hζμ : ∀ a b, Section1.scalarProduct M ζ (μ a b) = 0 := by
    intro a b
    exact scalarProduct_irreducible_ne hζirr (hμirr a b) (hζ_ne_μ a b)
  have hμζ : ∀ a b, Section1.scalarProduct M (μ a b) ζ = 0 := by
    intro a b
    simpa [Section1.scalarProduct_star_swap] using congrArg star (hζμ a b)
  have hζcol :
      Section1.scalarProduct M ζ (muColumn μ j0) = 0 := by
    unfold muColumn
    have hsum :
        ((∑ p : I, μ p j0 : Section1.ClassFunction M)) =
          fun x => ∑ p : I, μ p j0 x := by
      ext x
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_right]
    simp [hζμ]
  have hα :
      alphaChar μ ζ n δ j0 i0 j =
        μ i0 j + (-(δ : ℂ)) • μ i0 j0 + (-(n : ℂ)) • ζ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hαcol :
      Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) (muColumn μ j0) =
        -(δ : ℂ) := by
    have hentry :
        Section1.scalarProduct M (μ i0 j) (muColumn μ j0) = 0 := by
      simpa [hj] using
        theorem_10_10_4_mu_entry_muColumn_supported hnotation i0 j j0
    have hbase :
        Section1.scalarProduct M (μ i0 j0) (muColumn μ j0) = 1 := by
      simpa using
        theorem_10_10_4_mu_entry_muColumn_supported hnotation i0 j0 j0
    rw [hα]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [hentry, hbase, hζcol]
    ring
  have hαζ :
      Section1.scalarProduct M (alphaChar μ ζ n δ j0 i0 j) ζ =
        -(n : ℂ) := by
    rw [hα]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [hμζ i0 j, hμζ i0 j0, scalarProduct_irreducible_self hζirr]
    ring
  rw [Section5.scalarProduct_sub_right, hαcol, hαζ]
  ring

public theorem theorem_10_10_4_supported_alpha_tau_baseColumn_sub_sOne_scalarProduct_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hζ : ζ ∈ S₁)
    {j : J} (_hj : j ≠ j0) :
    Section1.scalarProduct G
        (τ (alphaChar μ ζ n δ j0 i0 j))
        (τ (muColumn μ j0 - ζ)) =
      -(δ : ℂ) + (n : ℂ) := by
  classical
  have hζS : ζ ∈ S := typeVCharacterCount_sOne_subset _hcount _hζ
  have hζIrr : Section1.IsIrreducibleCharacterOnGroup ζ := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact (hS1irr ζ _hζ).1
  have hζDegree : Section1.degree ζ = (Nat.card W1 : ℂ) := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact (hS1irr ζ _hζ).2
  have hαA0 :
      Section1.supportedOn (alphaChar μ ζ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    typeVAlpha_supportedOn_primeDadeA0_of_typeVCharacterCountData_supported
      _hred _h10 _hcount _hnotation _hζ _hj
  have hdiffA0 :
      Section1.supportedOn (muColumn μ j0 - ζ)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    theorem_10_9_candidate_supportedOn_primeDadeA0_supported
      _h10 _hnotation rfl hζS hζIrr hζDegree
  have hμIrr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        _hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hμIrr i j))
  have hζClass : Section1.IsClassFunction ζ := by
    exact Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζIrr)
  have hαClass :
      Section1.IsClassFunction (alphaChar μ ζ n δ j0 i0 j) := by
    intro x g
    simp [alphaChar, hμClass i0 j x g, hμClass i0 j0 x g, hζClass x g]
  have hcolClass : Section1.IsClassFunction (muColumn μ j0) := by
    intro x g
    unfold muColumn
    simpa using Finset.sum_congr rfl (fun i _hi => hμClass i j0 x g)
  have hdiffClass : Section1.IsClassFunction (muColumn μ j0 - ζ) := by
    intro x g
    simp [hcolClass x g, hζClass x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        _hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  rw [hτiso (alphaChar μ ζ n δ j0 i0 j) (muColumn μ j0 - ζ) hαClass
    hdiffClass hαA0 hdiffA0]
  exact theorem_10_10_4_alpha_baseColumn_sub_sOne_scalarProduct_supported
    _hred _h10 _hcount _hnotation _hζ _hj

public theorem theorem_10_10_4_supported_base_formula_from_notation_count_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (_hred : typeVReductionData M MF H H' W1 W2 p)
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (_hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (_hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (_hζ : ζ ∈ S₁)
    (_halpha : typeVAlphaFormulaData W A0 j0 μ ω σ ζ τ τ₁ n δ)
    {j : J} (_hj : j ≠ j0) :
    τ (muColumn μ j0 - ζ) =
      Section4Scratch.omegaColumnSigma σ ω j0 - τ₁ ζ := by
  classical
  have hζS : ζ ∈ S := typeVCharacterCount_sOne_subset _hcount _hζ
  have hζirr : Section1.IsIrreducibleCharacterOnGroup ζ := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact (hS1irr ζ _hζ).1
  have hζdeg : Section1.degree ζ = (Nat.card W1 : ℂ) := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, hS1irr, _hmu, _hd, _hδ, _hn⟩
    exact (hS1irr ζ _hζ).2
  have hW1ltW2 : Nat.card W1 < Nat.card W2 :=
    (typeVReduction_prime_eq_two_mul_card_sub_one _hred).2
  rcases theorem_10_9_supported_decomposition_source
      (M := M) (MF := MF) (W1 := W1) (W2 := W2)
      (W := W) (A := A) (A0 := A0)
      (S := S) (τ := τ) (i0 := i0) (j0 := j0)
      (μ := μ) (δSign := δSign) (ω := ω) (σ := σ)
      (ξ := ζ) (μ0 := muColumn μ j0)
      _h10 _hnotation rfl hζS hζirr hζdeg hW1ltW2 with
    ⟨χ, hχpack⟩
  rcases hχpack with ⟨hdecomp, _hχvirt, hχorth, hχnorm⟩
  let Ω0 : Section1.ClassFunction G := Section4Scratch.omegaColumnSigma σ ω j0
  let φ : Section1.ClassFunction G := σ (ω i0 j)
  let ψ : Section1.ClassFunction G := σ (ω i0 j0)
  let zη : Section1.ClassFunction G := τ₁ ζ
  have hsourcePair :
      Section1.scalarProduct G
          (τ (alphaChar μ ζ n δ j0 i0 j))
          (τ (muColumn μ j0 - ζ)) =
        -(δ : ℂ) + (n : ℂ) :=
    theorem_10_10_4_supported_alpha_tau_baseColumn_sub_sOne_scalarProduct_source
      _hred _h10 _hnotation _hcount _hζ _hj
  have hpairDecomp :
      Section1.scalarProduct G
          (τ (alphaChar μ ζ n δ j0 i0 j))
          (Ω0 - χ) =
        -(δ : ℂ) + (n : ℂ) := by
    simpa [Ω0, Section4Scratch.omegaColumnSigma, hdecomp] using hsourcePair
  have hαformula :
      τ (alphaChar μ ζ n δ j0 i0 j) =
        (δ : ℂ) • (φ - ψ) - (n : ℂ) • zη := by
    simpa [φ, ψ, zη] using (_halpha i0 j _hj).2
  have hφΩ :
      Section1.scalarProduct G φ Ω0 = 0 := by
    simpa [φ, Ω0, _hj] using
      scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
        _hnotation i0 j j0
  have hψΩ :
      Section1.scalarProduct G ψ Ω0 = 1 := by
    simpa [ψ, Ω0] using
      scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData
        _hnotation i0 j0 j0
  have hφχ : Section1.scalarProduct G φ χ = 0 := by
    have hωirr : Section1.IsIrreducibleCharacterOnGroup (ω i0 j) := by
      rcases _hnotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, _hA0, _h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hω.irreducible i0 j
    have hχφ := hχorth (ω i0 j) hωirr
    simpa [φ, Section1.scalarProduct_star_swap] using congrArg star hχφ
  have hψχ : Section1.scalarProduct G ψ χ = 0 := by
    have hωirr : Section1.IsIrreducibleCharacterOnGroup (ω i0 j0) := by
      rcases _hnotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, _hA0, _h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hω.irreducible i0 j0
    have hχψ := hχorth (ω i0 j0) hωirr
    simpa [ψ, Section1.scalarProduct_star_swap] using congrArg star hχψ
  have hzηΩ : Section1.scalarProduct G zη Ω0 = 0 := by
    unfold Ω0 Section4Scratch.omegaColumnSigma
    have hsum :
        ((∑ i : I, σ (ω i j0) : Section1.ClassFunction G)) =
          fun g => ∑ i : I, σ (ω i j0) g := by
      ext g
      simp
    rw [hsum, Section1.scalarProduct_fintype_sum_right]
    have horth : ∀ i, Section1.scalarProduct G zη (σ (ω i j0)) = 0 := by
      intro i
      exact theorem_10_10_3_tauOne_sOne_orthogonal_sigma_omega_supported
        _hred _h10 _hcount _hnotation _hζ _hτ₁ i j0
    simp [zη, horth]
  have hformulaPair :
      Section1.scalarProduct G
          (τ (alphaChar μ ζ n δ j0 i0 j))
          (Ω0 - χ) =
        -(δ : ℂ) + (n : ℂ) * Section1.scalarProduct G zη χ := by
    rw [hαformula]
    rw [Section5.scalarProduct_sub_left]
    rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
    rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_left]
    rw [hφΩ, hψΩ, hφχ, hψχ, hzηΩ]
    ring
  have hn : n = 2 := by
    rcases _hcount with
      ⟨_hJ, _hdecomp, _hS1card, _hS1irr, _hmu, _hd, _hδ, hn⟩
    exact hn
  have hzηχ : Section1.scalarProduct G zη χ = 1 := by
    have heq :
        -(δ : ℂ) + (n : ℂ) * Section1.scalarProduct G zη χ =
          -(δ : ℂ) + (n : ℂ) := by
      exact hformulaPair.symm.trans hpairDecomp
    rw [hn] at heq
    have hmul :
        (2 : ℂ) * Section1.scalarProduct G zη χ = (2 : ℂ) * 1 := by
      simpa using add_left_cancel heq
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    exact mul_left_cancel₀ htwo hmul
  have hχzη : Section1.scalarProduct G χ zη = 1 := by
    simpa [zη, Section1.scalarProduct_star_swap] using congrArg star hzηχ
  have hzηself : Section1.scalarProduct G zη zη = 1 := by
    have hgram :=
      theorem_10_10_4_tauOne_sOne_gram _hτ₁
        (⟨ζ, _hζ⟩ : S₁) (⟨ζ, _hζ⟩ : S₁)
    simpa [zη, scalarProduct_irreducible_self hζirr] using hgram
  have hzηnorm : Section5.cfNormSq zη = 1 := by
    unfold Section5.cfNormSq
    rw [hzηself]
    norm_num
  have hnormEq : Section5.cfNormSq χ = Section5.cfNormSq zη := by
    rw [hχnorm, hzηnorm]
  have hdiffRight : Section1.scalarProduct G (χ - zη) zη = 0 := by
    rw [Section5.scalarProduct_sub_left, hχzη, hzηself]
    ring
  have hdiffLeft : Section1.scalarProduct G zη (χ - zη) = 0 := by
    rw [Section5.scalarProduct_sub_right, hzηχ, hzηself]
    ring
  have hχeq : χ = zη :=
    classFunction_eq_of_norm_eq_and_sub_orthogonal hnormEq hdiffRight hdiffLeft
  calc
    τ (muColumn μ j0 - ζ) = Ω0 - χ := by
      simpa [Ω0, Section4Scratch.omegaColumnSigma] using hdecomp
    _ = Section4Scratch.omegaColumnSigma σ ω j0 - τ₁ ζ := by
      rw [hχeq]

public theorem theorem_10_10_4_supported_nonbase_formula_from_notation_count_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    {τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction M}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ)
    (hτ₁ : typeVCoherentSubfamilyData M S₁ τ τ₁)
    (hζ : ζ ∈ S₁) :
    ∀ j : J, j ≠ j0 →
      τ (muColumn μ j - (d : ℂ) • ζ) =
        (δ : ℂ) • Section4Scratch.omegaColumnSigma σ ω j -
          (d : ℂ) • τ₁ ζ := by
  intro j hj
  have hμcol : ∀ j : J, (fun j => muColumn μ j) j = muColumn μ j := by
    intro j
    rfl
  have halpha :
      typeVAlphaFormulaData W A0 j0 μ ω σ ζ τ τ₁ n δ :=
    theorem_10_10_4_supported_alpha_formula_from_notation_count_source
      hred h10 hnotation hcount hτ₁ hζ
  have hbase :
      τ ((fun j : J => muColumn μ j) j0 - ζ) =
        Section4Scratch.omegaColumnSigma σ ω j0 - τ₁ ζ := by
    simpa using
      theorem_10_10_4_supported_base_formula_from_notation_count_source
        hred h10 hnotation hcount hτ₁ hζ halpha hj
  exact theorem_10_10_4_nonbase_formula_from_base_and_alpha_supported
    hred h10 hcount hnotation hμcol hbase halpha hj

public theorem theorem_10_10_4_supported_image_family_from_notation_count_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF H H' W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S S₁ : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {p d n : ℕ}
    {δ : ℤ}
    (hred : typeVReductionData M MF H H' W1 W2 p)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (hcount : typeVCharacterCountData M S S₁ W1 j0
      (fun j => muColumn μ j) p d n δ) :
    ∃ img : S → Section1.ClassFunction G,
      (∀ η : S, IsVirtualCharacter (img η)) ∧
        (∀ η ξ : S,
          Section1.scalarProduct G (img η) (img ξ) =
            Section1.scalarProduct M (η : Section1.ClassFunction M)
              (ξ : Section1.ClassFunction M)) ∧
        (∀ Tnew : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          (∀ η : S, Tnew (η : Section1.ClassFunction M) = img η) →
            Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ Tnew) := by
  have hcoh : Section6.coherentFamily S₁ τ :=
    typeVCharacterCount_coherentFamily_of_hypothesis_10_1_supported_data
      hred h10 hcount
  rcases exists_typeVCoherentSubfamilyData_of_coherentFamily hcoh with
    ⟨τ₁, hτ₁⟩
  rcases typeVCharacterCount_sOne_nonempty hred hcount with ⟨ζ, hζ⟩
  exact theorem_10_10_4_image_family_from_supported_notation_bridge
    (M := M) (MF := MF) (H := H) (H' := H') (W1 := W1) (W2 := W2)
    (W := W) (A := A) (A0 := A0) (S := S) (S₁ := S₁) (τ := τ)
    (τ₁ := τ₁) (ζ := ζ) (i0 := i0) (j0 := j0) (μ := μ)
    (μcol := fun j => muColumn μ j) (δSign := δSign) (ω := ω) (σ := σ)
    (p := p) (d := d) (n := n) (δ := δ)
    hred h10 hcount hnotation (by intro j; rfl) hτ₁ hζ
    (theorem_10_10_4_supported_nonbase_formula_from_notation_count_source
      hred h10 hnotation hcount hτ₁ hζ)

public theorem theorem_10_10_4_coherence_from_image_family_of_hypothesis52
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h52 : Section5.hypothesis_5_2_statement S τ)
    (himage : ∃ img : S → Section1.ClassFunction G,
      (∀ η : S, IsVirtualCharacter (img η)) ∧
        (∀ η ξ : S,
          Section1.scalarProduct G (img η) (img ξ) =
            Section1.scalarProduct M (η : Section1.ClassFunction M)
              (ξ : Section1.ClassFunction M)) ∧
        (∀ Tnew : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          (∀ η : S, Tnew (η : Section1.ClassFunction M) = img η) →
            Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ Tnew)) :
    Section6.coherentFamily S τ := by
  classical
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  rcases himage with ⟨img, himg_virt, hgram, hagree⟩
  have hself_ne_zero :
      ∀ η : S,
        Section1.scalarProduct M (η : Section1.ClassFunction M)
          (η : Section1.ClassFunction M) ≠ 0 := by
    intro η hzero
    have hself :
        Section1.scalarProduct M (η : Section1.ClassFunction M)
            (η : Section1.ClassFunction M) =
          (Section5.cfNormSq (η : Section1.ClassFunction M) : ℂ) :=
      Section5.scalarProduct_self_eq_cfNormSq_of_character (hsetup.2 η)
    have hcf_complex :
        (Section5.cfNormSq (η : Section1.ClassFunction M) : ℂ) = 0 := by
      simpa [hself] using hzero
    have hcf : Section5.cfNormSq (η : Section1.ClassFunction M) = 0 := by
      exact_mod_cast hcf_complex
    have hηzero : (η : Section1.ClassFunction M) = 0 :=
      Section5.cfNormSq_eq_zero hcf
    exact (h52a η).2 (by
      ext g
      simp [hηzero, Section1.conjugateCharacter])
  rcases Section5.exists_extension_fields_of_image_family_pf57
      S τ img h52c hself_ne_zero himg_virt hgram hagree with
    ⟨Tnew, hIso, hVirt, hAgree⟩
  have hsrc : Section5.sourceVirtualCharacters S := by
    intro ψ hψ
    exact Section5.isVirtualCharacter_of_isCharacter
      (hsetup.2 ⟨ψ, hψ⟩)
  have hnonempty : Section5.integerSpanOnNonempty S Section5.puncturedSet := by
    rcases hsetup.1 with ⟨χ, hχ⟩
    exact Section5.integerSpanOnNonempty_of_conjugate_pair hχ
      (h52a ⟨χ, hχ⟩).1 (h52a ⟨χ, hχ⟩).2
      (hsetup.2 ⟨χ, hχ⟩)
  exact ⟨hsrc, hnonempty, Tnew, hIso, hVirt, hAgree⟩


public theorem theorem_10_10_4_supported_image_family_source
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hred : typeVReductionData M MF H H' W1 W2 p) :
    ∃ img : S → Section1.ClassFunction G,
      (∀ η : S, IsVirtualCharacter (img η)) ∧
        (∀ η ξ : S,
          Section1.scalarProduct G (img η) (img ξ) =
            Section1.scalarProduct M (η : Section1.ClassFunction M)
              (ξ : Section1.ClassFunction M)) ∧
        (∀ Tnew : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
          (∀ η : S, Tnew (η : Section1.ClassFunction M) = img η) →
            Section5.agreesOnIntegerSpanOn S Section5.puncturedSet τ Tnew) := by
  rcases theorem_10_10_4_supported_notation_count_package_bridge
      _hred _h10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign, ω, σ,
      S₁, d, n, δ, hnotation, hcount⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  exact theorem_10_10_4_supported_image_family_from_notation_count_source
    (M := M) (MF := MF) (H := H) (H' := H') (W1 := W1) (W2 := W2)
    (W := W) (A := A) (A0 := A0) (S := S) (S₁ := S₁) (τ := τ)
    (i0 := i0) (j0 := j0) (μ := μ) (δSign := δSign) (ω := ω) (σ := σ)
    (p := p) (d := d) (n := n) (δ := δ)
    _hred _h10 hnotation hcount

public theorem theorem_10_10_no_typeVReduction_of_hypothesis_10_1_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF H H' W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : ℕ}
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hred : typeVReductionData M MF H H' W1 W2 p) :
    False := by
  have hcoh : Section6.coherentFamily S τ :=
    theorem_10_10_4_coherence_from_image_family_of_hypothesis52
      (hypothesis_5_2_of_hypothesis_10_1_supported_data h10)
      (theorem_10_10_4_supported_image_family_source h10 hred)
  exact theorem_10_8_supported M MF W1 W2 (section16HatW W1 W2) S τ h10 hcoh

public theorem theorem_10_10_source_typeV_structural_hypothesis_10_1_fields
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF)) :
    typeIIIIVVData M MF W1 W2 (section16HatW W1 W2) ∧
      W1 ≤ M ∧ W2 ≤ M ∧ (W1 ⊔ W2) ≤ M := by
  have hType : typeIIIIVVData M MF W1 W2 (section16HatW W1 W2) := by
    refine ⟨rfl, ⟨⊥, hP, ?_⟩⟩
    exact Or.inr (Or.inr ⟨rfl, hAlt⟩)
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hCompM, _hUle, _hUnil,
      _hW1norm, _hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, hW2leMFSecond, _hW2cyc, _hW2ne, _hCentralizer,
      _hNormalizer⟩
  rcases hMF with ⟨hMFnil, _hMFmax⟩
  rcases hMFnil with ⟨hMFleM, _hMFnorm, _hMFnil, _hMFhall⟩
  rcases hW1Hall with ⟨hW1leM, _hW1hall⟩
  have hW2leMF : W2 ≤ MF := (le_inf_iff.mp hW2leMFSecond).1
  have hW2leM : W2 ≤ M := hW2leMF.trans hMFleM
  exact ⟨hType, hW1leM, hW2leM, sup_le hW1leM hW2leM⟩

public theorem theorem_10_10_typeP_bot_mf_eq_derived
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2) :
    MF = ambientDerivedSubgroup M := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hCompM, _hUle, _hUnil,
      _hW1norm, hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, _hW2leMFSecond, _hW2cyc, _hW2ne, _hCentralizer,
      _hNormalizer⟩
  simpa using hCompD.2.2.1.symm

public theorem theorem_10_10_section8CentralizerUnion_derived_mf_eq
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2) :
    Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF =
      section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
  classical
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  ext y
  constructor
  · rintro ⟨_x, _hxMF, hyCent⟩
    rcases hyCent with ⟨hyCent, hyne⟩
    exact ⟨hyCent.1, hyne⟩
  · intro hyD
    refine ⟨y, ?_, ?_⟩
    · simpa [hMF_eq_D] using hyD
    · refine ⟨?_, hyD.2⟩
      change y ∈ elementCentralizerIn (ambientDerivedSubgroup M) y
      rw [elementCentralizerIn]
      refine ⟨hyD.1, ?_⟩
      simp [Subgroup.mem_centralizer_iff]

public theorem theorem_10_10_typeP_bot_complement_eq_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hPbot : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hcomp : section12ComplementIn (ambientDerivedSubgroup M) MF U) :
    U = ⊥ := by
  rcases hcomp with ⟨_hMFleD, hUleD, _hDsup, hdisj⟩
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hPbot
  apply le_antisymm ?_ bot_le
  intro x hxU
  have hxMF : x ∈ MF := by
    simpa [hMF_eq_D] using hUleD hxU
  exact hdisj.le_bot ⟨hxMF, hxU⟩

public theorem theorem_10_10_not_typeII_of_typeP_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hPbot : Section8.typePDefinitionData M MF ⊥ W1 W2) :
    ¬ Section8.typeIIDefinitionData M MF := by
  rintro ⟨U, W1', _W2', _U1, _U0, hP, hExtra, _hUcomm, _hUnorm, _hF⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact hExtra.1 (theorem_10_10_typeP_bot_complement_eq_bot hPbot hCompMFU)

public theorem theorem_10_10_not_typeIII_of_typeP_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hPbot : Section8.typePDefinitionData M MF ⊥ W1 W2) :
    ¬ Section8.typeIIIDefinitionData M MF := by
  rintro ⟨U, W1', _W2', hP, hExtra, _hUcomm, _hUnorm⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact hExtra.1 (theorem_10_10_typeP_bot_complement_eq_bot hPbot hCompMFU)

public theorem theorem_10_10_not_typeIV_of_typeP_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hPbot : Section8.typePDefinitionData M MF ⊥ W1 W2) :
    ¬ Section8.typeIVDefinitionData M MF := by
  rintro ⟨U, W1', _W2', hP, hExtra, _hUncomm, _hUnorm⟩
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hW1comp, _hUleD, _hUnil,
      _hW1norm, hCompMFU, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hHatW⟩
  exact hExtra.1 (theorem_10_10_typeP_bot_complement_eq_bot hPbot hCompMFU)

public theorem theorem_10_10_exists_notation_8_10_source_data_of_typeV_exclusive
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hnotI : ¬ Section8.typeIDefinitionData M MF)
    (hnotII : ¬ Section8.typeIIDefinitionData M MF)
    (hnotIII : ¬ Section8.typeIIIDefinitionData M MF)
    (hnotIV : ¬ Section8.typeIVDefinitionData M MF) :
    ∃ Ms : Subgroup G, ∃ A A0 A1 : Set G,
      Section8.notation_8_10_source_data M MF Ms A A0 A1 ∧
        Ms = MF ∧
          A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
            A = A1 ∧
              A0 =
                A ∪ section16ConjugatesOfSetBySet
                  (section16HatW W1 W2) (M : Set G) := by
  classical
  let Ms : Subgroup G := MF
  let A1 : Set G := section16NonidentityElements (ambientDerivedSubgroup M : Set G)
  let A : Set G := Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms
  let A0 : Set G := A ∪ section16ConjugatesOfSetBySet
    (section16HatW W1 W2) (M : Set G)
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  have hMF : section16MFSubgroup M MF := hP.1
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hAeq :
      Section8.section8CentralizerUnion (ambientDerivedSubgroup M) MF =
        section16NonidentityElements (ambientDerivedSubgroup M : Set G) :=
    theorem_10_10_section8CentralizerUnion_derived_mf_eq hP
  have hMsChoice : Section8.msChoiceSource M MF Ms := by
    refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    exact ⟨hnotI, hnotII, hnotIII, hnotIV, hTypeV, rfl⟩
  have hA1 : A1 = Section8.a1Set Ms := by
    simp [A1, Ms, Section8.a1Set, hMF_eq_D]
  have hA_A1 : A = A1 := by
    simpa [A, A1, Ms] using hAeq
  refine ⟨Ms, A, A0, A1, ?_, rfl, rfl, hA_A1, rfl⟩
  refine ⟨hM, hMF, hMsChoice, hA1, Or.inr ?_⟩
  refine ⟨⊥, W1, W2, hP, Or.inr (Or.inr (Or.inr hTypeV)), rfl, rfl, ?_⟩
  intro _hLate
  exact ⟨rfl, hA_A1⟩

public theorem theorem_10_10_exists_notation_8_10_source_data_of_typeV_not_typeI
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hnotI : ¬ Section8.typeIDefinitionData M MF) :
    ∃ Ms : Subgroup G, ∃ A A0 A1 : Set G,
      Section8.notation_8_10_source_data M MF Ms A A0 A1 ∧
        Ms = MF ∧
          A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
            A = A1 ∧
              A0 =
                A ∪ section16ConjugatesOfSetBySet
                  (section16HatW W1 W2) (M : Set G) :=
  theorem_10_10_exists_notation_8_10_source_data_of_typeV_exclusive
    hM hP hAlt hnotI
    (theorem_10_10_not_typeII_of_typeP_bot hP)
    (theorem_10_10_not_typeIII_of_typeP_bot hP)
    (theorem_10_10_not_typeIV_of_typeP_bot hP)

public theorem theorem_10_10_exists_derivedInducedFamily
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    ∃ S : Finset (Section1.ClassFunction M), derivedInducedFamily M S := by
  classical
  rcases exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := derivedSubgroup M) with
    ⟨ι, hι, χrep, hχrep, _hsum⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let χ : ι → Section1.ClassFunction (derivedSubgroup M) :=
    fun i => Section1.ofConjClassFunction (χrep i)
  let S : Finset (Section1.ClassFunction M) :=
    (Finset.univ.filter fun i => χ i ≠
      Section1.principalCharacter (derivedSubgroup M)).image
        (fun i => Section1.inducedCF (derivedSubgroup M) (χ i))
  have hχirr :
      ∀ i, Section1.IsIrreducibleCharacterOnGroup (χ i) := by
    intro i
    exact ofConjClassFunction_isIrreducibleCharacterOnGroup_sec10 (hχrep.1 i)
  have hχcomplete :
      ∀ θ : Section1.ClassFunction (derivedSubgroup M),
        Section1.IsIrreducibleCharacterOnGroup θ → ∃ i, χ i = θ := by
    intro θ hθirr
    let θrep : ConjClassFunction (derivedSubgroup M) :=
      Section1.toConjClassFunction θ
        (isClassFunction_of_irreducibleCharacterOnGroup_sec10 hθirr)
    have hθrepirr : IsIrreducibleConjCharacter θrep :=
      toConjClassFunction_isIrreducibleCharacter_of_onGroup_sec10 hθirr
    rcases hχrep.2.1 θrep hθrepirr with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext g
    change χrep i (ConjClasses.mk g) = θ g
    rw [hi]
    rfl
  refine ⟨S, ?_⟩
  intro ψ
  constructor
  · intro hψ
    rcases Finset.mem_image.mp hψ with ⟨i, hi, rfl⟩
    have hne : χ i ≠ Section1.principalCharacter (derivedSubgroup M) := by
      exact (Finset.mem_filter.mp hi).2
    exact ⟨χ i, hχirr i, hne, rfl⟩
  · rintro ⟨θ, hθirr, hθne, rfl⟩
    rcases hχcomplete θ hθirr with ⟨i, hi⟩
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, by simpa only [hi] using hθne⟩
    · simp only [hi]

public theorem theorem_10_10_inducedKernelFamily_bot_of_derivedInducedFamily
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : derivedInducedFamily M S) :
    Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S := by
  refine ⟨bot_le, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
    refine ⟨θ, hθirr, ?_, hθne, hχeq⟩
    intro a
    have haM :
        (((a : (⊥ : Subgroup M).subgroupOf (derivedSubgroup M)) :
          derivedSubgroup M) : M) = 1 := by
      have hmem :
          (((a : (⊥ : Subgroup M).subgroupOf (derivedSubgroup M)) :
            derivedSubgroup M) : M) ∈ (⊥ : Subgroup M) :=
        Subgroup.mem_subgroupOf.mp a.2
      simpa using hmem
    have haD : (a : derivedSubgroup M) = 1 := Subtype.ext haM
    simp [Section1.degree, haD]
  · intro hχ
    rcases hχ with ⟨θ, hθirr, _hθker, hθne, hχeq⟩
    exact (hS χ).mpr ⟨θ, hθirr, hθne, hχeq⟩

public theorem theorem_10_10_section8InducedNonkernelFamily_of_typeP_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hS : derivedInducedFamily M S) :
    Section8.section8InducedNonkernelFamily M MF S := by
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    theorem_10_10_inducedKernelFamily_bot_of_derivedInducedFamily hS
  have hSnonempty : S.Nonempty := by
    rcases Section6.inducedKernelFamily_nonempty_of_solvable_proper
        (typePDefinitionData_derivedSubgroup_solvable hP)
        (by infer_instance : (⊥ : Subgroup M).Normal)
        (lt_of_le_of_lt bot_le
          (typePDefinitionData_secondDerived_lt_derivedSubgroup hP))
        hSbot with
      ⟨χ, hχ⟩
    exact ⟨χ, hχ⟩
  have hSclosed :
      ∀ χ : Section1.ClassFunction M, χ ∈ S →
        Section1.conjugateCharacter χ ∈ S :=
    Section6.inducedKernelFamily_conjugate_closed hSbot
  refine ⟨hSnonempty, hSclosed, ?_⟩
  intro χ hχ
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθne, hχeq⟩
  refine ⟨θ, hθirr, ?_, hχeq⟩
  intro hker
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hkerTop : Section1.subgroupInKernel' θ ⊤ := by
    intro x
    have hxD : (((x : (⊤ : Subgroup (derivedSubgroup M))) :
          derivedSubgroup M) : M) ∈ derivedSubgroup M :=
      (x : derivedSubgroup M).property
    have hxAmb :
        ((((x : (⊤ : Subgroup (derivedSubgroup M))) :
          derivedSubgroup M) : M) : G) ∈ ambientDerivedSubgroup M := by
      change ((((x : (⊤ : Subgroup (derivedSubgroup M))) :
          derivedSubgroup M) : M) : G) ∈
        (derivedSubgroup M).map M.subtype
      exact Subgroup.mem_map_of_mem M.subtype hxD
    exact hker (x : derivedSubgroup M) (by simpa [hMF_eq_D] using hxAmb)
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10 hθirr
  exact hθne
    (eq_principalCharacter_of_isBookIrreducibleCharacter_subgroupInKernel_top_sec10
      θ hθbook hkerTop)

public theorem theorem_10_10_ms_eq_mf_of_typeV_notation
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hTypeV : Section8.typeVDefinitionData M MF) :
    Ms = MF := by
  rcases hNotation with ⟨_hM, _hMF, hMs, _hA1, _hcase⟩
  rcases hMs with hI | hII | hIII | hIV | hV
  · rcases hI with ⟨_hI, _hnotII, _hnotIII, _hnotIV, hnotV, _hMs⟩
    exact (hnotV hTypeV).elim
  · rcases hII with ⟨_hnotI, _hII, _hnotIII, _hnotIV, hnotV, _hMs⟩
    exact (hnotV hTypeV).elim
  · rcases hIII with ⟨_hnotI, _hnotII, _hIII, _hnotIV, hnotV, _hMs⟩
    exact (hnotV hTypeV).elim
  · rcases hIV with ⟨_hnotI, _hnotII, _hnotIII, _hIV, hnotV, _hMs⟩
    exact (hnotV hTypeV).elim
  · rcases hV with ⟨_hnotI, _hnotII, _hnotIII, _hnotIV, _hV, hMs⟩
    exact hMs


public theorem theorem_10_10_hypothesis_10_1_supported_of_typeV_source_context
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hFamily : derivedInducedFamily M S)
    (hDade : dadeIsometryRelativeToA0SupportedSourceData M MF τ)
    (h46 :
      ∃ Apre : Set M,
        Section4Scratch.hypothesis_4_6_statement
          (derivedSubgroup M)
          (W1.subgroupOf M)
          (W2.subgroupOf M)
          ((W1 ⊔ W2).subgroupOf M)
          (derivedSubgroup M)
          Apre)
    (hNotation10 :
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
    (h52 : Section5.hypothesis_5_2_statement S τ) :
    hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ := by
  rcases theorem_10_10_source_typeV_structural_hypothesis_10_1_fields
      hP hAlt with ⟨hType, hW1M, hW2M, hW12M⟩
  exact ⟨hM, hType, hFamily, hW1M, hW2M, hW12M, hDade, h46,
    hNotation10, h52⟩

public theorem theorem_10_10_subgroupImagePuncturedSet_derived_eq_ambientDerived
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    Section6.subgroupImagePuncturedSet M (derivedSubgroup M) =
      section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
  have hD_le_M : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hDmap : (derivedSubgroup M).map M.subtype = ambientDerivedSubgroup M := by
    calc
      (derivedSubgroup M).map M.subtype =
          ((ambientDerivedSubgroup M).subgroupOf M).map M.subtype := by
            rw [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
      _ = ambientDerivedSubgroup M ⊓ M :=
          Subgroup.subgroupOf_map_subtype (H := ambientDerivedSubgroup M) (K := M)
      _ = ambientDerivedSubgroup M := inf_eq_left.2 hD_le_M
  rw [Section6.theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured, hDmap]
  ext x
  rfl

public theorem theorem_10_10_typeV_ti_subgroupImagePuncturedSet
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hTI : section16TISubset (section16NonidentityElements (MF : Set G))) :
    Section2.IsTISubsetWithNormalizer
      (Section6.subgroupImagePuncturedSet M (derivedSubgroup M)) M := by
  classical
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hTI_D :
      section16TISubset
        (section16NonidentityElements (ambientDerivedSubgroup M : Set G)) := by
    simpa [hMF_eq_D] using hTI
  have hD_le_M : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hDmap : (derivedSubgroup M).map M.subtype = ambientDerivedSubgroup M := by
    calc
      (derivedSubgroup M).map M.subtype =
          ((ambientDerivedSubgroup M).subgroupOf M).map M.subtype := by
            rw [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
      _ = ambientDerivedSubgroup M ⊓ M :=
          Subgroup.subgroupOf_map_subtype (H := ambientDerivedSubgroup M) (K := M)
      _ = ambientDerivedSubgroup M := inf_eq_left.2 hD_le_M
  have hD_sub_norm : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    rw [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
    infer_instance
  have hD_ne : (ambientDerivedSubgroup M).subgroupOf M ≠ ⊥ := by
    have hlt : (section16SecondDerivedSubgroup M).subgroupOf M < derivedSubgroup M :=
      typePDefinitionData_secondDerived_lt_derivedSubgroup hP
    intro hbot
    rw [← section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)] at hlt
    rw [hbot] at hlt
    exact (not_lt_of_ge bot_le) hlt
  have hD_ne_ambient : ambientDerivedSubgroup M ≠ (⊥ : Subgroup G) := by
    intro hbot
    apply hD_ne
    ext x
    constructor
    · intro hx
      have hxG : (x : G) ∈ ambientDerivedSubgroup M := hx
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hbot] using hxG
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxBot))
    · intro hx
      have hxone : x = 1 := Subgroup.mem_bot.mp hx
      simp [hxone]
  have hMmax8 : M ∈ section8MaximalSubgroups G :=
    section8_maximal_of_section9_maximal (G := G) hM
  have hNormD : Subgroup.normalizer ((ambientDerivedSubgroup M : Set G)) = M :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      (G := G) hMmax8 hD_le_M hD_ne_ambient hD_sub_norm
  have hAeq :
      Section6.subgroupImagePuncturedSet M (derivedSubgroup M) =
        section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
    exact theorem_10_10_subgroupImagePuncturedSet_derived_eq_ambientDerived M
  have hDsharpNonempty :
      (section16NonidentityElements (ambientDerivedSubgroup M : Set G)).Nonempty := by
    by_contra hEmpty
    apply hD_ne_ambient
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxD
    by_contra hxne
    exact hEmpty ⟨x, ⟨hxD, hxne⟩⟩
  have hNormalizer :
      Section2.setNormalizer
          (Section6.subgroupImagePuncturedSet M (derivedSubgroup M)) = M := by
    calc
      Section2.setNormalizer
          (Section6.subgroupImagePuncturedSet M (derivedSubgroup M)) =
          Subgroup.normalizer (((derivedSubgroup M).map M.subtype : Subgroup G) : Set G) := by
            rw [Section6.theorem_6_8_normalizer_map_subtype_eq_setNormalizer_punctured]
      _ = Subgroup.normalizer ((ambientDerivedSubgroup M : Set G)) := by rw [hDmap]
      _ = M := hNormD
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hAeq]
    exact hDsharpNonempty
  · intro a ha
    have haD : a ∈ section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
      rw [← hAeq]
      exact ha
    exact haD.2
  · intro g hg
    have hg16 :
        (section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∩
            section16ConjugateSet
              (section16NonidentityElements (ambientDerivedSubgroup M : Set G)) g).Nonempty := by
      rcases hg with ⟨x, hxA, hxConj⟩
      refine ⟨x, ?_⟩
      constructor
      · rw [← hAeq]
        exact hxA
      · rcases hxConj with ⟨y, hyA, hyx⟩
        exact ⟨y, by rw [← hAeq]; exact hyA, by simpa [Section2.conjBy] using hyx⟩
    rcases hTI_D g with hEq | hSub
    · change Section2.normalizesSet
        (Section6.subgroupImagePuncturedSet M (derivedSubgroup M)) g
      intro x
      rw [hAeq, Section2.conjBy]
      constructor
      · intro hx
        have hxConj :
            g * x * g⁻¹ ∈ section16ConjugateSet
              (section16NonidentityElements (ambientDerivedSubgroup M : Set G)) g := by
          simpa [hEq] using hx
        rcases hxConj with ⟨y, hySharp, hyx⟩
        have hxy : x = y := by
          have h := congrArg (fun z : G => g⁻¹ * z * g) hyx
          simpa [mul_assoc] using h
        simpa [hxy] using hySharp
      · intro hx
        have hxConj :
            g * x * g⁻¹ ∈
              section16ConjugateSet
                (section16NonidentityElements (ambientDerivedSubgroup M : Set G)) g :=
          ⟨x, hx, rfl⟩
        simpa [hEq] using hxConj
    · exfalso
      rcases hg16 with ⟨x, hx⟩
      have hxone : x = 1 := hSub hx
      exact hx.1.2 hxone
  · exact hNormalizer

public theorem theorem_10_10_not_typeI_of_msChoiceSource_typeV
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    (hMs : Section8.msChoiceSource M MF Ms)
    (hTypeV : Section8.typeVDefinitionData M MF) :
    ¬ Section8.typeIDefinitionData M MF := by
  intro hTypeI
  rcases hMs with hI | hII | hIII | hIV | hV
  · exact hI.2.2.2.2.1 hTypeV
  · exact hII.1 hTypeI
  · exact hIII.1 hTypeI
  · exact hIV.1 hTypeI
  · exact hV.1 hTypeI

public theorem theorem_10_10_transformAgreesWithInductionOn_of_typeV_ti_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hTI : section16TISubset (section16NonidentityElements (MF : Set G)))
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    Section6.transformAgreesWithInductionOn M S τ := by
  classical
  intro χ hχ
  rcases h10 with
    ⟨hM, _hType, hS, _hW1M, _hW2M, _hW12M, hDade, _h46, _hNotation10, _h52⟩
  rcases hDade with ⟨Ms, A, A0, A1, R, hNotation, hA0M, hτeq⟩
  let Aimg : Set G := Section6.subgroupImagePuncturedSet M (derivedSubgroup M)
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, Or.inl hTI⟩
  have hAeq :
      Aimg = section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
    exact theorem_10_10_subgroupImagePuncturedSet_derived_eq_ambientDerived M
  have hAimgA0 : Aimg ⊆ A0 := by
    intro a ha
    rcases hNotation with
      ⟨_hM, _hMF, hMs, _hA1, hCases⟩
    rcases hCases with hI | hPcase
    · rcases hI with ⟨hTypeI, _hA, _hA0⟩
      exact (theorem_10_10_not_typeI_of_msChoiceSource_typeV hMs hTypeV
        hTypeI).elim
    · rcases hPcase with
        ⟨_U, _W1, _W2, _hPsource, _hTypes, _hA, hA0, hLate⟩
      have hlate := hLate (Or.inr (Or.inr hTypeV))
      rw [hA0]
      exact Or.inl (by
        rw [hlate.2, hlate.1, ← hAeq]
        exact ha)
  have hχAimg : Section2.CFOn M Aimg χ := by
    have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
      theorem_10_10_inducedKernelFamily_bot_of_derivedInducedFamily hS
    simpa [Aimg] using
      Section6.theorem_6_8_CFOn_subgroupImagePuncturedSet_of_integerSpanOn
        (L := M) (H := derivedSubgroup M) hSbot hχ
  have hχA0 : Section2.CFOn M A0 χ :=
    Section2.CFOn_mono hAimgA0 hχAimg
  have hHyp2triv : Section2.Hypothesis2 Aimg M (fun _ : G => ⊥) := by
    have hTI68 :
        Section2.IsTISubsetWithNormalizer Aimg M := by
      simpa [Aimg] using
        theorem_10_10_typeV_ti_subgroupImagePuncturedSet hM hP hTI
    exact (Section2.proposition_2_3 Aimg M hTI68.1).mp hTI68
  have hconst :
      ∀ ψ : ConjClassFunction G,
        IsIrreducibleConjCharacter ψ →
          ∀ ⦃a h0 : G⦄, a ∈ Aimg → h0 ∈ R a →
            Section1.ofConjClassFunction ψ (a * h0) =
              Section1.ofConjClassFunction ψ a := by
    intro ψ _hψ a h0 ha hh0
    have hcent_le_M : Section2.elementCentralizer a ≤ M := by
      intro c hc
      have hprod0 := hHyp2triv.centralizer_eq_product ha
      rcases hprod0.mul_surjective c hc with ⟨z, hz, k, hk, hck⟩
      have hz1 : z = 1 := by simpa using hz
      subst z
      have hkM : k ∈ M := (Subgroup.mem_inf.mp hk).1
      simpa [hck] using hkM
    have hprod := hA0M.centralizer_eq_product (hAimgA0 ha)
    have hRa_bot : R a = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxR
      have hxCent : x ∈ Section2.elementCentralizer a := hprod.left_le hxR
      have hxM : x ∈ M := hcent_le_M hxCent
      have hxInf : x ∈ R a ⊓ Section2.centralizerIn M a :=
        ⟨hxR, ⟨hxM, hxCent⟩⟩
      simpa [hprod.inf_eq_bot] using hxInf
    have hh0bot : h0 ∈ (⊥ : Subgroup G) := by
      simpa [hRa_bot] using hh0
    have hh0one : h0 = 1 := Subgroup.mem_bot.mp hh0bot
    simp [hh0one]
  have hdade :
      Section2.dadeTransform R hA0M.subset_L χ = Section1.inducedCF M χ :=
    Section2.dadeTransform_eq_inducedCF_of_coset_constancy_on_support
      A0 Aimg M R hAimgA0 hA0M hA0M.subset_L χ hχAimg hconst
  calc
    τ χ = Section2.dadeTransform R hA0M.subset_L χ := hτeq χ hχA0
    _ = Section1.inducedCF M χ := hdade


public theorem theorem_10_10_inducedFromNonkernelFamily_of_section8
    {G : Type u}
    [Group G]
    [Finite G]
    {M Ms : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : Section8.section8InducedNonkernelFamily M Ms S) :
    Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup M) (Ms.subgroupOf M) S := by
  intro χ hχ
  rcases hS.2.2 χ hχ with ⟨θ, hθirr, hθnonker, hχeq⟩
  refine ⟨θ, hθirr, ?_, hχeq⟩
  intro hker
  apply hθnonker
  intro m hmMs
  let a : (Ms.subgroupOf M).subgroupOf (derivedSubgroup M) :=
    ⟨m, by
      change ((m : M) : G) ∈ Ms
      exact hmMs⟩
  have ha := hker a
  simpa [a, Section1.subgroupInKernel', Section1.degree] using ha

public theorem theorem_10_10_hypothesis52_a_of_section8InducedNonkernelFamily
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M Ms : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : Section8.section8InducedNonkernelFamily M Ms S) :
    Section5.hypothesis_5_2_a_statement S := by
  classical
  have hModd : Odd (Nat.card M) :=
    Odd.of_dvd_nat IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  intro X
  constructor
  · exact hS.2.1 (X : Section1.ClassFunction M) X.2
  · intro hreal
    rcases hS.2.2 (X : Section1.ClassFunction M) X.2 with
      ⟨θ, hθirr, hθnonker, hXeq⟩
    rcases hθirr with ⟨n, ρ, hρirr, hθeq⟩
    have hθne' :
        ρ.character ≠ Section1.principalCharacter (derivedSubgroup M) := by
      intro hprin
      apply hθnonker
      intro m hmMs
      rw [hθeq, hprin]
      simp [Section1.principalCharacter]
    have horth :=
      Section1.proposition_1_5_e_rep_dual_orbit_relIndex_canonical
        (derivedSubgroup M) ρ hModd hρirr hθne'
    have horth0 :
        Section1.scalarProduct M
          (X : Section1.ClassFunction M)
          (Section1.conjugateCharacter (X : Section1.ClassFunction M)) = 0 := by
      simpa [Section1.orthogonal, hXeq, hθeq] using horth
    have hself0 :
        Section1.scalarProduct M
          (X : Section1.ClassFunction M) (X : Section1.ClassFunction M) = 0 := by
      simpa [← hreal] using horth0
    have hself :
        Section1.scalarProduct M
          (X : Section1.ClassFunction M) (X : Section1.ClassFunction M) =
            ((derivedSubgroup M).relIndex
              (Section1.inertiaSubgroup (derivedSubgroup M) ρ.character) : ℂ) := by
      simpa [hXeq, hθeq] using
        (Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
          (derivedSubgroup M) ρ hρirr)
    have hrel_ne :
        (((derivedSubgroup M).relIndex
          (Section1.inertiaSubgroup (derivedSubgroup M) ρ.character)) : ℂ) ≠ 0 := by
      have hrel_nat_ne :
          (derivedSubgroup M).relIndex
            (Section1.inertiaSubgroup (derivedSubgroup M) ρ.character) ≠ 0 := by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite
      exact_mod_cast hrel_nat_ne
    exact hrel_ne (by rw [← hself, hself0])


public theorem theorem_10_10_exists_hypothesis_4_6_of_section10FourSixNotationSupported
    {G : Type u}
    [Group G]
    [Finite G]
    {M W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {MF : Subgroup G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hNotation10 :
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) :
    ∃ Apre : Set M,
      Section4Scratch.hypothesis_4_6_statement
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (derivedSubgroup M)
        Apre := by
  rcases hNotation10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign,
      ω, σ, hNotation⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  have h46 :=
    hypothesis_4_6_derived_of_section10FourSixNotationSupportedData_of_late
      hP.1 (Or.inr (Or.inr hTypeV)) hNotation
  rcases hNotation with
    ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource,
      hW, _hA0, _h46Selected, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
      _h45, _h48, _hTauA0, _hFull⟩
  exact ⟨A, by simpa [hW] using h46⟩

public theorem theorem_10_10_hypothesis_5_2_of_section10FourSixNotationSupported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hS : derivedInducedFamily M S)
    (hNotation10 :
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) :
    Section5.hypothesis_5_2_statement S τ := by
  rcases hNotation10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign,
      ω, σ, hNotation⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  rcases derivedSupportedFourSixData_of_section10FourSixNotationSupportedData_of_late
      hP.1 (Or.inr (Or.inr hTypeV)) hNotation with
    ⟨σM, xChar, H_A, _H_A0, hSupported46⟩
  rcases hNotation with
    ⟨_MFsrc, _Ms, Abook, _A0book, _A1book, hSource,
      hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, _hFull⟩
  rcases hSource with ⟨hApre, _hA0sub, _hNotationSrc, _hDadeSrc⟩
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hFamilyMF : Section8.section8InducedNonkernelFamily M MF S :=
    theorem_10_10_section8InducedNonkernelFamily_of_typeP_bot hP hS
  have hFamilyD :
      Section8.section8InducedNonkernelFamily M (ambientDerivedSubgroup M) S := by
    simpa [hMF_eq_D] using hFamilyMF
  have hSupportedCtxt :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        W
        (derivedSubgroup M)
        A
        i0 j0 ω σM σ μ xChar (fun j => (δSign j : ℂ)) τ H_A := by
    exact hSupported46
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σL := σM)
      (σ := σ)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ)
      (H_A := H_A)
      hSupportedCtxt
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    theorem_10_10_hypothesis52_a_of_section8InducedNonkernelFamily hFamilyD
  have hInd :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup M) (derivedSubgroup M) S := by
    simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using
      theorem_10_10_inducedFromNonkernelFamily_of_section8 hFamilyD
  have hpack :=
    Section5.theorem_5_3_b_core
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (H := derivedSubgroup M)
      (A := A)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σL := σM)
      (σ := σ)
      (piChar := μ)
      (xChar := xChar)
      (deltaSign := fun j => (δSign j : ℂ))
      (τ := τ)
      (S := S)
      hCtx hFamilyD.1 h52a hInd
  rcases hpack with ⟨R5, hsetup, h52a', h52b, h52c, h52d, h52e, _hextra⟩
  exact ⟨hsetup, R5, h52a', h52b, h52c, h52d, h52e⟩


public theorem theorem_10_10_dadeIsometryRelativeToA0SupportedSourceData_of_section10FourSixNotationSupported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hNotation10 :
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ) :
    dadeIsometryRelativeToA0SupportedSourceData M MF τ := by
  rcases hNotation10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign,
      ω, σ, hNotation⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  rcases hNotation with
    ⟨MFsrc, Ms, Abook, A0book, A1book, hSource, _hW, _hA0, _h46,
      _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull⟩
  rcases hSource with
    ⟨_hApre, _hA0sub, hNotationSrc, H_A0, hA0M, hτ⟩
  have hMFsrc_eq : MFsrc = MF :=
    section16MFSubgroup_unique hNotationSrc.2.1 hP.1
  exact ⟨Ms, Abook, A0book, A1book, H_A0,
    by simpa [hMFsrc_eq] using hNotationSrc, hA0M, hτ⟩


public def theorem_10_10_typeV_ti_fourSixSupportedCoreData
    {G : Type u}
    [Group G]
    [Finite G]
    (M MF W1 W2 : Subgroup G) : Prop :=
  ∃ Ms : Subgroup G, ∃ Abook A0book A1book : Set G,
    ∃ d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 Abook,
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      letI : DecidableEq d52.I := d52.instDecidableEqI
      letI : DecidableEq d52.J := d52.instDecidableEqJ
      ∃ δSign : d52.J → ℤ,
        d52.deltaSign = (fun j => (δSign j : ℂ)) ∧
          Section8.notation_8_10_source_data M MF Ms Abook A0book A1book ∧
          Section8.section8SubgroupSetPreimage M A0book ⊆
            Section4Scratch.a0Set (W2.subgroupOf M) d52.W
              (Section8.section8SubgroupSetPreimage M Abook) ∧
          (∃ hA0M : Section2.Hypothesis2 A0book M d52.H_A0,
            ∀ α : Section1.ClassFunction M,
              Section2.CFOn M A0book α →
                d52.tau α =
                  Section2.dadeTransform d52.H_A0 hA0M.subset_L α) ∧
          section10BaseRowGaloisData d52.i0 d52.j0 d52.piChar δSign

public theorem theorem_10_10_not_typeI_of_typeV_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF)) :
    ¬ Section8.typeIDefinitionData M MF := by
  exact
    Section8.not_typeIDefinitionData_of_typeP_bot_typeV_source
      _hM _hP _hAlt

public theorem theorem_10_10_typeV_notation_typeP_witness
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    Section8.notation_8_10_source_typeP_witness M MF Ms A A0 A1
      ⊥ W1 W2 := by
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  have hMs_eq : Ms = MF :=
    theorem_10_10_ms_eq_mf_of_typeV_notation hNotation hTypeV
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hLateType :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF :=
    Or.inr (Or.inr hTypeV)
  have hAcentral :
      A = Section8.section8CentralizerUnion (ambientDerivedSubgroup M) Ms := by
    have hAD :
        A = Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
          (ambientDerivedSubgroup M) :=
      theorem_10_8_A_eq_late_of_notation_8_10_source_data
        hNotation hLateType
    simpa [hMs_eq, hMF_eq_D] using hAD
  exact ⟨hP, Or.inr (Or.inr (Or.inr hTypeV)), hAcentral, hA0, hLate⟩

public theorem theorem_10_10_source_typeV_fourSixCore_hypothesis52_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (_hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (_hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (_hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    Section8.section8Hypothesis52Source M MF Ms A A0 A1 := by
  exact
    Section8.section8Hypothesis52Source_of_typeP_bot_typeV_notation_source
      _hP _hAlt _hNotation _hA0 _hLate

public theorem theorem_10_10_source_typeV_fourSixCore_fullData_payload_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (_hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (_hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (_hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    Nonempty (Section8.section8Hypothesis52FullData M Ms W1 W2 A) := by
  exact
    (theorem_10_10_source_typeV_fourSixCore_hypothesis52_source
      _hP _hAlt _hNotation _hA0 _hLate)
        ⊥ W1 W2
        (theorem_10_10_typeV_notation_typeP_witness
          _hP _hAlt _hNotation _hA0 _hLate)

public theorem theorem_10_10_deltaSign_int_witness_of_hypothesis52FullData
    {G : Type u}
    [Group G]
    [Finite G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 A) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    ∃ δSign : d52.J → ℤ,
      d52.deltaSign = (fun j => (δSign j : ℂ)) := by
  classical
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  rcases d52.fullHypothesis with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      htail⟩
  rcases htail with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hBaseColumn⟩
  let δSign : d52.J → ℤ :=
    fun j => if d52.deltaSign j = 1 then 1 else -1
  refine ⟨δSign, ?_⟩
  funext j
  by_cases hδ : d52.deltaSign j = 1
  · simp [δSign, hδ]
  · have hsign : Section1.IsSign (d52.deltaSign j) := h43b.2.1 j
    rw [Section1.IsSign] at hsign
    rcases hsign with hδone | hδneg
    · exact False.elim (hδ hδone)
    · simp [δSign, hδneg]

public theorem theorem_10_10_typeV_notation_W2_prime
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1) :
    Nat.Prime (Nat.card W2) := by
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  rcases hNotation with ⟨hM, _hMF, hMs, _hA1, _hCases⟩
  have hPair : section10TypeIIPairingData W2 :=
    section10TypeIIPairingData_of_source_typeP_msChoice_tail
      (G := G) (M := M) (MF := MF) (U := (⊥ : Subgroup G))
      (W1 := W1) (W2 := W2) (Ms := Ms)
      hM hP hMs (Or.inr (Or.inr hTypeV))
  exact nat_prime_card_of_section10TypeIIPairingData hPair

public theorem theorem_10_10_source_typeV_fourSixCore_payload_baseRowGalois_prime_source
    {G : Type u}
    [Group G]
    [Finite G]
    {M Ms W1 W2 : Subgroup G}
    {A : Set G}
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 A)
    (δSign : d52.J → ℤ)
    (_hδSign : d52.deltaSign = (fun j => (δSign j : ℂ)))
    (_hW2prime : Nat.Prime (Nat.card (W2.subgroupOf M))) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    section10BaseRowGaloisData d52.i0 d52.j0 d52.piChar δSign := by
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  exact
    section10BaseRowGaloisData_of_hypothesis_4_6_supported_statement
      (L := M)
      (K := derivedSubgroup M)
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := d52.W)
      (H := Ms.subgroupOf M)
      (A := Section8.section8SubgroupSetPreimage M A)
      (i0 := d52.i0)
      (j0 := d52.j0)
      (ω := d52.omega)
      (σL := d52.sigmaM)
      (σ := d52.sigma)
      (piChar := d52.piChar)
      (xChar := d52.xChar)
      (deltaSign := d52.deltaSign)
      (deltaSignInt := δSign)
      (τ := d52.tau)
      (H_A := d52.H_A)
      d52.fullHypothesis _hδSign _hW2prime

public theorem theorem_10_10_source_typeV_fourSixCore_payload_baseRowGalois_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (_hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (_hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (_hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1)
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 A)
    (δSign : d52.J → ℤ)
    (_hδSign : d52.deltaSign = (fun j => (δSign j : ℂ))) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    section10BaseRowGaloisData d52.i0 d52.j0 d52.piChar δSign := by
  have hW2prime : Nat.Prime (Nat.card W2) :=
    theorem_10_10_typeV_notation_W2_prime _hP _hAlt _hNotation
  rcases theorem_10_10_source_typeV_structural_hypothesis_10_1_fields
      _hP _hAlt with
    ⟨_hType, _hW1M, hW2M, _hW12M⟩
  have hW2localCard : Nat.card (W2.subgroupOf M) = Nat.card W2 :=
    natCard_subgroupOf_eq W2 M hW2M
  have hW2localPrime : Nat.Prime (Nat.card (W2.subgroupOf M)) := by
    rw [hW2localCard]
    exact hW2prime
  exact
    theorem_10_10_source_typeV_fourSixCore_payload_baseRowGalois_prime_source
      d52 δSign _hδSign hW2localPrime

public theorem theorem_10_10_source_typeV_fourSixCore_payload_baseRow_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (_hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (_hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (_hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1)
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 A) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    ∃ δSign : d52.J → ℤ,
      d52.deltaSign = (fun j => (δSign j : ℂ)) ∧
        section10BaseRowGaloisData d52.i0 d52.j0 d52.piChar δSign := by
  rcases theorem_10_10_deltaSign_int_witness_of_hypothesis52FullData d52 with
    ⟨δSign, hδSign⟩
  exact
    ⟨δSign, hδSign,
      theorem_10_10_source_typeV_fourSixCore_payload_baseRowGalois_source
        _hP _hAlt _hNotation _hA0 _hLate d52 δSign hδSign⟩

public theorem theorem_10_10_section8SubgroupSetPreimage_typeP_A0_eq
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {A A0 : Set G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G)) :
    Section8.section8SubgroupSetPreimage M A0 =
      Section8.section8CyclicA0Set M W1 W2 A := by
  classical
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hW1M : W1 ≤ M := hW1hall.1
  have hW2M : W2 ≤ M := fun y hy => hMF.1.1 (hW2le hy).1
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  ext x
  constructor
  · intro hx
    change (x : G) ∈ A0 at hx
    rw [hA0] at hx
    rcases hx with hxA | hxConj
    · exact Or.inl hxA
    · rcases hxConj with ⟨w, hw, m, hmM, hx_eq⟩
      let wM : M := ⟨w, hWM hw.1⟩
      have hwM :
          wM ∈ Section3.cyclicTISet
            (W1.subgroupOf M) (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M) := by
        simpa [wM, Section3.cyclicTISet, section16HatW, Subgroup.mem_subgroupOf]
          using hw
      let mM : M := ⟨m, hmM⟩
      refine Or.inr ?_
      refine ⟨wM, hwM, mM, ?_⟩
      ext
      simpa [Section2.conjBy, wM, mM] using hx_eq.symm
  · intro hx
    change (x : G) ∈ A0
    rw [hA0]
    rcases hx with hxA | hxConj
    · exact Or.inl hxA
    · rcases hxConj with ⟨wM, hwM, mM, hconj⟩
      refine Or.inr ?_
      refine ⟨(wM : G), ?_, (mM : G), mM.property, ?_⟩
      · simpa [Section3.cyclicTISet, section16HatW, Subgroup.mem_subgroupOf]
          using hwM
      · have hval := congrArg Subtype.val hconj
        simpa [Section2.conjBy] using hval.symm


public theorem theorem_10_10_subgroupImageSet_section8SubgroupSetPreimage_eq
    {G : Type u} [Group G]
    {M : Subgroup G} {A : Set G}
    (hA : A ⊆ (M : Set G)) :
    Section4Scratch.subgroupImageSet M
        (Section8.section8SubgroupSetPreimage M A) = A := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [Section8.section8SubgroupSetPreimage] using hm
  · intro hg
    exact ⟨⟨g, hA hg⟩,
      by simpa [Section8.section8SubgroupSetPreimage] using hg, rfl⟩

public theorem theorem_10_10_source_typeV_A0_subset_M
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    A0 ⊆ (M : Set G) := by
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq, _hFittingLeD,
      hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hW1M : W1 ≤ M := hW1hall.1
  have hW2M : W2 ≤ M := fun y hy => hMF.1.1 (hW2le hy).1
  have hWM : W1 ⊔ W2 ≤ M := sup_le hW1M hW2M
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _,
      ⟨hMF, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD, _hUnil,
        _hW1normU, _hcompDU, _hMFnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩,
      rfl, hAlt⟩
  have hLateV := hLate (Or.inr (Or.inr hTypeV))
  intro x hx
  rw [hA0] at hx
  rcases hx with hxA | hxConj
  · have hxD :
        x ∈ section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
      simpa [hLateV.2, hLateV.1] using hxA
    exact section12_ambientDerivedSubgroup_le hxD.1
  · rcases hxConj with ⟨w, hw, m, hmM, hx_eq⟩
    have hwM : w ∈ M := hWM hw.1
    rw [hx_eq]
    exact M.mul_mem (M.mul_mem hmM hwM) (M.inv_mem hmM)

public theorem theorem_10_10_source_typeV_A0_subset_section4_a0Set_image
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1)
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 A) :
    A0 ⊆
      Section4Scratch.subgroupImageSet M
        (Section4Scratch.a0Set (W2.subgroupOf M) d52.W
          (Section8.section8SubgroupSetPreimage M A)) := by
  intro x hx
  have hA0subM : A0 ⊆ (M : Set G) :=
    theorem_10_10_source_typeV_A0_subset_M hP hAlt hA0 hLate
  have hpre :
      Section8.section8SubgroupSetPreimage M A0 =
        Section8.section8CyclicA0Set M W1 W2 A :=
    theorem_10_10_section8SubgroupSetPreimage_typeP_A0_eq hP hA0
  have hlocal :
      (⟨x, hA0subM hx⟩ : M) ∈
        Section4Scratch.a0Set (W2.subgroupOf M) d52.W
          (Section8.section8SubgroupSetPreimage M A) := by
    have hxpre :
        (⟨x, hA0subM hx⟩ : M) ∈
          Section8.section8SubgroupSetPreimage M A0 := by
      simpa [Section8.section8SubgroupSetPreimage] using hx
    exact
      Section8.section8CyclicA0Set_subset_section4_a0Set
        (M := M) (W1 := W1) (W2 := W2) (A := A) (W := d52.W)
        d52.W_eq (by simpa [hpre] using hxpre)
  exact ⟨⟨x, hA0subM hx⟩, hlocal, rfl⟩

public theorem theorem_10_10_source_typeV_A0_le_setNormalizer
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1) :
    M ≤ Section2.setNormalizer A0 := by
  classical
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  have hLateV := hLate (Or.inr (Or.inr hTypeV))
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDnorm : (D.subgroupOf M).Normal := by
    simpa [D] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hMnormD : M ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDleM).1 hDnorm
  have hforward :
      ∀ m : G, m ∈ M → ∀ z : G, z ∈ A0 → m * z * m⁻¹ ∈ A0 := by
    intro m hmM z hz
    rw [hA0] at hz ⊢
    rcases hz with hzA | hzConj
    · have hzD :
          z ∈ section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
        simpa [hLateV.2, hLateV.1] using hzA
      have hconjD : m * z * m⁻¹ ∈ D :=
        (hMnormD hmM z).1 (by simpa [D] using hzD.1)
      have hconj_ne : m * z * m⁻¹ ≠ 1 := by
        intro hconj_one
        apply hzD.2
        calc
          z = m⁻¹ * (m * z * m⁻¹) * m := by group
          _ = m⁻¹ * 1 * m := by rw [hconj_one]
          _ = 1 := by group
      have hconjSharp :
          m * z * m⁻¹ ∈
            section16NonidentityElements (ambientDerivedSubgroup M : Set G) :=
        ⟨by simpa [D] using hconjD, hconj_ne⟩
      exact Or.inl (by
        simpa [hLateV.2, hLateV.1] using hconjSharp)
    · rcases hzConj with ⟨x, hx, y, hyM, hz_eq⟩
      refine Or.inr ?_
      refine ⟨x, hx, m * y, M.mul_mem hmM hyM, ?_⟩
      rw [hz_eq]
      group
  intro m hmM
  change Section2.normalizesSet A0 m
  intro z
  constructor
  · intro hz
    have hzback := hforward m⁻¹ (M.inv_mem hmM) (m * z * m⁻¹) hz
    simpa [mul_assoc] using hzback
  · exact hforward m hmM z

public theorem theorem_10_10_source_typeV_fourSixCore_payload_commonTauOnA0_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms W1 W2 : Subgroup G}
    {A A0 A1 : Set G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (_hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (_hA0 :
      A0 = A ∪ section16ConjugatesOfSetBySet
        (section16HatW W1 W2) (M : Set G))
    (_hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1)
    (d52 : Section8.section8Hypothesis52FullData M Ms W1 W2 A) :
    letI : Fintype d52.I := d52.instFintypeI
    letI : Fintype d52.J := d52.instFintypeJ
    letI : DecidableEq d52.I := d52.instDecidableEqI
    letI : DecidableEq d52.J := d52.instDecidableEqJ
    ∃ hA0M : Section2.Hypothesis2 A0 M d52.H_A0,
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M A0 α →
          d52.tau α =
            Section2.dadeTransform d52.H_A0 hA0M.subset_L α := by
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  have hCyclicPre :
      Section8.section8SubgroupSetPreimage M A0 =
        Section8.section8CyclicA0Set M W1 W2 A :=
    theorem_10_10_section8SubgroupSetPreimage_typeP_A0_eq _hP _hA0
  have hA0sub : A0 ⊆ (M : Set G) :=
    theorem_10_10_source_typeV_A0_subset_M _hP _hAlt _hA0 _hLate
  have hCyclicImage :
      Section4Scratch.subgroupImageSet M
          (Section8.section8CyclicA0Set M W1 W2 A) = A0 := by
    calc
      Section4Scratch.subgroupImageSet M
          (Section8.section8CyclicA0Set M W1 W2 A) =
          Section4Scratch.subgroupImageSet M
            (Section8.section8SubgroupSetPreimage M A0) := by
            rw [← hCyclicPre]
      _ = A0 :=
          theorem_10_10_subgroupImageSet_section8SubgroupSetPreimage_eq hA0sub
  have hA0norm : M ≤ Section2.setNormalizer A0 :=
    theorem_10_10_source_typeV_A0_le_setNormalizer
      _hP _hAlt _hA0 _hLate
  have h211 := Section2.proposition_2_11
    (Section4Scratch.subgroupImageSet M
      (Section8.section8CyclicA0Set M W1 W2 A))
    A0 M d52.H_A0
  have hA0subCyclic :
      A0 ⊆
        Section4Scratch.subgroupImageSet M
          (Section8.section8CyclicA0Set M W1 W2 A) := by
    intro x hx
    simpa [hCyclicImage] using hx
  have hA0M : Section2.Hypothesis2 A0 M d52.H_A0 :=
    (h211 hA0subCyclic hA0norm d52.cyclicA0Hypothesis).1
  have hRestrict :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M A0 α →
          Section2.dadeTransform d52.H_A0
              d52.cyclicA0Hypothesis.subset_L α =
            Section2.dadeTransform d52.H_A0 hA0M.subset_L α :=
    (h211 hA0subCyclic hA0norm d52.cyclicA0Hypothesis).2
      d52.cyclicA0Hypothesis.subset_L hA0M.subset_L
  have hCFOnCyclic :
      ∀ α : Section1.ClassFunction M,
        Section2.CFOn M A0 α →
          Section2.CFOn M
            (Section4Scratch.subgroupImageSet M
              (Section8.section8CyclicA0Set M W1 W2 A)) α := by
    intro α hα
    simpa [hCyclicImage] using hα
  refine ⟨hA0M, ?_⟩
  intro α hα
  exact (d52.tau_cyclicA0 α (hCFOnCyclic α hα)).trans
    (hRestrict α hα)


public theorem theorem_10_10_source_typeV_fourSixSupportedCore_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF)) :
    theorem_10_10_typeV_ti_fourSixSupportedCoreData M MF W1 W2 := by
  classical
  have hnotI : ¬ Section8.typeIDefinitionData M MF :=
    theorem_10_10_not_typeI_of_typeV_source _hM _hP _hAlt
  rcases theorem_10_10_exists_notation_8_10_source_data_of_typeV_not_typeI
      _hM _hP _hAlt hnotI with
    ⟨Ms, A, A0, A1, hNotation, _hMs, hA1, hA, hA0⟩
  have hLate :
      (Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF) →
        A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) ∧
          A = A1 := by
    intro _hLate
    exact ⟨hA1, hA⟩
  rcases theorem_10_10_source_typeV_fourSixCore_fullData_payload_source
      _hP _hAlt hNotation hA0 hLate with
    ⟨d52⟩
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  rcases theorem_10_10_source_typeV_fourSixCore_payload_baseRow_source
      _hP _hAlt hNotation hA0 hLate d52 with
    ⟨δSign, hδSign, hGalois⟩
  have hA0subImage :
      A0 ⊆
        Section4Scratch.subgroupImageSet M
          (Section4Scratch.a0Set (W2.subgroupOf M) d52.W
            (Section8.section8SubgroupSetPreimage M A)) :=
    theorem_10_10_source_typeV_A0_subset_section4_a0Set_image
      _hP _hAlt hA0 hLate d52
  have hA0subLocal :
      Section8.section8SubgroupSetPreimage M A0 ⊆
        Section4Scratch.a0Set (W2.subgroupOf M) d52.W
          (Section8.section8SubgroupSetPreimage M A) := by
    intro x hx
    have hxA0 : (x : G) ∈ A0 := by
      simpa [Section8.section8SubgroupSetPreimage] using hx
    rcases hA0subImage hxA0 with ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  rcases theorem_10_10_source_typeV_fourSixCore_payload_commonTauOnA0_source
      _hP _hAlt hNotation hA0 hLate d52 with
    ⟨hA0M, hτ⟩
  exact ⟨Ms, A, A0, A1, d52, δSign, hδSign, hNotation, hA0subLocal,
    ⟨hA0M, hτ⟩, hGalois⟩

public theorem theorem_10_10_fourSixNotationSupportedPackage_of_core
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF))
    (hCore : theorem_10_10_typeV_ti_fourSixSupportedCoreData M MF W1 W2) :
    ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
      ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
        @section10FourSixNotationSupportedData G _ _ I J instI instJ decI decJ
          M W1 W2 W A A0 i0 j0 μ δSign ω σ τ := by
  rcases hCore with
    ⟨Ms, Abook, A0book, A1book, d52, δSign, hδSign, hNotation,
      hA0sub, hDade, hGalois⟩
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, hAlt⟩
  have hMs_eq : Ms = MF :=
    theorem_10_10_ms_eq_mf_of_typeV_notation hNotation hTypeV
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hMs_subgroupOf_eq : Ms.subgroupOf M = derivedSubgroup M := by
    simpa [hMs_eq, hMF_eq_D] using
      (section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M))
  have hFull46 :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        d52.W
        (derivedSubgroup M)
        (Section8.section8SubgroupSetPreimage M Abook)
        d52.i0
        d52.j0
        d52.omega
        d52.sigmaM
        d52.sigma
        d52.piChar
        d52.xChar
        (fun j => (δSign j : ℂ))
        d52.tau
        d52.H_A := by
    simpa [hδSign, hMs_subgroupOf_eq] using d52.fullHypothesis
  have hFull46pkg := hFull46
  rcases hFull46 with
    ⟨h46, _hW2K, _h31, hIso, hVirt, _hClass, hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, h45a, h45b, _hTauCyc, h48,
      hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have h45 :
      Section4Scratch.theorem_4_5_statement (derivedSubgroup M) d52.piChar :=
    ⟨d52.xChar, h45a, h45b⟩
  refine ⟨d52.tau, d52.I, d52.instFintypeI, d52.instDecidableEqI,
    d52.J, d52.instFintypeJ, d52.instDecidableEqJ, d52.W,
    Section8.section8SubgroupSetPreimage M Abook,
    Section4Scratch.a0Set (W2.subgroupOf M) d52.W
      (Section8.section8SubgroupSetPreimage M Abook),
    d52.i0, d52.j0, d52.piChar, δSign, d52.omega, d52.sigma, ?_⟩
  exact ⟨MF, Ms, Abook, A0book, A1book,
    ⟨rfl, hA0sub, hNotation, ⟨d52.H_A0, hDade⟩⟩,
    d52.W_eq, rfl, (by simpa [hMs_subgroupOf_eq] using h46),
    hω, hIso, hVirt, hPrin, d52.sigma_agrees_cyclicTI,
    h45, h48,
    hTauIso, ⟨d52.sigmaM, d52.xChar, d52.H_A, d52.H_A0,
      (by simpa [hMs_subgroupOf_eq] using hFull46pkg), hGalois⟩⟩


public theorem theorem_10_10_source_typeV_hypothesis_10_1_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF)) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ := by
  rcases theorem_10_10_exists_derivedInducedFamily M with ⟨S, hS⟩
  rcases theorem_10_10_fourSixNotationSupportedPackage_of_core
      _hP _hAlt
      (theorem_10_10_source_typeV_fourSixSupportedCore_source _hM _hP _hAlt) with
    ⟨τ, hNotation10⟩
  have hDade : dadeIsometryRelativeToA0SupportedSourceData M MF τ :=
    theorem_10_10_dadeIsometryRelativeToA0SupportedSourceData_of_section10FourSixNotationSupported
      _hP hNotation10
  have h46 :
      ∃ Apre : Set M,
        Section4Scratch.hypothesis_4_6_statement
          (derivedSubgroup M)
          (W1.subgroupOf M)
          (W2.subgroupOf M)
          ((W1 ⊔ W2).subgroupOf M)
          (derivedSubgroup M)
          Apre :=
    theorem_10_10_exists_hypothesis_4_6_of_section10FourSixNotationSupported
      _hP _hAlt hNotation10
  have h52 : Section5.hypothesis_5_2_statement S τ :=
    theorem_10_10_hypothesis_5_2_of_section10FourSixNotationSupported
      _hP _hAlt hS hNotation10
  refine ⟨S, τ, ?_⟩
  exact theorem_10_10_hypothesis_10_1_supported_of_typeV_source_context
    _hM _hP _hAlt hS hDade h46 hNotation10 h52

public theorem theorem_10_10_section8SubgroupSetPreimage_derived_nonidentity
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    Section8.section8SubgroupSetPreimage M
        (section16NonidentityElements (ambientDerivedSubgroup M : Set G)) =
      {x : M | x ∈ derivedSubgroup M ∧ x ≠ 1} := by
  ext x
  constructor
  · intro hx
    constructor
    · have hxD : (x : G) ∈ ambientDerivedSubgroup M := hx.1
      have hxDsub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := hxD
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
        using hxDsub
    · intro hxone
      exact hx.2 (by simp [hxone])
  · rintro ⟨hxD, hxne⟩
    constructor
    · have hxD' :
          x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
        simpa [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
          using hxD
      exact hxD'
    · intro hxone
      exact hxne (Subtype.ext hxone)


public theorem theorem_10_10_caseC2FullData_of_typeV_ti_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hTI : section16TISubset (section16NonidentityElements (MF : Set G)))
  (h10 : hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    Nonempty
      (Section6.caseC2FullData M (derivedSubgroup M)
        (W1.subgroupOf M) (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) τ) := by
  rcases exists_section10FourSixNotationSupportedData_of_hypothesis_10_1_supported_data
      h10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign,
      ω, σ, hNotation10⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  rcases hNotation10 with
    ⟨MFsrc, Ms, Abook, A0book, A1book, hSource,
      hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin,
        _hσAgreeCyc, _h45, _h48, _hTauA0, hFull⟩
  rcases hSource with ⟨hApre, _hA0sub, hNotationSrc, _hDadeSrc⟩
  rcases hFull with ⟨σM, xChar, H_A, _H_A0, hSupported46, _hGalois⟩
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, hP, rfl, Or.inl hTI⟩
  have hMFsrc_eq : MFsrc = MF :=
    section16MFSubgroup_unique hNotationSrc.2.1 hP.1
  have hNotationOuter :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book := by
    simpa [hMFsrc_eq] using hNotationSrc
  have hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF :=
    Or.inr (Or.inr hTypeV)
  have hMs_eq : Ms = ambientDerivedSubgroup M :=
    Section8.notation_8_10_source_data_ms_eq_ambientDerived_of_late
      hNotationOuter hTail
  have hCarrier : Ms.subgroupOf M = derivedSubgroup M := by
    rw [hMs_eq, section12_ambientDerivedSubgroup_subgroupOf_eq]
  have hAbook_eq_A1 : Abook = A1book :=
    theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data
      hNotationOuter hTail
  have hA1book_eq :
      A1book =
        section16NonidentityElements (ambientDerivedSubgroup M : Set G) :=
    theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
      hNotationOuter hTail
  have hAeq :
      A = {x : M | x ∈ derivedSubgroup M ∧ x ≠ 1} := by
    calc
      A = Section8.section8SubgroupSetPreimage M Abook := hApre
      _ = Section8.section8SubgroupSetPreimage M
            (section16NonidentityElements (ambientDerivedSubgroup M : Set G)) := by
          rw [hAbook_eq_A1, hA1book_eq]
      _ = {x : M | x ∈ derivedSubgroup M ∧ x ≠ 1} :=
          theorem_10_10_section8SubgroupSetPreimage_derived_nonidentity M
  subst W
  have hSupportedC2 :
      Section4Scratch.hypothesis_4_6_supported_statement M
        (derivedSubgroup M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (derivedSubgroup M)
        ({x : M | x ∈ derivedSubgroup M ∧ x ≠ 1})
        i0 j0 ω σM σ μ xChar (fun j => (δSign j : ℂ)) τ H_A := by
    simpa [hAeq, hCarrier] using hSupported46
  exact ⟨
    { I := I
      J := J
      instFintypeI := instI
      instFintypeJ := instJ
      instDecidableEqI := decI
      instDecidableEqJ := decJ
      i0 := i0
      j0 := j0
      omega := ω
      sigmaL := σM
      sigma := σ
      piChar := μ
      xChar := xChar
      deltaSign := fun j => (δSign j : ℂ)
      H_A := H_A
      H_A0 := fun _ => ⊥
      fullHypothesis := hSupportedC2 }⟩

public theorem theorem_10_10_typeP_W2_subgroupOf_le_derived_commutator
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    W2.subgroupOf M ≤ ⁅derivedSubgroup M, derivedSubgroup M⁆ := by
  intro x hxW2
  have hxSecond :
      x ∈ (section16SecondDerivedSubgroup M).subgroupOf M :=
    typePDefinitionData_W2_subgroupOf_le_secondDerived_subgroupOf hP hxW2
  have hxD : x ∈ derivedSubgroup M :=
    secondDerivedSubgroup_subgroupOf_le_derived M hxSecond
  have hxSecondD :
      (⟨x, hxD⟩ : derivedSubgroup M) ∈
        ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M) := by
    change x ∈ (section16SecondDerivedSubgroup M).subgroupOf M
    exact hxSecond
  have hxCommD : (⟨x, hxD⟩ : derivedSubgroup M) ∈
      derivedSubgroup (derivedSubgroup M) := by
    rw [← secondDerivedSubgroup_subgroupOf_derived_eq M]
    exact hxSecondD
  have hxMap :
      (x : M) ∈ (derivedSubgroup (derivedSubgroup M)).map
        (derivedSubgroup M).subtype :=
    ⟨⟨x, hxD⟩, hxCommD, rfl⟩
  change (x : M) ∈ (commutator (derivedSubgroup M)).map
      (derivedSubgroup M).subtype at hxMap
  rw [← Subgroup.map_subtype_commutator (H := derivedSubgroup M)]
  exact hxMap


public theorem theorem_10_10_source_typeV_ti_W2_prime_card_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    ∃ p : ℕ, Nat.Prime p ∧ Nat.card (W2.subgroupOf M) = p := by
  have hPrimeW2 : Nat.Prime (Nat.card W2) :=
    nat_prime_card_of_section10TypeIIPairingData
      (section10TypeIIPairingData_of_hypothesis_10_1_supported _h10)
  rcases _h10 with
    ⟨_hM, _hType, _hS, _hW1M, hW2M, _hW12M, _hDade, _h46,
      _hNotation10, _h52⟩
  refine ⟨Nat.card W2, hPrimeW2, ?_⟩
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).toEquiv


public theorem theorem_10_10_source_typeV_ti_pf6_8_branch_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hTI : section16TISubset (section16NonidentityElements (MF : Set G)))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    Section6.frobeniusWithKernel (⊤ : Subgroup M) (derivedSubgroup M) ∨
      Section6.caseC2Hypothesis M (derivedSubgroup M)
        (W1.subgroupOf M) (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M) τ := by
  refine Or.inr ?_
  exact ⟨
    theorem_10_10_caseC2FullData_of_typeV_ti_supported _hP _hTI _h10,
    theorem_10_10_source_typeV_ti_W2_prime_card_source_supported _h10,
    theorem_10_10_typeP_W2_subgroupOf_le_derived_commutator _hP⟩

public theorem theorem_10_10_source_typeV_ti_hypothesis_10_1_and_6_8_tail_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hTI : section16TISubset (section16NonidentityElements (MF : Set G))) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ ∧
          (Section6.frobeniusWithKernel (⊤ : Subgroup M) (derivedSubgroup M) ∨
            Section6.caseC2Hypothesis M (derivedSubgroup M)
              (W1.subgroupOf M) (W2.subgroupOf M)
              ((W1 ⊔ W2).subgroupOf M) τ) := by
  rcases theorem_10_10_source_typeV_hypothesis_10_1_supported_source
      _hM _hP (Or.inl _hTI) with
    ⟨S, τ, h10⟩
  exact ⟨S, τ, h10,
    theorem_10_10_source_typeV_ti_pf6_8_branch_source_supported
      _hP _hTI h10⟩

public theorem theorem_10_10_source_typeV_ti_hypothesis_6_8_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hTI : section16TISubset (section16NonidentityElements (MF : Set G))) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ ∧
          Section6.theorem_6_8_hypothesis M (derivedSubgroup M)
            (W1.subgroupOf M) (W2.subgroupOf M)
            ((W1 ⊔ W2).subgroupOf M) S τ := by
  rcases theorem_10_10_source_typeV_ti_hypothesis_10_1_and_6_8_tail_source_supported
      _hM _hP _hTI with
    ⟨S, τ, h10, hBranch⟩
  have hTind : Section6.transformAgreesWithInductionOn M S τ :=
    theorem_10_10_transformAgreesWithInductionOn_of_typeV_ti_supported
      _hP _hTI h10
  have hTI68 :
      Section2.IsTISubsetWithNormalizer
        (Section6.subgroupImagePuncturedSet M (derivedSubgroup M)) M :=
    theorem_10_10_typeV_ti_subgroupImagePuncturedSet
      _hM _hP _hTI
  have h42 : Section4.hypothesis_4_2_statement
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) :=
    hypothesis_4_2_of_hypothesis_10_1_supported_data h10
  have hoddM : Odd (Nat.card M) :=
    Odd.of_dvd_nat IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hDne : derivedSubgroup M ≠ ⊥ := by
    have hlt : (section16SecondDerivedSubgroup M).subgroupOf M < derivedSubgroup M :=
      typePDefinitionData_secondDerived_lt_derivedSubgroup _hP
    intro hbot
    rw [hbot] at hlt
    exact (not_lt_of_ge bot_le) hlt
  have hDnil : Group.IsNilpotent (derivedSubgroup M) := by
    rcases _hP.1 with ⟨hMFhall, _hMFmax⟩
    rcases hMFhall with ⟨_hMFleM, _hMFnorm, hMFnil, _hHall⟩
    have hMF_eq_D : MF = ambientDerivedSubgroup M :=
      theorem_10_10_typeP_bot_mf_eq_derived _hP
    let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
      Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
        M.subtype_injective
    have hDnil_ambient : Group.IsNilpotent (ambientDerivedSubgroup M) := by
      have _ : Group.IsNilpotent MF := hMFnil
      exact Group.nilpotent_of_mulEquiv (MulEquiv.subgroupCongr hMF_eq_D)
    exact Group.nilpotent_of_mulEquiv (G := ambientDerivedSubgroup M)
      (G' := derivedSubgroup M) e.symm
  refine ⟨S, τ, h10, ?_⟩
  exact ⟨h42.1, hoddM, hDne, hDnil, hTI68,
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10,
    hTind, hBranch⟩

public theorem theorem_10_10_source_typeV_ti_case_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hTI : section16TISubset (section16NonidentityElements (MF : Set G))) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ ∧
          Section6.coherentFamily S τ := by
  rcases theorem_10_10_source_typeV_ti_hypothesis_6_8_source_supported
      _hM _hP _hTI with
    ⟨S, τ, h10, h68⟩
  exact ⟨S, τ, h10,
    Section6.theorem_6_8 M (derivedSubgroup M) (W1.subgroupOf M)
      (W2.subgroupOf M) ((W1 ⊔ W2).subgroupOf M) S τ h68⟩

public theorem theorem_10_10_section15PCoreIn_eq_self_of_isPGroup
    {G : Type u}
    [Group G]
    [Finite G]
    {H : Subgroup G}
    {p : Nat.Primes}
    (hHp : IsPGroup p.val H) :
    section15PCoreIn p H = H := by
  have hcore_top : pCore p.val H = ⊤ := by
    apply top_unique
    intro x _hx
    have htop_mem : (⊤ : Subgroup H) ∈ normalPSubgroups p.val H := by
      exact ⟨inferInstance, IsPGroup.to_subgroup hHp ⊤⟩
    exact Subgroup.mem_sSup_of_mem htop_mem trivial
  rw [section15PCoreIn, hcore_top]
  ext x
  constructor
  · intro hx
    exact Subgroup.map_subtype_le (H := H) (K := ⊤) hx
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩

public theorem theorem_10_10_nonabelianPQuotient_bot_isPGroup
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {p : Nat.Primes}
    (hpQ :
      Section6.nonabelianPQuotient
        (⊥ : Subgroup M) (derivedSubgroup M) p.val) :
    IsPGroup p.val (derivedSubgroup M) := by
  rcases hpQ with
    ⟨_hbotD, _hbotNormD, _hbotNorm, _hDnorm, _hpprime, hquotP,
      _hnoncomm⟩
  have hbot_sub :
      (⊥ : Subgroup M).subgroupOf (derivedSubgroup M) =
        (⊥ : Subgroup (derivedSubgroup M)) := by
    exact Subgroup.bot_subgroupOf (H := derivedSubgroup M)
  let eQuot :
      derivedSubgroup M ⧸
          (⊥ : Subgroup M).subgroupOf (derivedSubgroup M) ≃*
        derivedSubgroup M :=
    (QuotientGroup.quotientMulEquivOfEq hbot_sub).trans
      QuotientGroup.quotientBot
  exact IsPGroup.of_equiv hquotP eQuot

public theorem theorem_10_10_isPGroup_mf_of_internal_derived
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF : Subgroup G}
    {p : Nat.Primes}
    (hMF_eq_D : MF = ambientDerivedSubgroup M)
    (hpD : IsPGroup p.val (derivedSubgroup M)) :
    IsPGroup p.val MF := by
  have hDmap : (derivedSubgroup M).map M.subtype = ambientDerivedSubgroup M := by
    calc
      (derivedSubgroup M).map M.subtype =
          ((ambientDerivedSubgroup M).subgroupOf M).map M.subtype := by
            rw [section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := M)]
      _ = ambientDerivedSubgroup M ⊓ M :=
          Subgroup.subgroupOf_map_subtype (H := ambientDerivedSubgroup M) (K := M)
      _ = ambientDerivedSubgroup M :=
          inf_eq_left.2 (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  let eMap : derivedSubgroup M ≃* (derivedSubgroup M).map M.subtype :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
      M.subtype_injective
  let eAmb : (derivedSubgroup M).map M.subtype ≃* ambientDerivedSubgroup M :=
    MulEquiv.subgroupCongr hDmap
  let eMF : ambientDerivedSubgroup M ≃* MF :=
    MulEquiv.subgroupCongr hMF_eq_D.symm
  exact IsPGroup.of_equiv hpD ((eMap.trans eAmb).trans eMF)

public theorem theorem_10_10_nonabelianPQuotient_prime_eq_of_typeP_bot_cyclic_core
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {p q : Nat.Primes}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hCyclic : IsCyclic (section10PPrimeCore p MF))
    (hqQ :
      Section6.nonabelianPQuotient
        (⊥ : Subgroup M) (derivedSubgroup M) q.val) :
    q = p := by
  by_contra hne
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hnotcyc : ¬ IsCyclic MF := by
    rcases hP with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hCompM, _hUle, _hUnil,
        _hW1norm, _hCompD, hMFnotCyclic, _hSecondLe, _hFittingEq,
        _hFittingLe, _hW2leMFSecond, _hW2cyc, _hW2ne, _hCentralizer,
        _hNormalizer⟩
    exact hMFnotCyclic
  have hqD : IsPGroup q.val (derivedSubgroup M) :=
    theorem_10_10_nonabelianPQuotient_bot_isPGroup hqQ
  have hqMF : IsPGroup q.val MF :=
    theorem_10_10_isPGroup_mf_of_internal_derived hMF_eq_D hqD
  have hcore_eq : section15PCoreIn q MF = MF :=
    theorem_10_10_section15PCoreIn_eq_self_of_isPGroup hqMF
  have hle_core : section15PCoreIn q MF ≤ section10PPrimeCore p MF :=
    theorem_15_7_pCoreIn_le_pPrimeCore_of_ne
      (G := G) (H := MF) (p := p) (q := q) hne
  have hMFle : MF ≤ section10PPrimeCore p MF := by
    simpa [hcore_eq] using hle_core
  have hcorele : section10PPrimeCore p MF ≤ MF := by
    simpa [section10PPrimeCore] using piCoreIn_le (section10PPrimeSet p) MF
  have hMF_eq_core : MF = section10PPrimeCore p MF :=
    le_antisymm hMFle hcorele
  have hcycMF : IsCyclic MF := by
    rw [hMF_eq_core]
    exact hCyclic
  exact hnotcyc hcycMF

public theorem theorem_10_10_nilpotent_derivedSubgroup_of_typeP_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2) :
    Group.IsNilpotent (derivedSubgroup M) := by
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hCompM, _hUle, _hUnil,
      _hW1norm, _hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hNormalizer⟩
  rcases hMF with ⟨hMFhall, _hMFmax⟩
  rcases hMFhall with ⟨_hMFleM, _hMFnorm, hMFnil, _hHall⟩
  let e : derivedSubgroup M ≃* ambientDerivedSubgroup M :=
    Subgroup.equivMapOfInjective (f := M.subtype) (derivedSubgroup M)
      M.subtype_injective
  have hDnil_ambient : Group.IsNilpotent (ambientDerivedSubgroup M) := by
    have _ : Group.IsNilpotent MF := hMFnil
    exact Group.nilpotent_of_mulEquiv (MulEquiv.subgroupCongr hMF_eq_D)
  exact Group.nilpotent_of_mulEquiv (G := ambientDerivedSubgroup M)
    (G' := derivedSubgroup M) e.symm


public theorem theorem_10_10_hypothesis_6_1_of_typeP_bot_hypothesis_10_1_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    Section6.hypothesis_6_1_statement (derivedSubgroup M) S τ := by
  have hDnorm : (derivedSubgroup M).Normal := by infer_instance
  have hDnil : Group.IsNilpotent (derivedSubgroup M) :=
    theorem_10_10_nilpotent_derivedSubgroup_of_typeP_bot hP
  have hDsolv : Group.IsSolvable (derivedSubgroup M) := by
    have _ : Group.IsNilpotent (derivedSubgroup M) := hDnil
    infer_instance
  exact ⟨hypothesis_5_2_of_hypothesis_10_1_supported_data h10,
    hDnorm, hDsolv,
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10⟩


public theorem theorem_10_10_hypothesis_6_4_commutator_of_frobenius_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ)
    (hfrob :
      Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M) ⁅derivedSubgroup M, derivedSubgroup M⁆) :
    Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ := by
  have h61 :
      Section6.hypothesis_6_1_statement (derivedSubgroup M) S τ :=
    theorem_10_10_hypothesis_6_1_of_typeP_bot_hypothesis_10_1_supported
      hP h10
  have hoddM : Odd (Nat.card M) :=
    Odd.of_dvd_nat IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hDnorm : (derivedSubgroup M).Normal := by infer_instance
  have hDnil : Group.IsNilpotent (derivedSubgroup M) :=
    theorem_10_10_nilpotent_derivedSubgroup_of_typeP_bot hP
  have hnilQuot :
      Section6.nilpotentQuotient (⊥ : Subgroup M) (derivedSubgroup M) :=
    Section6.theorem_6_8_nilpotentQuotient_bot
      (derivedSubgroup M) hDnorm hDnil
  have hcomm :
      Section6.commutatorQuotientHypothesis
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        (derivedSubgroup M) :=
    Section6.theorem_6_8_commutatorQuotient_bot_commutator
      (derivedSubgroup M) hDnorm
  exact ⟨h61, hoddM, bot_le, bot_le, hnilQuot, hcomm, hfrob⟩

public theorem theorem_10_10_frobeniusQuotient_commutator_of_hypothesis_4_2
    {L : Type u}
    [Group L]
    [Finite L]
    {H W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement H W1 W2 W)
    (hHne : H ≠ ⊥)
    (hnil : Group.IsNilpotent H)
    (hW2comm : W2 ≤ ⁅H, H⁆) :
    Section6.frobeniusQuotientWithKernel H ⁅H, H⁆ := by
  classical
  rcases h42 with
    ⟨hsemi, hHall, _hW1cyc, hW1card_ne, _hW2cyc, _hW2card_ne,
      hcentW1, _hW1W, _hW2W, _hW, _hWodd⟩
  have hHnorm : H.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rcases hsemi.mul_surjective g trivial with ⟨h, hh, w, hw, hg⟩
    rw [hg]
    have hwh : Section2.conjBy w n ∈ H :=
      hsemi.right_normalizes_left w hw n hn
    have hconj : h * (w * n * w⁻¹) * h⁻¹ ∈ H := by
      exact H.mul_mem (H.mul_mem hh hwh) (H.inv_mem hh)
    simpa [Section2.conjBy, mul_assoc] using hconj
  have _ : H.Normal := hHnorm
  let H1 : Subgroup L := ⁅H, H⁆
  have hH1_le_H : H1 ≤ H :=
    Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  have _ : H1.Normal := by
    dsimp [H1]
    infer_instance
  have hH1_subgroupOf_comm :
      H1.subgroupOf H = commutator H := by
    ext x
    constructor
    · intro hx
      have hxmap : (x : L) ∈ (commutator H).map H.subtype := by
        rw [Subgroup.map_subtype_commutator]
        exact hx
      rcases hxmap with ⟨y, hycomm, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hycomm
    · intro hx
      have hxmap : (x : L) ∈ (commutator H).map H.subtype :=
        ⟨x, hx, rfl⟩
      rwa [Subgroup.map_subtype_commutator] at hxmap
  have hH_not_le_H1 : ¬ H ≤ H1 := by
    intro hle
    have htop_ne : (⊤ : Subgroup H) ≠ ⊥ := by
      intro htop_bot
      apply hHne
      rw [Subgroup.eq_bot_iff_forall]
      intro x hxH
      have hx_sub : (⟨x, hxH⟩ : H) ∈ (⊥ : Subgroup H) := by
        simp [← htop_bot]
      have hx_eq : (⟨x, hxH⟩ : H) = 1 := by
        simpa using hx_sub
      exact congrArg Subtype.val hx_eq
    have hcomm_lt : commutator H < (⊤ : Subgroup H) := by
      have _ : Group.IsNilpotent H := hnil
      simpa [show commutator H =
          ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ from rfl] using
        (Section6.nilpotent_commutator_lt_self_of_normal
          (⊤ : Subgroup H) htop_ne)
    have hsubtop : H1.subgroupOf H = ⊤ := by
      exact Subgroup.subgroupOf_eq_top.2 hle
    rw [hH1_subgroupOf_comm] at hsubtop
    exact hcomm_lt.ne hsubtop
  have hcomp : H.IsComplement' W1 := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxH hxW1
      have hxInf : x ∈ H ⊓ W1 := ⟨hxH, hxW1⟩
      simpa [hsemi.inf_eq_bot] using hxInf
    · rw [Set.eq_univ_iff_forall]
      intro x
      rcases hsemi.mul_surjective x trivial with ⟨h, hh, w, hw, hx⟩
      exact ⟨h, hh, w, hw, hx.symm⟩
  have hcopHW1 : Nat.Coprime (Nat.card H) (Nat.card W1) := by
    rcases hHall with ⟨π, hHallπ⟩
    have hindex_eq : W1.index = Nat.card H := hcomp.index_eq_card
    simpa [hindex_eq] using
      (IsHallSubgroup.card_coprime_index (π := π) (H := W1) hHallπ).symm
  have hsolvH : Group.IsSolvable H := by
    have _ : Group.IsNilpotent H := hnil
    infer_instance
  let q : L →* L ⧸ H1 := QuotientGroup.mk' H1
  have hcompQuot :
      (H.map q).IsComplement' (W1.map q) :=
    isComplement'_map_mk'_of_le_isComplement' H W1 H1 hH1_le_H hcomp
  have hHmap_ne : H.map q ≠ ⊥ := by
    intro hbot
    apply hH_not_le_H1
    intro h hhH
    have hhq_bot : q h ∈ (⊥ : Subgroup (L ⧸ H1)) := by
      rw [← hbot]
      exact ⟨h, hhH, rfl⟩
    have hhq_one : q h = 1 := by
      simpa using hhq_bot
    exact (QuotientGroup.eq_one_iff (N := H1) h).mp hhq_one
  have hW1map_card : Nat.card (W1.map q) = Nat.card W1 :=
    natCard_map_mk'_eq_of_le_isComplement' H W1 H1 hH1_le_H hcomp
  have hW1map_ne : W1.map q ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card (W1.map q) = 1 := by
      simp [hbot]
    exact hW1card_ne (hW1map_card ▸ hcard1)
  refine ⟨by infer_instance, hH1_le_H, hHnorm, W1.map q, hcompQuot,
    hHmap_ne, hW1map_ne, ?_⟩
  intro r hr
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyElem :
      y ∈ elementCentralizerIn (H.map q) (r : L ⧸ H1) := by
    simpa [q, H1, Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hy
  rcases r.property with ⟨w, hwW1, hwq⟩
  have hw_sub_ne : (⟨w, hwW1⟩ : W1) ≠ 1 := by
    intro hwone
    apply hr
    apply Subtype.ext
    calc
      (r : L ⧸ H1) = q w := hwq.symm
      _ = 1 := by
        have hwoneL : w = 1 := congrArg Subtype.val hwone
        simp [q, hwoneL]
  let R0 : Subgroup L := Subgroup.zpowers w
  have hR0_le_W1 : R0 ≤ W1 := by
    exact (Subgroup.zpowers_le).2 hwW1
  have hR0normH : R0 ≤ Subgroup.normalizer (H : Set L) := by
    exact hR0_le_W1.trans (Subgroup.le_normalizer_of_normal (H := H))
  have hR0card_dvd_W1 : Nat.card R0 ∣ Nat.card W1 := by
    rw [← natCard_subgroupOf_eq R0 W1 hR0_le_W1]
    exact Subgroup.card_subgroup_dvd_card (R0.subgroupOf W1)
  have hcopHR0 : Nat.Coprime (Nat.card H) (Nat.card R0) :=
    Nat.Coprime.of_dvd_right hR0card_dvd_W1 hcopHW1
  have hH1inv : ∀ r0 : R0, ∀ x ∈ H1, (r0 : L) * x * (r0 : L)⁻¹ ∈ H1 := by
    intro r0 x hx
    exact (inferInstance : H1.Normal).conj_mem x hx (r0 : L)
  have hcentSubQuot :
      subgroupCentralizerIn (H.map q) (R0.map q) =
        (subgroupCentralizerIn H R0).map q :=
    subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
      H R0 H1 hR0normH hsolvH hcopHR0 hH1inv
  have hySub :
      y ∈ subgroupCentralizerIn (H.map q) (R0.map q) := by
    refine ⟨hyElem.1, ?_⟩
    change y ∈ Subgroup.centralizer
      ((R0.map q : Subgroup (L ⧸ H1)) : Set (L ⧸ H1))
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hz with ⟨a, haR0, haz⟩
    rcases Subgroup.mem_zpowers_iff.mp haR0 with ⟨n, hn⟩
    have hcomm_r : y * (r : L ⧸ H1) = (r : L ⧸ H1) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyElem.2
    have hcomm_qw : Commute y (q w) := by
      change y * q w = q w * y
      rw [hwq]
      exact hcomm_r
    have hcomm_qa : Commute y (q a) := by
      rw [← hn]
      simpa [q] using hcomm_qw.zpow_right n
    calc
      z * y = q a * y := by rw [haz]
      _ = y * q a := hcomm_qa.eq.symm
      _ = y * z := by rw [haz]
  have hymap : y ∈ (subgroupCentralizerIn H R0).map q := by
    simpa [hcentSubQuot] using hySub
  rcases hymap with ⟨z, hzcent, hzy⟩
  have hcent_w : elementCentralizerIn H w = W2 := by
    simpa [Section2.centralizerIn, Section2.elementCentralizer,
      elementCentralizerIn] using hcentW1 ⟨w, hwW1⟩ hw_sub_ne
  have hzElem : z ∈ elementCentralizerIn H w := by
    refine ⟨hzcent.1, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcomm :
        w * z = z * w :=
      Subgroup.mem_centralizer_iff.mp hzcent.2 w (Subgroup.mem_zpowers w)
    exact hcomm.symm
  have hzW2 : z ∈ W2 := by
    simpa [hcent_w] using hzElem
  have hzH1 : z ∈ H1 := hW2comm hzW2
  have hy_eq_one : y = 1 := by
    calc
      y = q z := hzy.symm
      _ = 1 := by
        simpa [q] using (QuotientGroup.eq_one_iff (N := H1) z).2 hzH1
  simp [hy_eq_one]


public theorem theorem_10_10_source_typeV_core_frobeniusQuotient_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    Section6.frobeniusQuotientWithKernel
      (derivedSubgroup M) ⁅derivedSubgroup M, derivedSubgroup M⁆ := by
  have h42 : Section4.hypothesis_4_2_statement
      (derivedSubgroup M)
      (W1.subgroupOf M)
      (W2.subgroupOf M)
      ((W1 ⊔ W2).subgroupOf M) :=
    hypothesis_4_2_of_hypothesis_10_1_supported_data _h10
  have hDne : derivedSubgroup M ≠ ⊥ := by
    have hlt : (section16SecondDerivedSubgroup M).subgroupOf M < derivedSubgroup M :=
      typePDefinitionData_secondDerived_lt_derivedSubgroup _hP
    intro hbot
    rw [hbot] at hlt
    exact (not_lt_of_ge bot_le) hlt
  have hDnil : Group.IsNilpotent (derivedSubgroup M) :=
    theorem_10_10_nilpotent_derivedSubgroup_of_typeP_bot _hP
  have hW2comm :
      W2.subgroupOf M ≤ ⁅derivedSubgroup M, derivedSubgroup M⁆ :=
    theorem_10_10_typeP_W2_subgroupOf_le_derived_commutator _hP
  exact theorem_10_10_frobeniusQuotient_commutator_of_hypothesis_4_2
    h42 hDne hDnil hW2comm


public theorem theorem_10_10_source_typeV_cyclicCore_frobeniusQuotient_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2 (section16HatW W1 W2) S τ) :
    Section6.frobeniusQuotientWithKernel
      (derivedSubgroup M) ⁅derivedSubgroup M, derivedSubgroup M⁆ :=
  theorem_10_10_source_typeV_core_frobeniusQuotient_source_supported
    _hP _hpMF _hCyclic _h10


public theorem theorem_10_10_source_typeV_cyclicCore_section6_payload_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ ∧
      Section6.nonabelianPQuotient
        (⊥ : Subgroup M) (derivedSubgroup M) p.val := by
  have h64 :
      Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ :=
    theorem_10_10_hypothesis_6_4_commutator_of_frobenius_supported
      _hP _h10
      (theorem_10_10_source_typeV_cyclicCore_frobeniusQuotient_source_supported
        _hP _hpMF _hCyclic _h10)
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data _h10
  rcases
      Section6.theorem_6_5_b (derivedSubgroup M) (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ S S τ h64 hSbot _hnot with
    ⟨q, hqQ⟩
  have hqPrime : Nat.Prime q := by
    rcases hqQ with
      ⟨_hbotD, _hbotNormD, _hbotNorm, _hDnorm, hqPrime, _hqgroup,
        _hnoncomm⟩
    exact hqPrime
  let qPrime : Nat.Primes := ⟨q, hqPrime⟩
  have hq_eq_p : qPrime = p :=
    theorem_10_10_nonabelianPQuotient_prime_eq_of_typeP_bot_cyclic_core
      _hP _hCyclic (q := qPrime) (by simpa [qPrime] using hqQ)
  have hq_val : q = p.val :=
    congrArg (fun r : Nat.Primes => r.val) hq_eq_p
  exact ⟨h64, by simpa [hq_val] using hqQ⟩


public theorem theorem_10_10_source_typeV_cyclicCore_coherent_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hCyclicCore :
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
        Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ) :
    Section6.coherentFamily S τ := by
  by_contra hnot
  rcases _hCyclicCore with ⟨p, hpMF, hW1div, hCyclic⟩
  rcases theorem_10_10_source_typeV_cyclicCore_section6_payload_source_supported
      _hP hpMF hCyclic _h10 hnot with
    ⟨h64, hpQ⟩
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data _h10
  have hnotDiv :
      ¬ (derivedSubgroup M).relIndex (⊤ : Subgroup M) ∣ p.val - 1 :=
    Section6.theorem_6_5_c (derivedSubgroup M) (⊥ : Subgroup M)
      ⁅derivedSubgroup M, derivedSubgroup M⁆ S S τ h64 hSbot hnot
      p.val hpQ
  have hindexF :
      (derivedSubgroup M).index = Fintype.card W1 := by
    simpa [Nat.card_eq_fintype_card] using
      derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data _h10
  have hindexComm :
      (commutator M).index = Fintype.card W1 := by
    rw [← derivedSeries_one]
    exact hindexF
  have hindexTop :
      (⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆).index = Fintype.card W1 := by
    simpa [_root_.commutator_def] using hindexComm
  exact hnotDiv (by
    simpa [Subgroup.relIndex_top_right, derivedSubgroup, derivedSeries_one,
      Nat.card_eq_fintype_card, hindexTop] using hW1div)

public theorem theorem_10_10_source_typeV_cyclicCore_case_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hCyclicCore :
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
        Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2
          (section16HatW W1 W2) S τ ∧
          Section6.coherentFamily S τ := by
  rcases theorem_10_10_source_typeV_hypothesis_10_1_supported_source
      _hM _hP (Or.inr (Or.inl _hCyclicCore)) with
    ⟨S, τ, h10⟩
  exact ⟨S, τ, h10,
    theorem_10_10_source_typeV_cyclicCore_coherent_source_supported
      _hP _hCyclicCore h10⟩

public theorem theorem_10_10_odd_prime_of_subgroupPrimeSet
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {H : Subgroup G}
    {p : Nat.Primes}
    (hpH : p ∈ subgroupPrimeSet H) :
    Odd p.val := by
  have hpHcard : p.val ∣ Nat.card H := by
    simpa [subgroupPrimeSet] using hpH
  have hpG : p.val ∣ Nat.card G :=
    hpHcard.trans (Subgroup.card_subgroup_dvd_card H)
  exact Odd.of_dvd_nat IsMinCE.odd_order hpG

public theorem theorem_10_10_odd_card_W1_of_typeP
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    Odd (Nat.card W1) := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, hW1Hall, _hCompM, _hUle, _hUnil,
      _hW1norm, _hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hNormalizer⟩
  rcases hW1Hall with ⟨hW1M, _hHallW1⟩
  have hW1dvdG : Nat.card W1 ∣ Nat.card G :=
    (Subgroup.card_dvd_of_le hW1M).trans
      (Subgroup.card_subgroup_dvd_card M)
  exact Odd.of_dvd_nat IsMinCE.odd_order hW1dvdG

public theorem theorem_10_10_W1_card_gt_one_of_typeP
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    1 < Nat.card W1 := by
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1Hall, _hCompM, _hUle, _hUnil,
      _hW1norm, _hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hNormalizer⟩
  exact (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne

public theorem theorem_10_10_W2_eq_secondDerived_of_card
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    {p : Nat.Primes}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hSecondCard :
      Nat.card (ambientDerivedSubgroup (ambientDerivedSubgroup M)) = p.val) :
    W2 = ambientDerivedSubgroup (ambientDerivedSubgroup M) := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hCompM, _hUle, _hUnil,
      _hW1norm, _hCompD, _hMFnotCyclic, _hSecondLe, _hFittingEq,
      _hFittingLe, hW2le, _hW2cyc, hW2ne, _hCentralizer,
      _hNormalizer⟩
  have hW2Second : W2 ≤ section16SecondDerivedSubgroup M := by
    intro x hx
    exact (hW2le hx).2
  have hW2card_dvd_p : Nat.card W2 ∣ p.val := by
    have hdiv : Nat.card W2 ∣ Nat.card (section16SecondDerivedSubgroup M) :=
      Subgroup.card_dvd_of_le hW2Second
    have hSecondCard' : Nat.card (section16SecondDerivedSubgroup M) = p.val := by
      simpa [section16SecondDerivedSubgroup] using hSecondCard
    have hSecondCardF : Fintype.card (section16SecondDerivedSubgroup M) = p.val := by
      simpa [Nat.card_eq_fintype_card] using hSecondCard'
    simpa [Nat.card_eq_fintype_card, hSecondCardF] using hdiv
  have hW2card_ne_one : Nat.card W2 ≠ 1 := by
    intro hcard
    exact hW2ne ((Subgroup.card_eq_one (H := W2)).1 hcard)
  have hW2card_eq_p : Nat.card W2 = p.val := by
    rcases p.property.eq_one_or_self_of_dvd (Nat.card W2) hW2card_dvd_p with
      hcard | hcard
    · exact False.elim (hW2card_ne_one hcard)
    · exact hcard
  have hcard_ge :
      Nat.card (section16SecondDerivedSubgroup M) ≤ Nat.card W2 := by
    have hSecondCard' : Nat.card (section16SecondDerivedSubgroup M) = p.val := by
      simpa [section16SecondDerivedSubgroup] using hSecondCard
    rw [hSecondCard', hW2card_eq_p]
  simpa [section16SecondDerivedSubgroup] using
    Subgroup.eq_of_le_of_card_ge hW2Second hcard_ge

public theorem theorem_10_10_secondDerived_eq_center_and_card_of_noncomm_p3
    {G : Type u}
    [Group G]
    [Finite G]
    {H : Subgroup G}
    {p : Nat.Primes}
    (hpgroup : IsPGroup p.val H)
    (hnoncomm : ¬ IsMulCommutative H)
    (hHcard : Nat.card H = p.val ^ 3) :
    ambientDerivedSubgroup H = (Subgroup.center H).map H.subtype ∧
      Nat.card (ambientDerivedSubgroup H) = p.val := by
  classical
  have _ : Fact p.val.Prime := ⟨p.property⟩
  let _ : Fact (IsPGroup p.val H) := ⟨hpgroup⟩
  have hp : Nat.Prime p.val := p.property
  have hHnontriv : Nontrivial H := by
    have hcard_gt : 1 < Nat.card H := by
      rw [hHcard]
      exact one_lt_pow₀ hp.one_lt (by decide)
    exact Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  let _ : Nontrivial H := hHnontriv
  have hclass2 : NilpotencyClassLe 2 H :=
    nilpotencyClassLe_of_card_le_p_cubed (R := H) (p := p.val) (by rw [hHcard])
  have hcomm_center : commutator H ≤ Subgroup.center H :=
    commutator_le_center_of_le_upperCentralSeries_two (G := H) (⊤ : Subgroup H)
      (by simpa [hclass2])
  have hcenter_ne_top : Subgroup.center H ≠ ⊤ := by
    intro htop
    apply hnoncomm
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxcent : x ∈ Subgroup.center H := by simp [htop]
    exact (Subgroup.mem_center_iff.mp hxcent y).symm
  have hcenter_lt_top : Subgroup.center H < (⊤ : Subgroup H) :=
    lt_of_le_of_ne le_top hcenter_ne_top
  have hcenter_card_lt : Nat.card (Subgroup.center H) < p.val ^ 3 := by
    have hHcardF : Fintype.card H = p.val ^ 3 := by
      simpa [Nat.card_eq_fintype_card] using hHcard
    have hlt := natCard_lt_of_subgroup_lt_local (G := H)
      (H := Subgroup.center H) (K := (⊤ : Subgroup H)) hcenter_lt_top
    simpa [Nat.card_eq_fintype_card, hHcardF] using hlt
  have hcenter_p : IsPGroup p.val (Subgroup.center H) :=
    hpgroup.to_subgroup (Subgroup.center H)
  obtain ⟨m, hm⟩ := hcenter_p.exists_card_eq
  have hm_pos : 0 < m := by
    have hcenter_nontriv : Nontrivial (Subgroup.center H) :=
      IsPGroup.center_nontrivial (p := p.val) (G := H) (hG := hpgroup)
    have hcard_gt_one : 1 < Nat.card (Subgroup.center H) :=
      Finite.one_lt_card_iff_nontrivial.mpr hcenter_nontriv
    rw [hm] at hcard_gt_one
    by_contra hm_zero
    have : m = 0 := by omega
    simp [this] at hcard_gt_one
  have hm_lt_three : m < 3 := by
    rw [hm] at hcenter_card_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hcenter_card_lt
  have hm_le_two : m ≤ 2 := by omega
  have hm_eq_one : m = 1 := by
    by_contra hm_ne_one
    have hm_eq_two : m = 2 := by omega
    have hcenter_card_sq : Nat.card (Subgroup.center H) = p.val ^ 2 := by
      simpa [hm_eq_two] using hm
    have hquot_card : Nat.card (H ⧸ Subgroup.center H) = p.val := by
      have hmul :
          Nat.card (H ⧸ Subgroup.center H) * p.val ^ 2 = p.val * p.val ^ 2 := by
        calc
          Nat.card (H ⧸ Subgroup.center H) * p.val ^ 2
              = Nat.card (H ⧸ Subgroup.center H) * Nat.card (Subgroup.center H) := by
                  rw [hcenter_card_sq]
          _ = Nat.card H := by
                simpa using
                  (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := H)
                    (s := Subgroup.center H)).symm
          _ = p.val ^ 3 := hHcard
          _ = p.val * p.val ^ 2 := by ring_nf
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hmul
    have hquot_cyc : IsCyclic (H ⧸ Subgroup.center H) :=
      isCyclic_of_prime_card (α := H ⧸ Subgroup.center H) hquot_card
    let _ : IsCyclic (H ⧸ Subgroup.center H) := hquot_cyc
    apply hnoncomm
    exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center H))
      (by simp [QuotientGroup.ker_mk'])
  have hcenter_card : Nat.card (Subgroup.center H) = p.val := by
    simpa [hm_eq_one] using hm
  have hder_le_center : derivedSubgroup H ≤ Subgroup.center H := by
    change derivedSeries H 1 ≤ Subgroup.center H
    rw [derivedSeries_one]
    exact hcomm_center
  have hder_ne_bot : derivedSubgroup H ≠ ⊥ := by
    intro hder_bot
    apply hnoncomm
    apply (_root_.commutator_eq_bot_iff H).mp
    rw [← derivedSeries_one]
    exact hder_bot
  have hcenter_le_der : Subgroup.center H ≤ derivedSubgroup H :=
    center_le_of_le_center_ne_bot_of_prime_center_local
      (K := H) (q := p.val) (hcenter := hcenter_card)
      hder_le_center hder_ne_bot
  have hder_eq_center : derivedSubgroup H = Subgroup.center H :=
    le_antisymm hder_le_center hcenter_le_der
  have hcomm_eq_center : commutator H = Subgroup.center H := by
    rw [← derivedSeries_one]
    exact hder_eq_center
  have hCenter :
      ambientDerivedSubgroup H = (Subgroup.center H).map H.subtype := by
    simp [ambientDerivedSubgroup, hcomm_eq_center]
  have hCenterCard : Nat.card ((Subgroup.center H).map H.subtype) = p.val := by
    calc
      Nat.card ((Subgroup.center H).map H.subtype) =
          Nat.card (Subgroup.center H) := by
        exact Subgroup.card_map_of_injective
          (K := Subgroup.center H) (f := H.subtype) H.subtype_injective
      _ = p.val := hcenter_card
  exact ⟨hCenter, by simpa [hCenter] using hCenterCard⟩

public theorem theorem_10_10_secondDerivedSubgroup_subgroupOf_eq_commutator
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    (section16SecondDerivedSubgroup M).subgroupOf M =
      ⁅derivedSubgroup M, derivedSubgroup M⁆ := by
  ext x
  constructor
  · intro hx
    have hxD : x ∈ derivedSubgroup M :=
      secondDerivedSubgroup_subgroupOf_le_derived M hx
    have hxSecondD :
        (⟨x, hxD⟩ : derivedSubgroup M) ∈
          ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
            (derivedSubgroup M) := by
      change x ∈ (section16SecondDerivedSubgroup M).subgroupOf M
      exact hx
    have hxCommD : (⟨x, hxD⟩ : derivedSubgroup M) ∈
        derivedSubgroup (derivedSubgroup M) := by
      rw [← secondDerivedSubgroup_subgroupOf_derived_eq M]
      exact hxSecondD
    have hxMap :
        (x : M) ∈ (derivedSubgroup (derivedSubgroup M)).map
          (derivedSubgroup M).subtype :=
      ⟨⟨x, hxD⟩, hxCommD, rfl⟩
    change (x : M) ∈ (commutator (derivedSubgroup M)).map
        (derivedSubgroup M).subtype at hxMap
    rw [← Subgroup.map_subtype_commutator (H := derivedSubgroup M)]
    exact hxMap
  · intro hx
    have hxD : x ∈ derivedSubgroup M :=
      (Subgroup.commutator_le_left (H₁ := derivedSubgroup M)
        (H₂ := derivedSubgroup M)) hx
    rw [← Subgroup.map_subtype_commutator (H := derivedSubgroup M)] at hx
    rcases hx with ⟨y, hyComm, hyx⟩
    have hySecond :
        y ∈ ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
          (derivedSubgroup M) := by
      rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
      exact hyComm
    have hy_eq : y = (⟨x, hxD⟩ : derivedSubgroup M) := by
      apply Subtype.ext
      exact hyx
    rw [hy_eq] at hySecond
    change x ∈ (section16SecondDerivedSubgroup M).subgroupOf M at hySecond
    exact hySecond

public theorem theorem_10_10_secondDerived_relIndex_eq_commutator
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    (ambientDerivedSubgroup (ambientDerivedSubgroup M)).relIndex
        (ambientDerivedSubgroup M) =
      ⁅derivedSubgroup M, derivedSubgroup M⁆.relIndex
        (derivedSubgroup M) := by
  have hamb :
      ((section16SecondDerivedSubgroup M).subgroupOf M).relIndex
          ((ambientDerivedSubgroup M).subgroupOf M) =
        (section16SecondDerivedSubgroup M).relIndex
          (ambientDerivedSubgroup M) := by
    exact Subgroup.relIndex_subgroupOf
      (H := section16SecondDerivedSubgroup M)
      (K := ambientDerivedSubgroup M) (L := M)
      (section12_ambientDerivedSubgroup_le (E := M))
  rw [section12_ambientDerivedSubgroup_subgroupOf_eq] at hamb
  rw [theorem_10_10_secondDerivedSubgroup_subgroupOf_eq_commutator] at hamb
  simpa [section16SecondDerivedSubgroup] using hamb.symm

public theorem theorem_10_10_isMulCommutative_of_mulEquiv
    {A B : Type*}
    [Group A]
    [Group B]
    (e : A ≃* B)
    (hcomm : IsMulCommutative A) :
    IsMulCommutative B := by
  have _ : IsMulCommutative A := hcomm
  refine ⟨⟨fun b₁ b₂ => ?_⟩⟩
  apply e.symm.injective
  simpa using hcomm.is_comm.comm (e.symm b₁) (e.symm b₂)

public theorem theorem_10_10_not_isMulCommutative_ambientDerived_of_nonabelianPQuotient
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {p : ℕ}
    (hpQ :
      Section6.nonabelianPQuotient (⊥ : Subgroup M) (derivedSubgroup M) p) :
    ¬ IsMulCommutative (ambientDerivedSubgroup M) := by
  intro hcommAmbient
  rcases hpQ with
    ⟨_hbotD, _hbotNormD, _hbotNorm, _hDnorm, _hpprime, _hpgroup,
      hquotNoncomm⟩
  have hDcomm : IsMulCommutative (derivedSubgroup M) := by
    let eAmbientSub :
        ambientDerivedSubgroup M ≃*
          (ambientDerivedSubgroup M).subgroupOf M :=
      (Subgroup.subgroupOfEquivOfLe
        (section12_ambientDerivedSubgroup_le (E := M))).symm
    let eSubD :
        (ambientDerivedSubgroup M).subgroupOf M ≃* derivedSubgroup M :=
      MulEquiv.subgroupCongr
        (section12_ambientDerivedSubgroup_subgroupOf_eq (E := M))
    exact theorem_10_10_isMulCommutative_of_mulEquiv
      (eAmbientSub.trans eSubD) hcommAmbient
  have hbot_sub :
      (⊥ : Subgroup M).subgroupOf (derivedSubgroup M) =
        (⊥ : Subgroup (derivedSubgroup M)) := by
    exact Subgroup.bot_subgroupOf (H := derivedSubgroup M)
  let eQuot :
      derivedSubgroup M ⧸
          (⊥ : Subgroup M).subgroupOf (derivedSubgroup M) ≃*
        derivedSubgroup M :=
    (QuotientGroup.quotientMulEquivOfEq hbot_sub).trans
      QuotientGroup.quotientBot
  have hquotComm :
      IsMulCommutative
        (derivedSubgroup M ⧸
          (⊥ : Subgroup M).subgroupOf (derivedSubgroup M)) :=
    theorem_10_10_isMulCommutative_of_mulEquiv eQuot.symm hDcomm
  exact hquotNoncomm hquotComm


public theorem theorem_10_10_noncomm_ambientDerived_of_section6_hypothesis_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h64 :
      Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ)
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hnot : ¬ Section6.coherentFamily S τ) :
    ¬ IsMulCommutative (ambientDerivedSubgroup M) := by
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10
  rcases
      Section6.theorem_6_5_b (derivedSubgroup M) (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ S S τ h64 hSbot hnot with
    ⟨q, hq⟩
  exact
    theorem_10_10_not_isMulCommutative_ambientDerived_of_nonabelianPQuotient hq

public theorem theorem_10_10_ambientDerived_card_eq_cube_prime_of_internal_frobenius_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (hCyclic : IsCyclic (section10PPrimeCore p MF))
    (h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (hFrobInternal :
      Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆)
    (hnot : ¬ Section6.coherentFamily S τ) :
    Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 := by
  have h64 :
      Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ :=
    theorem_10_10_hypothesis_6_4_commutator_of_frobenius_supported
      hP h10 hFrobInternal
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data h10
  rcases
      Section6.theorem_6_5_b (derivedSubgroup M) (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ S S τ h64 hSbot hnot with
    ⟨q, hqQ⟩
  have hqPrime : Nat.Prime q := by
    rcases hqQ with
      ⟨_hbotD, _hbotNormD, _hbotNorm, _hDnorm, hqPrime, _hqgroup,
        _hnoncomm⟩
    exact hqPrime
  let qPrime : Nat.Primes := ⟨q, hqPrime⟩
  have hq_eq_p : qPrime = p :=
    theorem_10_10_nonabelianPQuotient_prime_eq_of_typeP_bot_cyclic_core
      hP hCyclic (q := qPrime) (by simpa [qPrime] using hqQ)
  have hq_val : q = p.val :=
    congrArg (fun r : Nat.Primes => r.val) hq_eq_p
  have hpQ :
      Section6.nonabelianPQuotient
        (⊥ : Subgroup M) (derivedSubgroup M) p.val := by
    simpa [hq_val] using hqQ
  have hpD : IsPGroup p.val (derivedSubgroup M) :=
    theorem_10_10_nonabelianPQuotient_bot_isPGroup hpQ
  have hMF_eq_D : MF = ambientDerivedSubgroup M :=
    theorem_10_10_typeP_bot_mf_eq_derived hP
  have hpMF : IsPGroup p.val MF :=
    theorem_10_10_isPGroup_mf_of_internal_derived hMF_eq_D hpD
  have hcore15 : section15PCoreIn p MF = MF :=
    theorem_10_10_section15PCoreIn_eq_self_of_isPGroup hpMF
  have hcore16 : section16PCoreIn p MF = MF := by
    simpa [section16PCoreIn, section15PCoreIn] using hcore15
  have hMFcard : Nat.card MF = p.val ^ 3 := by
    simpa [hcore16] using hpCoreCard
  simpa [hMF_eq_D] using hMFcard

public theorem theorem_10_10_source_typeV_cubeCore_section6_payload_fields_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 := by
  have hFrobInternal :
      Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ :=
    theorem_10_10_source_typeV_core_frobeniusQuotient_source_supported
      _hP _hpMF _hCyclic _h10
  have hHcard :
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 :=
    theorem_10_10_ambientDerived_card_eq_cube_prime_of_internal_frobenius_supported
      _hP _hpCoreCard _hCyclic _h10 hFrobInternal _hnot
  exact ⟨hFrobInternal, hHcard⟩

public theorem theorem_10_10_source_typeV_cubeCore_section6_payload_core_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 := by
  rcases theorem_10_10_source_typeV_cubeCore_section6_payload_fields_source_supported
      _hP _hpMF _hpCoreCard _hCyclic _h10 _hnot with
    ⟨hFrobInternal, hHcard⟩
  have h64 :
      Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ :=
    theorem_10_10_hypothesis_6_4_commutator_of_frobenius_supported
      _hP _h10 hFrobInternal
  exact ⟨hFrobInternal, h64, hHcard⟩

public theorem theorem_10_10_source_typeV_cubeCore_section6_payload_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      Section6.hypothesis_6_4_statement
        (derivedSubgroup M)
        (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆
        S τ ∧
      ¬ IsMulCommutative (ambientDerivedSubgroup M) ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 := by
  rcases theorem_10_10_source_typeV_cubeCore_section6_payload_core_source_supported
      _hP _hpMF _hpCoreCard _hCyclic _h10 _hnot with
    ⟨hFrob, h64, hHcard⟩
  have hnoncomm :
      ¬ IsMulCommutative (ambientDerivedSubgroup M) :=
    theorem_10_10_noncomm_ambientDerived_of_section6_hypothesis_supported
      h64 _h10 _hnot
  exact ⟨hFrob, h64, hnoncomm, hHcard⟩

public theorem theorem_10_10_source_typeV_cubeCore_reduction_structural_payload_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      ¬ IsMulCommutative (ambientDerivedSubgroup M) ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 ∧
      (ambientDerivedSubgroup (ambientDerivedSubgroup M)).relIndex
          (ambientDerivedSubgroup M) ≤
        4 * (Nat.card W1) ^ 2 + 1 := by
  rcases theorem_10_10_source_typeV_cubeCore_section6_payload_source_supported
      _hP _hpMF _hpCoreCard _hCyclic _h10 _hnot with
    ⟨hFrob, h64, hnoncomm, hHcard⟩
  have hSbot : Section6.inducedKernelFamily (derivedSubgroup M) ⊥ S :=
    inducedKernelFamily_bot_of_hypothesis_10_1_supported_data _h10
  rcases
      Section6.theorem_6_5_a (derivedSubgroup M) (⊥ : Subgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ S S τ h64 hSbot _hnot with
    ⟨_hchief, hboundInternal⟩
  have hindex :
      (derivedSubgroup M).index = Nat.card W1 :=
    derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data _h10
  have hindexF :
      (derivedSubgroup M).index = Fintype.card W1 := by
    simpa [Nat.card_eq_fintype_card] using hindex
  have hindexComm :
      (commutator M).index = Fintype.card W1 := by
    rw [← derivedSeries_one]
    exact hindexF
  have hbound :
      (ambientDerivedSubgroup (ambientDerivedSubgroup M)).relIndex
          (ambientDerivedSubgroup M) ≤
        4 * (Nat.card W1) ^ 2 + 1 := by
    simpa [theorem_10_10_secondDerived_relIndex_eq_commutator M, hindexComm]
      using hboundInternal
  exact ⟨hFrob, hnoncomm, hHcard, hbound⟩

public theorem theorem_10_10_source_typeV_cubeCore_reduction_structural_core_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    ambientDerivedSubgroup (ambientDerivedSubgroup M) =
        (Subgroup.center (ambientDerivedSubgroup M)).map
          (ambientDerivedSubgroup M).subtype ∧
      Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      Nat.card (ambientDerivedSubgroup (ambientDerivedSubgroup M)) = p.val ∧
      IsPGroup p.val (ambientDerivedSubgroup M) ∧
      ¬ IsMulCommutative (ambientDerivedSubgroup M) ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 ∧
      (ambientDerivedSubgroup (ambientDerivedSubgroup M)).relIndex
          (ambientDerivedSubgroup M) ≤
        4 * (Nat.card W1) ^ 2 + 1 := by
  rcases theorem_10_10_source_typeV_cubeCore_reduction_structural_payload_source_supported
      _hP _hpMF _hpCoreCard _hCyclic _h10 _hnot with
    ⟨hFrob, hnoncomm, hHcard, hbound⟩
  have hpgroup : IsPGroup p.val (ambientDerivedSubgroup M) :=
    IsPGroup.of_card (n := 3) hHcard
  rcases
    theorem_10_10_secondDerived_eq_center_and_card_of_noncomm_p3
      (G := G) (H := ambientDerivedSubgroup M) (p := p)
      hpgroup hnoncomm hHcard with
    ⟨hCenter, hHprimeCard⟩
  exact ⟨hCenter, hFrob, hHprimeCard, hpgroup, hnoncomm,
    hHcard, hbound⟩

public theorem theorem_10_10_source_typeV_cubeCore_reduction_structural_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    ambientDerivedSubgroup (ambientDerivedSubgroup M) =
        (Subgroup.center (ambientDerivedSubgroup M)).map
          (ambientDerivedSubgroup M).subtype ∧
      W2 = ambientDerivedSubgroup (ambientDerivedSubgroup M) ∧
      Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      Nat.card (ambientDerivedSubgroup (ambientDerivedSubgroup M)) = p.val ∧
      IsPGroup p.val (ambientDerivedSubgroup M) ∧
      ¬ IsMulCommutative (ambientDerivedSubgroup M) ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 ∧
      (ambientDerivedSubgroup (ambientDerivedSubgroup M)).relIndex
          (ambientDerivedSubgroup M) ≤
        4 * (Nat.card W1) ^ 2 + 1 := by
  rcases theorem_10_10_source_typeV_cubeCore_reduction_structural_core_source_supported
      _hP _hpMF _hpCoreCard _hCyclic _h10 _hnot with
    ⟨hCenter, hFrob, hHprimeCard, hpgroup, hnoncomm,
      hHcard, hbound⟩
  exact ⟨hCenter,
    theorem_10_10_W2_eq_secondDerived_of_card _hP hHprimeCard,
    hFrob, hHprimeCard, hpgroup, hnoncomm, hHcard, hbound⟩

public theorem theorem_10_10_source_typeV_cubeCore_reduction_fields_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {p : Nat.Primes}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hpMF : p ∈ subgroupPrimeSet MF)
    (_hpCoreCard : Nat.card (section16PCoreIn p MF) = p.val ^ 3)
    (_hCyclic : IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    ambientDerivedSubgroup (ambientDerivedSubgroup M) =
        (Subgroup.center (ambientDerivedSubgroup M)).map
          (ambientDerivedSubgroup M).subtype ∧
      W2 = ambientDerivedSubgroup (ambientDerivedSubgroup M) ∧
      Section6.frobeniusQuotientWithKernel
        (derivedSubgroup M)
        ⁅derivedSubgroup M, derivedSubgroup M⁆ ∧
      Nat.card W2 = p.val ∧
      Odd p.val ∧
      Odd (Nat.card W1) ∧
      1 < Nat.card W1 ∧
      Nat.card (ambientDerivedSubgroup (ambientDerivedSubgroup M)) = p.val ∧
      IsPGroup p.val (ambientDerivedSubgroup M) ∧
      ¬ IsMulCommutative (ambientDerivedSubgroup M) ∧
      Nat.card (ambientDerivedSubgroup M) = p.val ^ 3 ∧
      (ambientDerivedSubgroup (ambientDerivedSubgroup M)).relIndex
          (ambientDerivedSubgroup M) ≤
        4 * (Nat.card W1) ^ 2 + 1 := by
  rcases theorem_10_10_source_typeV_cubeCore_reduction_structural_source_supported
      _hP _hpMF _hpCoreCard _hCyclic _h10 _hnot with
    ⟨hCenter, hW2eq, hFrob, hHprimeCard, hpgroup, hnoncomm,
      hHcard, hbound⟩
  exact ⟨hCenter, hW2eq, hFrob,
    by simpa [hW2eq] using hHprimeCard,
    theorem_10_10_odd_prime_of_subgroupPrimeSet _hpMF,
    theorem_10_10_odd_card_W1_of_typeP _hP,
    theorem_10_10_W1_card_gt_one_of_typeP _hP,
    hHprimeCard, hpgroup, hnoncomm, hHcard, hbound⟩

public theorem theorem_10_10_source_typeV_cubeCore_reduction_source_supported_of_noncoherence
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hCubeCore :
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
        Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
        Nat.card W1 ∣ p.val + 1 ∧
        IsCyclic (section10PPrimeCore p MF))
    (_h10 :
      hypothesis_10_1_supported_data M MF W1 W2
        (section16HatW W1 W2) S τ)
    (_hnot : ¬ Section6.coherentFamily S τ) :
    ∃ H H' : Subgroup G, ∃ p : ℕ,
      typeVReductionData M MF H H' W1 W2 p := by
  rcases _hCubeCore with ⟨p, hpMF, hpCoreCard, hW1div, hCyclic⟩
  rcases theorem_10_10_source_typeV_cubeCore_reduction_fields_source_supported
      _hP hpMF hpCoreCard hCyclic _h10 _hnot with
    ⟨hCenter, hW2eq, hFrob, hW2card, hOddp, hOddW1,
      hW1gt, hHprimeCard, hpgroup, hnoncomm, hHcard, hbound⟩
  let H : Subgroup G := ambientDerivedSubgroup M
  let Hprime : Subgroup G := ambientDerivedSubgroup (ambientDerivedSubgroup M)
  have hM : M ∈ section9MaximalSubgroups G := by
    rcases _h10 with
      ⟨hM, _hType, _hS, _hW1M, _hW2M, _hW12M, _hDade, _h46,
        _hNotation10, _h52⟩
    exact hM
  have hMF : section16MFSubgroup M MF := _hP.1
  have hTypeV : Section8.typeVDefinitionData M MF :=
    ⟨⊥, _, _, _hP, rfl, Or.inr (Or.inr ⟨p, hpMF, hpCoreCard, hW1div, hCyclic⟩)⟩
  have hT6 :
      ∀ A0 A1 : Subgroup G,
        section16PrimeOrderSubgroupOf A0 ⊥ →
          section16PrimeOrderSubgroupOf A1 ⊥ →
            section16ConjugateSubgroupsIn ⊤ A0 A1 →
              ¬ section16ConjugateSubgroupsIn M A0 A1 →
                subgroupCentralizerIn MF A0 = ⊥ ∨
                  subgroupCentralizerIn MF A1 = ⊥ :=
    Section8.sourceTypeP_T6_of_source_typeP hM hMF _hP
  have hCommon : section16TypeCommon M MF ⊥ W1 W2 :=
    Section8.section16TypeCommon_of_source_typeP_with_T6 _hP hT6
  have hAlt : typeVReductionSourceAlternative M MF W1 :=
    Or.inr (Or.inr ⟨p, hpMF, hpCoreCard, hW1div, hCyclic⟩)
  refine ⟨H, Hprime, p.val, ?_⟩
  refine ⟨hMF, hTypeV, hCommon, hAlt, rfl, rfl, ?_, ?_, ?_, ?_,
    p.property, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [H, Hprime] using hCenter
  · dsimp [Hprime, H]
    exact section12_ambientDerivedSubgroup_le
      (G := G) (E := ambientDerivedSubgroup M)
  · simpa [Hprime] using hW2eq
  · exact hFrob
  · simpa using hW2card
  · simpa using hOddp
  · simpa using hOddW1
  · simpa using hW1gt
  · simpa [Hprime] using hHprimeCard
  · simpa [H] using hpgroup
  · simpa [H] using hnoncomm
  · simpa [H] using hHcard
  · exact hW1div
  · simpa [H, Hprime] using hbound

public theorem theorem_10_10_source_typeV_cubeCore_case_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (_hCubeCore :
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
        Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
        Nat.card W1 ∣ p.val + 1 ∧
        IsCyclic (section10PPrimeCore p MF)) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2
            (section16HatW W1 W2) S τ ∧
          (Section6.coherentFamily S τ ∨
            ∃ H H' : Subgroup G, ∃ p : ℕ,
              typeVReductionData M MF H H' W1 W2 p) := by
  rcases theorem_10_10_source_typeV_hypothesis_10_1_supported_source
      _hM _hP (Or.inr (Or.inr _hCubeCore)) with
    ⟨S, τ, h10⟩
  by_cases hcoh : Section6.coherentFamily S τ
  · exact ⟨S, τ, h10, Or.inl hcoh⟩
  · exact ⟨S, τ, h10, Or.inr
      (theorem_10_10_source_typeV_cubeCore_reduction_source_supported_of_noncoherence
        _hP _hCubeCore h10 hcoh)⟩

public theorem theorem_10_10_source_typeV_cases_core_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF ⊥ W1 W2)
    (hAlt :
      section16TISubset (section16NonidentityElements (MF : Set G)) ∨
        (∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
          Nat.card W1 ∣ p.val - 1 ∧ IsCyclic (section10PPrimeCore p MF)) ∨
          ∃ p : Nat.Primes, p ∈ subgroupPrimeSet MF ∧
            Nat.card (section16PCoreIn p MF) = p.val ^ 3 ∧
            Nat.card W1 ∣ p.val + 1 ∧
            IsCyclic (section10PPrimeCore p MF)) :
    ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2
            (section16HatW W1 W2) S τ ∧
          (Section6.coherentFamily S τ ∨
            ∃ H H' : Subgroup G, ∃ p : ℕ,
              typeVReductionData M MF H H' W1 W2 p) := by
  rcases hAlt with hTI | hRest
  · rcases theorem_10_10_source_typeV_ti_case_source_supported hM hP hTI with
      ⟨S, τ, h10, hcoh⟩
    exact ⟨S, τ, h10, Or.inl hcoh⟩
  · rcases hRest with hCyclicCore | hCubeCore
    · rcases theorem_10_10_source_typeV_cyclicCore_case_source_supported
        hM hP hCyclicCore with
        ⟨S, τ, h10, hcoh⟩
      exact ⟨S, τ, h10, Or.inl hcoh⟩
    · exact theorem_10_10_source_typeV_cubeCore_case_source_supported
        hM hP hCubeCore

public theorem theorem_10_10_source_typeV_cases_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hTypeV : Section8.typeVDefinitionData M MF) :
    ∃ W1 W2 : Subgroup G,
      ∃ S : Finset (Section1.ClassFunction M),
      ∃ τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
        hypothesis_10_1_supported_data M MF W1 W2
            (section16HatW W1 W2) S τ ∧
          (Section6.coherentFamily S τ ∨
            ∃ H H' : Subgroup G, ∃ p : ℕ,
              typeVReductionData M MF H H' W1 W2 p) := by
  rcases hTypeV with ⟨U, W1, W2, hP, hUbot, hAlt⟩
  subst U
  rcases theorem_10_10_source_typeV_cases_core_supported hM hP hAlt with
    ⟨S, τ, h10, hcase⟩
  exact ⟨W1, W2, S, τ, h10, hcase⟩

public theorem theorem_10_10_source_bridge_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G] :
    ¬ ∃ M MF : Subgroup G,
      M ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup M MF ∧
        Section8.typeVDefinitionData M MF := by
  intro hTypeV
  rcases hTypeV with ⟨M, MF, hM, _hMF, hTypeV⟩
  rcases theorem_10_10_source_typeV_cases_supported hM hTypeV with
    ⟨W1, W2, S, τ, h10, hcase⟩
  rcases hcase with hcoh | ⟨H, H', p, hred⟩
  · exact theorem_10_8_supported M MF W1 W2 (section16HatW W1 W2) S τ h10 hcoh
  · exact theorem_10_10_no_typeVReduction_of_hypothesis_10_1_supported
      (M := M) (MF := MF) (H := H) (H' := H') (W1 := W1) (W2 := W2)
      (S := S) (τ := τ) (p := p) h10 hred

/-- Proof placeholder for `theorem_10_10_statement`. -/
public theorem theorem_10_10
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    : ¬ ∃ M MF : Subgroup G,
      M ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup M MF ∧
        Section8.typeVDefinitionData M MF :=
  theorem_10_10_source_bridge_supported


end Section10
