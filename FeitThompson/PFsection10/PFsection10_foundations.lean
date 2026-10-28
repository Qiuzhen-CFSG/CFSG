module

public import FeitThompson.PFsection10.Basic
import FeitThompson.PFsection8.SourceTypePBridge
import FeitThompson.PFsection5.PFsection5_8
import FeitThompson.PFsection5.PFsection5_9
import FeitThompson.PFsection7.PFsection7_5
public import FeitThompson.PFsection7.PFsection7_4
public import FeitThompson.PFsection7.PFsection7_6
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

/-! ## (10.2)--(10.10) -/


/-! ## Proof placeholders -/


public theorem theorem_10_2_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_10_1_supported_data M MF W1 W2 V S τ →
      ∃ ξ : Section1.ClassFunction M,
        ξ ∈ S ∧
          Section1.IsIrreducibleCharacterOnGroup ξ ∧
          Section1.degree ξ = (Nat.card W1 : ℂ) := by
  intro h
  classical
  have h10 := h
  rcases h with
    ⟨_hM, hType, hS, _hW1, _hW2, _hW12, _hDade, _h46,
      _hNotation10, _h52⟩
  rcases hType with ⟨_hV, U, hP, _hCases⟩
  let H2M : Subgroup M := (section16SecondDerivedSubgroup M).subgroupOf M
  have hNnormal : (H2M.subgroupOf (derivedSubgroup M)).Normal := by
    dsimp [H2M]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  let _ : (H2M.subgroupOf (derivedSubgroup M)).Normal := hNnormal
  have hcomm :
      IsMulCommutative (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) := by
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    dsimp [H2M]
    change derivedSubgroup (derivedSubgroup M) ≤
      ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
  have _ :
      IsMulCommutative (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) :=
    hcomm
  have hKsolv : Group.IsSolvable (derivedSubgroup M) :=
    typePDefinitionData_derivedSubgroup_solvable hP
  have _ : Group.IsSolvable (derivedSubgroup M) := hKsolv
  have hquotSolv :
      Group.IsSolvable (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) := by
    infer_instance
  have _ : Group.IsSolvable (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) :=
    hquotSolv
  have hH2lt : H2M < derivedSubgroup M :=
    typePDefinitionData_secondDerived_lt_derivedSubgroup hP
  have hquotNontrivial :
      Nontrivial (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    change H2M.subgroupOf (derivedSubgroup M) = ⊤ at htop
    have hle : derivedSubgroup M ≤ H2M := (Subgroup.subgroupOf_eq_top).1 htop
    exact hH2lt.not_ge hle
  have _ : Nontrivial (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) :=
    hquotNontrivial
  rcases Section6.exists_nontrivial_linear_character_of_solvable
      (derivedSubgroup M ⧸ H2M.subgroupOf (derivedSubgroup M)) with ⟨ψ, hψne⟩
  let θ : Section1.ClassFunction (derivedSubgroup M) :=
    Section1.quotientCharacterInflation H2M (derivedSubgroup M) ψ
  have hθirr :
      Section1.IsIrreducibleCharacterOnGroup θ :=
    Section6.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H2M (derivedSubgroup M) ψ
  have hθne :
      θ ≠ Section1.principalCharacter (derivedSubgroup M) :=
    Section6.quotientCharacterInflation_ne_principal_of_ne_one
      H2M (derivedSubgroup M) hψne
  have hθdegree : Section1.degree θ = 1 :=
    Section1.quotientCharacterInflation_degree H2M (derivedSubgroup M) ψ
  have hIndIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF (derivedSubgroup M) θ) := by
    simpa [θ, H2M] using
      typePDefinitionData_inducedCF_secondDerivedQuotient_isIrreducible_supported
        hP h10 ψ hψne
  refine ⟨Section1.inducedCF (derivedSubgroup M) θ, ?_, hIndIrr, ?_⟩
  · exact (hS (Section1.inducedCF (derivedSubgroup M) θ)).mpr
      ⟨θ, hθirr, hθne, rfl⟩
  · rw [Section1.degree_inducedClassFunction, hθdegree]
    rw [derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10]
    simp

public theorem nat_prime_card_of_section10TypeIIPairingData
    {G : Type u}
    [Group G]
    {H : Subgroup G}
    (h : section10TypeIIPairingData H) :
    Nat.Prime (Nat.card H) := by
  rcases h with ⟨p, hp⟩
  rw [hp]
  exact p.property

public theorem subgroupCentralizerIn_ambientDerived_W1_eq_W2_of_source_typeP
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    subgroupCentralizerIn (ambientDerivedSubgroup M) W1 = W2 := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1hall, _hW1comp, _hUleD,
      _hUnil, _hW1norm, _hUcomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2le, _hW2cyc, _hW2ne, hCentralizer, _hNormalizer⟩
  have hD2leD :
      section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
    simpa [section16SecondDerivedSubgroup] using
      (section12_ambientDerivedSubgroup_le (G := G) (E := ambientDerivedSubgroup M))
  have hW2leD : W2 ≤ ambientDerivedSubgroup M := by
    intro y hy
    exact hD2leD (hW2le hy).2
  apply le_antisymm
  · intro y hy
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne with ⟨x, hxne⟩
    have hxW1 : (x : G) ∈ W1 := x.property
    have hxGne : (x : G) ≠ 1 := by
      intro hx
      exact hxne (Subtype.ext hx)
    have hyCentX :
        y ∈ elementCentralizerIn (ambientDerivedSubgroup M) (x : G) := by
      refine ⟨hy.1, ?_⟩
      change y ∈ Subgroup.centralizer ({(x : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = (x : G) := by simpa using hz
      subst z
      exact Subgroup.mem_centralizer_iff.mp hy.2 (x : G) hxW1
    simpa [hCentralizer (x : G) hxW1 hxGne] using hyCentX
  · intro y hyW2
    refine ⟨hW2leD hyW2, ?_⟩
    change y ∈ Subgroup.centralizer (W1 : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxW1
    by_cases hx : x = 1
    · simp [hx]
    · have hyCentX : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
        simpa [hCentralizer x hxW1 hx] using hyW2
      exact Subgroup.mem_centralizer_iff.mp hyCentX.2 x (by simp)

public theorem section10_source_not_typeI_typeII_of_msChoice_tail
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    (hMs : Section8.msChoiceSource M MF Ms)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    ¬ Section8.typeIDefinitionData M MF ∧
      ¬ Section8.typeIIDefinitionData M MF := by
  rcases hTail with hIII | hTail
  · rcases hMs with hI | hII | hIIIbranch | hIV | hV
    · exact False.elim (hI.2.2.1 hIII)
    · exact False.elim (hII.2.2.1 hIII)
    · exact ⟨hIIIbranch.1, hIIIbranch.2.1⟩
    · exact False.elim (hIV.2.2.1 hIII)
    · exact False.elim (hV.2.2.1 hIII)
  · rcases hTail with hIVsrc | hVsrc
    · rcases hMs with hI | hII | hIIIbranch | hIVbranch | hV
      · exact False.elim (hI.2.2.2.1 hIVsrc)
      · exact False.elim (hII.2.2.2.1 hIVsrc)
      · exact False.elim (hIIIbranch.2.2.2.1 hIVsrc)
      · exact ⟨hIVbranch.1, hIVbranch.2.1⟩
      · exact False.elim (hV.2.2.2.1 hIVsrc)
    · rcases hMs with hI | hII | hIIIbranch | hIVbranch | hVbranch
      · exact False.elim (hI.2.2.2.2.1 hVsrc)
      · exact False.elim (hII.2.2.2.2.1 hVsrc)
      · exact False.elim (hIIIbranch.2.2.2.2.1 hVsrc)
      · exact False.elim (hIVbranch.2.2.2.2.1 hVsrc)
      · exact ⟨hVbranch.1, hVbranch.2.1⟩

public theorem section10_caseP1_of_msChoice_tail
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 Uc Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMs : Section8.msChoiceSource M MF Ms)
    (hKU : section16KUData M W1 Uc)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    section16CaseP1 W1 Uc := by
  have hNot :=
    section10_source_not_typeI_typeII_of_msChoice_tail
      (G := G) (M := M) (MF := MF) (Ms := Ms) hMs hTail
  have hProp :=
    proposition_16_1 (G := G) (M := M) (MF := MF) (K := W1) (U := Uc)
      hM hMF hKU
  rcases section16_type_exhaustive_of_maximal (G := G) hM hMF with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact False.elim
      (hNot.1 (Section8.theorem_8_8_typeI_to_source_public
        (G := G) hM hMF hTypeI))
  · exact False.elim
      (hNot.2 (Section8.theorem_8_8_typeII_to_source_public
        (G := G) hM hMF hTypeII))
  · exact ((hProp.2.2.1).mp (Or.inl hTypeIII)).1
  · exact ((hProp.2.2.1).mp (Or.inr hTypeIV)).1
  · exact ((hProp.2.2.2.1).mp hTypeV).1

public theorem section10TypeIIPairingData_of_source_typeP_msChoice_tail
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 Ms : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hMs : Section8.msChoiceSource M MF Ms)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    section10TypeIIPairingData W2 := by
  have hMF : section16MFSubgroup M MF := hP.1
  rcases Section8.sourceTypeP_exists_KUData_of_aligned_complement
      (G := G) hM hP with
    ⟨Uc, hKU⟩
  have hCaseP1 : section16CaseP1 W1 Uc :=
    section10_caseP1_of_msChoice_tail
      (G := G) (M := M) (MF := MF) (W1 := W1) (Uc := Uc) (Ms := Ms)
      hM hMF hMs hKU hTail
  have hC : section16TheoremCConclusions M MF W1 Uc :=
    theorem_16_C (G := G) hM hMF hKU hCaseP1.1
  rcases hC with
    ⟨_hUcomm, _hNormUNotLeM, _hKstarCyclic, _hKstarPos, _hKstarMF,
      _hMFnotCyclic, hDerEq, _hKstarSecond, _Mstar, _hMstarP, _hUnique,
      _hKeq, _hKstarHall, _hPrimeX, _hPrimeY, _hInter, _hProd, _hZcyc,
      _hCase, _hCover, _hHatTI, _hHatEq, _hHatTISubset, _hKprimeIfUne,
      hKstarPrimeIfBot⟩
  have hD_eq_sigma : ambientDerivedSubgroup M = section10Msigma M := by
    simpa [hCaseP1.2] using hDerEq
  have hCentralizer :
      subgroupCentralizerIn (ambientDerivedSubgroup M) W1 = W2 :=
    subgroupCentralizerIn_ambientDerived_W1_eq_W2_of_source_typeP
      (G := G) (M := M) (MF := MF) (U := U) hP
  have hKstar_eq_W2 : section16Kstar M W1 = W2 := by
    simpa [section16Kstar, ← hD_eq_sigma] using hCentralizer
  simpa [section10TypeIIPairingData, hKstar_eq_W2] using
    hKstarPrimeIfBot hCaseP1.2


public theorem section10TypeIIPairingData_of_hypothesis_10_1_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (_h : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    section10TypeIIPairingData W2 := by
  -- Same PF `(10.3)` projection as the old package; the supported Dade record
  -- still carries the source `(8.10)` notation and hence `msChoiceSource`.
  rcases _h with
    ⟨hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, hDade, _h46,
      _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, U, hP, hCases⟩
  rcases hDade with ⟨Ms, _A, _A0, _A1, _H, hNotation, _hA0M, _hτ⟩
  have hMs : Section8.msChoiceSource M MF Ms := hNotation.2.2.1
  have hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF := by
    rcases hCases with hIII | hIV | hV
    · exact Or.inl
        ⟨U, W1, W2, hP, hIII.1, hIII.2.1, hIII.2.2⟩
    · exact Or.inr (Or.inl
        ⟨U, W1, W2, hP, hIV.1, hIV.2.1, hIV.2.2⟩)
    · exact Or.inr (Or.inr
        ⟨U, W1, W2, hP, hV.1, hV.2⟩)
  exact section10TypeIIPairingData_of_source_typeP_msChoice_tail
    (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (Ms := Ms)
    hM hP hMs hTail


public theorem section10BaseRowGaloisData_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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
    (hdata :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ) :
    section10BaseRowGaloisData i0 j0 μ δSign := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _htauA0, hfull⟩
  rcases hfull with ⟨_σM, _xChar, _H_A, _H_A0, _hFull46, hGalois⟩
  exact hGalois

public theorem degree_mu_congruent_mod_card_W1_of_hypothesis_10_1_supported_data_early
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

public theorem degree_mu_eq_base_of_section10FourSixNotationSupportedData_early
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (i : I) (j : J) :
    Section1.degree (μ i j) = Section1.degree (μ i0 j) := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, h45, _h48, _htauA0, _hfull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  rcases h45a with ⟨hres, _hirrX, _hindX⟩
  have hi := congrFun (hres i j) 1
  have h0 := congrFun (hres i0 j) 1
  calc
    Section1.degree (μ i j) = Section1.degree (xChar j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hi
    _ = Section1.degree (μ i0 j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using h0.symm

public theorem deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData_early
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (hdata :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (j : J) :
    δSign j = 1 ∨ δSign j = -1 := by
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hdata with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hσiso, _hσvirt, _hmaps, _hprincipal, _h2A,
      hfull_tail⟩
  rcases hfull_tail with
    ⟨_hωfull, h43b, _h43c, _h43d, _h45a, _h45b, _htauTI, _htauA0,
      _htauIso, _htauPunct, _htauVirt, _hPF39⟩
  have hsignC : Section1.IsSign ((δSign j : ℂ)) := h43b.2.1 j
  rw [Section1.IsSign] at hsignC
  rcases hsignC with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h


public theorem theorem_10_3_mu_entry_irreducible_supported
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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
    (hdata :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ)
    (i : I) (j : J) :
    Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
  rcases hdata with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
      _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _htauA0, hfull⟩
  rcases hfull with ⟨_σM, _xChar, _H_A, _H_A0, hFull, _hGalois⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  exact h43b.2.2.1 i j

public theorem exists_pos_nat_degree_of_irreducible
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ d : ℕ, 0 < d ∧ Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  refine ⟨n, ?_, ?_⟩
  · have _ : Representation.IsIrreducible ρ := hρ
    have _ : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := ρ)
    have hdim_pos : 0 < Module.finrank ℂ (Fin n → ℂ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Fin n → ℂ)).2 inferInstance
    simpa using hdim_pos
  · simpa using (Section1.degree_representation_character ρ)


public theorem theorem_10_3_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G) :
    hypothesis_10_1_supported_data M MF W1 W2 V S τ →
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ →
        ∃ d n : ℕ, ∃ δ : ℤ,
          uniformMuData W1 W2 j0 μ δSign d n δ := by
  intro h10 hdata
  classical
  have hcardI :
      Nat.card I = Nat.card W1 :=
    uniformMu_card_I_eq_card_W1_of_hypothesis_10_1_supported_data h10 hdata
  have hcardJ :
      Nat.card J = Nat.card W2 :=
    uniformMu_card_J_eq_card_W2_of_hypothesis_10_1_supported_data h10 hdata
  have hprime : Nat.Prime (Nat.card W2) :=
    nat_prime_card_of_section10TypeIIPairingData
      (section10TypeIIPairingData_of_hypothesis_10_1_supported h10)
  rcases exists_ne_base_index_of_prime_card j0 hcardJ hprime with ⟨jref, hjref⟩
  rcases exists_pos_nat_degree_of_irreducible
      (theorem_10_3_mu_entry_irreducible_supported hdata i0 jref) with
    ⟨d, hdpos, hddeg⟩
  have hbaseDeg : ∀ j, j ≠ j0 → Section1.degree (μ i0 j) = (d : ℂ) := by
    intro j hj
    have hGalois :=
      section10BaseRowGaloisData_of_section10FourSixNotationSupportedData hdata
    have hdegEq :
        Section1.degree (μ i0 j) = Section1.degree (μ i0 jref) := by
      rcases exists_pos_nat_degree_of_irreducible
          (theorem_10_3_mu_entry_irreducible_supported hdata i0 j) with
        ⟨dj, hdjpos, hdegj⟩
      rcases hGalois j jref hj hjref with ⟨γ, hγ⟩
      have hdegSigned := congrArg Section1.degree hγ
      have hleft :
          Section1.degree ((δSign j : ℂ) • μ i0 j) =
            (δSign j : ℂ) * (dj : ℂ) := by
        calc
          Section1.degree ((δSign j : ℂ) • μ i0 j) =
              (δSign j : ℂ) * Section1.degree (μ i0 j) := rfl
          _ = (δSign j : ℂ) * (dj : ℂ) := by rw [hdegj]
      have hright :
          Section1.degree ((δSign jref : ℂ) • μ i0 jref) =
            (δSign jref : ℂ) * (d : ℂ) := by
        calc
          Section1.degree ((δSign jref : ℂ) • μ i0 jref) =
              (δSign jref : ℂ) * Section1.degree (μ i0 jref) := rfl
          _ = (δSign jref : ℂ) * (d : ℂ) := by rw [hddeg]
      have heq :
          (δSign j : ℂ) * (dj : ℂ) =
            (δSign jref : ℂ) * (d : ℂ) := by
        have hdeg' :
            Section1.degree ((δSign j : ℂ) • μ i0 j) =
              γ (Section1.degree ((δSign jref : ℂ) • μ i0 jref)) := by
          simpa [Section1.degree, Section3.classFunctionGaloisConjugate] using
            hdegSigned
        rw [hleft, hright] at hdeg'
        simpa using hdeg'
      rcases deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData_early
          hdata j with hsj | hsj
      · rcases deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData_early
            hdata jref with hsk | hsk
        · have hdjk : dj = d := by
            have hC : (dj : ℂ) = (d : ℂ) := by
              simpa [hsj, hsk] using heq
            exact_mod_cast hC
          rw [hdegj, hddeg, hdjk]
        · have hC : (dj : ℂ) = - (d : ℂ) := by
            simpa [hsj, hsk] using heq
          exfalso
          have hR : (dj : ℝ) = - (d : ℝ) := by
            have h := congrArg Complex.re hC
            simpa using h
          have hdjR : (0 : ℝ) < dj := by exact_mod_cast hdjpos
          have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
          nlinarith
      · rcases deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData_early
            hdata jref with hsk | hsk
        · have hC : - (dj : ℂ) = (d : ℂ) := by
            simpa [hsj, hsk] using heq
          exfalso
          have hR : - (dj : ℝ) = (d : ℝ) := by
            have h := congrArg Complex.re hC
            simpa using h
          have hdjR : (0 : ℝ) < dj := by exact_mod_cast hdjpos
          have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
          nlinarith
        · have hdjk : dj = d := by
            have hC : (dj : ℂ) = (d : ℂ) := by
              simpa [hsj, hsk] using heq
            exact_mod_cast hC
          rw [hdegj, hddeg, hdjk]
    rw [hdegEq, hddeg]
  have hd : 1 < d := by
    have hneDegree : Section1.degree (μ i0 jref) ≠ 1 := by
      intro hdeg
      have hμirr := theorem_10_3_mu_entry_irreducible_supported hdata i0 jref
      have hker :
          Section1.subgroupInKernel' (μ i0 jref) (derivedSubgroup M) :=
        subgroupInKernel_derivedSubgroup_of_irreducible_degree_one hμirr hdeg
      rcases supportedFourSixData_of_section10FourSixNotationSupportedData hdata with
        ⟨σM, _xChar, _H_A, _H_A0, hSupported⟩
      rcases hSupported with
        ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
          hFullRest⟩
      rcases hFullRest with
        ⟨hω, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
          _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
      have hbase :
          ∃ i, μ i0 jref = μ i j0 := by
        exact ((Section4.proposition_4_4
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
          h46.1 hω h43b h43c).1 (μ i0 jref) hμirr).mp hker
      rcases hbase with ⟨i, hi⟩
      have hpneq : (i0, jref) ≠ (i, j0) := by
        intro hp
        exact hjref (congrArg Prod.snd hp)
      exact h43b.2.2.2.1 (i0, jref) (i, j0) hpneq hi
    have hdne : d ≠ 1 := by
      intro hd1
      apply hneDegree
      rw [hddeg, hd1]
      norm_num
    omega
  rcases degree_mu_congruent_mod_card_W1_of_hypothesis_10_1_supported_data_early
      h10 hdata i0 jref with
    ⟨a, haC⟩
  have hdegC :
      (d : ℂ) =
        (δSign jref : ℂ) + ((a : ℂ) * (Nat.card W1 : ℂ)) :=
    (hbaseDeg jref hjref).symm.trans haC
  have hInt :
      (d : ℤ) = δSign jref + a * (Nat.card W1 : ℤ) := by
    exact_mod_cast hdegC
  have hcardW1_pos : 0 < Nat.card W1 := Nat.card_pos
  have ha_pos : 0 < a := by
    have hcardW1_pos_int : 0 < (Nat.card W1 : ℤ) := by
      exact_mod_cast hcardW1_pos
    rcases deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData_early
        hdata jref with hδ | hδ
    · rw [hδ] at hInt
      have hprod : 0 < a * (Nat.card W1 : ℤ) := by omega
      exact (mul_pos_iff_of_pos_right hcardW1_pos_int).mp hprod
    · rw [hδ] at hInt
      have hprod : 0 < a * (Nat.card W1 : ℤ) := by omega
      exact (mul_pos_iff_of_pos_right hcardW1_pos_int).mp hprod
  let n : ℕ := a.toNat
  have hn : 0 < n := by
    dsimp [n]
    have hne : a.toNat ≠ 0 := by
      intro hzero
      have hle : a ≤ 0 := Int.toNat_eq_zero.mp hzero
      omega
    exact Nat.pos_of_ne_zero hne
  have hnatCast : (n : ℤ) = a := by
    dsimp [n]
    exact Int.toNat_of_nonneg (le_of_lt ha_pos)
  have harith :
      (d : ℤ) = (n : ℤ) * (Nat.card W1 : ℤ) + δSign jref := by
    rw [hnatCast]
    omega
  let δ : ℤ := δSign jref
  have hdeg : ∀ i j, j ≠ j0 → Section1.degree (μ i j) = (d : ℂ) := by
    intro i j hj
    calc
      Section1.degree (μ i j) = Section1.degree (μ i0 j) :=
        degree_mu_eq_base_of_section10FourSixNotationSupportedData_early hdata i j
      _ = (d : ℂ) := hbaseDeg j hj
  have hsign : ∀ j, j ≠ j0 → δSign j = δ := by
    intro j hj
    unfold δ
    have hdegEq :
        Section1.degree (μ i0 j) = Section1.degree (μ i0 jref) := by
      rw [hbaseDeg j hj, hbaseDeg jref hjref]
    have hsignC : ((δSign j : ℂ) = (δSign jref : ℂ)) := by
      rcases hdata with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _h810, _hW, _hA0, _h46,
          _hω, _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, h48, _htauA0, _hfull⟩
      exact (h48 i0 j jref hj hjref hdegEq).2.1
    exact_mod_cast hsignC
  have hδ : δ = 1 ∨ δ = -1 := by
    exact deltaSign_eq_one_or_neg_one_of_section10FourSixNotationSupportedData_early
      hdata jref
  exact ⟨d, n, δ, hcardI, hcardJ, hprime, hd, hδ, hn, hdeg, hsign, harith⟩

public theorem alphaChar_sub_baseRow_eq_sign_smul_fourTenTerm
    {G : Type u}
    [Group G]
    {I J : Type*}
    (μ : I → J → Section1.ClassFunction G)
    (ξ : Section1.ClassFunction G)
    (n : ℕ)
    (δ : ℤ)
    (j0 : J)
    (i i0 : I)
    (j : J)
    (hδsq : ((δ : ℂ) * (δ : ℂ) = 1)) :
    alphaChar μ ξ n δ j0 i j - alphaChar μ ξ n δ j0 i0 j =
      (δ : ℂ) •
        ((δ : ℂ) • μ i j - (δ : ℂ) • μ i0 j - μ i j0 + μ i0 j0) := by
  ext x
  simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hpow : (δ : ℂ) ^ 2 = 1 := by simpa [pow_two] using hδsq
  ring_nf
  simp [hpow]

public theorem isVirtualCharacter_intCast_smul_sec10_base
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

public theorem isVirtualCharacter_natCast_smul_sec10_base
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (n : ℕ)
    (hχ : IsVirtualCharacter χ) :
    IsVirtualCharacter ((n : ℂ) • χ) := by
  simpa using
    isVirtualCharacter_intCast_smul_sec10_base (G := G) (χ := χ) (n : ℤ) hχ

public theorem isVirtualCharacter_finset_sum_sec10_base
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
          (isVirtualCharacter_intCast_smul_sec10_base
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

public theorem alphaChar_isVirtualCharacter_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    (i : I) (j : J) :
    IsVirtualCharacter (alphaChar μ ξ n δ j0 i j) := by
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_data h
  rcases h104a with ⟨_h10, _hNotation, _hξS, hξIrr, _hξDegree, _hUniform⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt⟩
    exact h43b.2.2.1
  have hentry :
      IsVirtualCharacter (μ i j) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμirr i j)
  have hbase :
      IsVirtualCharacter (μ i j0) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμirr i j0)
  have hξ :
      IsVirtualCharacter ξ :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr
  have hδbase :
      IsVirtualCharacter ((δ : ℂ) • μ i j0) :=
    isVirtualCharacter_intCast_smul_sec10_base δ hbase
  have hnξ :
      IsVirtualCharacter ((n : ℂ) • ξ) :=
    isVirtualCharacter_natCast_smul_sec10_base n hξ
  simpa [alphaChar] using
    Section3.isVirtualCharacter_sub
      (Section3.isVirtualCharacter_sub hentry hδbase) hnξ

public theorem alphaChar_tau_isVirtualCharacter_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I} {j : J}
    (hj : j ≠ j0) :
    IsVirtualCharacter (τ (alphaChar μ ξ n δ j0 i j)) := by
  have hαvirt := alphaChar_isVirtualCharacter_of_hypothesis_10_4_data h i j
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i j)
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hA0 :
        A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hNotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hA0
    have hαA0' :
        Section1.supportedOn (alphaChar μ ξ n δ j0 i j) A0 :=
      alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
        (hypothesis_10_4_a_of_hypothesis_10_4_data h) hj
    simpa [hA0] using hαA0'
  have hτvirt :
      Section4Scratch.tau_maps_a0_to_virtual_statement
        (W2.subgroupOf M) W A τ := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, hτvirt⟩
    exact hτvirt.1
  exact hτvirt (alphaChar μ ξ n δ j0 i j) hαvirt hαA0

public theorem tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    IsVirtualCharacter (τ₁ ξ) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨_h10, _hNotation, hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact (extensionInterfaces_of_hypothesis_10_4_data h).2.1 ξ
    (integerSpan_of_mem S hξS)

public theorem tauOne_xi_scalarProduct_self_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) = 1 := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  have hspanξ : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
  calc
    Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) =
        Section1.scalarProduct M ξ ξ :=
      (extensionInterfaces_of_hypothesis_10_4_data h).1 ξ ξ hspanξ hspanξ
    _ = 1 := scalarProduct_irreducible_self hξIrr

public theorem tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_supported_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    IsVirtualCharacter (τ₁ ξ) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨_h10, _hNotation, hξS, _hξIrr, _hξDegree, _hUniform⟩
  exact (extensionInterfaces_of_hypothesis_10_4_supported_data h).2.1 ξ
    (integerSpan_of_mem S hξS)

public theorem tauOne_xi_scalarProduct_self_of_hypothesis_10_4_supported_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) = 1 := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  have hspanξ : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
  calc
    Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) =
        Section1.scalarProduct M ξ ξ :=
      (extensionInterfaces_of_hypothesis_10_4_supported_data h).1 ξ ξ hspanξ hspanξ
    _ = 1 := scalarProduct_irreducible_self hξIrr

public theorem alphaChar_scalarProduct_conjugate_xi_eq_zero_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M
      (alphaChar μ ξ n δ j0 i j)
      (Section1.conjugateCharacter ξ) = 0 := by
  classical
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, hNotation, hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, hδ, hnpos, hdeg, _hsign, hdn⟩
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  rcases h46.1 with
    ⟨_hSemidirect, _hHall, _hCyclicW1, hW1ne1Sub, _hCyclicW2, _hW2ne1,
      _hCentralizer, _hW1W, _hW2W, _hDirect, _hOdd⟩
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis_10_1
      ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
        _hNotation10, _h52⟩
  rcases hypothesis_5_2_of_hypothesis_10_1
      ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
        _hNotation10, _h52⟩ with
    ⟨_hSetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
  have hξbarS : Section1.conjugateCharacter ξ ∈ S := (h52a ⟨ξ, hξS⟩).1
  have hξ_ne_bar :
      ξ ≠ Section1.conjugateCharacter ξ := (h52a ⟨ξ, hξS⟩).2
  have hξbarIrr :
      Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter ξ) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hξIrr
  have hξbarDegree :
      Section1.degree (Section1.conjugateCharacter ξ) = (Nat.card W1 : ℂ) := by
    calc
      Section1.degree (Section1.conjugateCharacter ξ) = star (Section1.degree ξ) :=
        by simp [Section1.degree, Section1.conjugateCharacter]
      _ = (Nat.card W1 : ℂ) := by
        rw [hξDegree]
        simp
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hW1ne1 : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne1Sub (by rw [hW1cardSub, hcard])
  have hW1gt : 1 < Nat.card W1 := by
    have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
    omega
  have hdneW1 : d ≠ Nat.card W1 := by
    intro hdw
    subst d
    rcases hδ with rfl | rfl
    · have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hnpos
      nlinarith [mul_le_mul_of_nonneg_right hn1
        (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
          (0 : ℤ) ≤ Nat.card W1)]
    · by_cases hn_eq : n = 1
      · subst n
        norm_num at hdn
      · have hn2_nat : 2 ≤ n := by omega
        have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn2_nat
        nlinarith [mul_le_mul_of_nonneg_right hn2
          (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
            (0 : ℤ) ≤ Nat.card W1)]
  have hentry_ne : μ i j ≠ Section1.conjugateCharacter ξ := by
    intro hEq
    have hdegEq : (d : ℂ) = (Nat.card W1 : ℂ) := by
      calc
        (d : ℂ) = Section1.degree (μ i j) := (hdeg i j hj).symm
        _ = Section1.degree (Section1.conjugateCharacter ξ) := by rw [hEq]
        _ = (Nat.card W1 : ℂ) := hξbarDegree
    have hdw : d = Nat.card W1 := by exact_mod_cast hdegEq
    exact hdneW1 hdw
  have hbase_ne : μ i j0 ≠ Section1.conjugateCharacter ξ := by
    intro hEq
    have hdegEq : (1 : ℂ) = (Nat.card W1 : ℂ) := by
      calc
        (1 : ℂ) = Section1.degree (μ i j0) :=
          (baseColumn_degree_one_of_section10FourSixNotationData hNotation i).symm
        _ = Section1.degree (Section1.conjugateCharacter ξ) := by rw [hEq]
        _ = (Nat.card W1 : ℂ) := hξbarDegree
    have hcard : Nat.card W1 = 1 := by exact_mod_cast hdegEq.symm
    exact hW1ne1 hcard
  have hentry :
      Section1.scalarProduct M (μ i j) (Section1.conjugateCharacter ξ) = 0 :=
    scalarProduct_irreducible_ne (hirr i j) hξbarIrr hentry_ne
  have hbase :
      Section1.scalarProduct M (μ i j0) (Section1.conjugateCharacter ξ) = 0 :=
    scalarProduct_irreducible_ne (hirr i j0) hξbarIrr hbase_ne
  have hξbar :
      Section1.scalarProduct M ξ (Section1.conjugateCharacter ξ) = 0 :=
    h52c hξS hξbarS hξ_ne_bar
  have halpha :
      alphaChar μ ξ n δ j0 i j =
        μ i j + (-(δ : ℂ)) • μ i j0 + (-(n : ℂ)) • ξ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  rw [halpha]
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
  rw [hentry, hbase, hξbar]
  simp

public theorem alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) ξ = -(n : ℂ) := by
  classical
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, hnpos, hdeg, _hsign, hdn⟩
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  rcases h46.1 with
    ⟨_hSemidirect, _hHall, _hCyclicW1, hW1ne1Sub, _hCyclicW2, _hW2ne1,
      _hCentralizer, _hW1W, _hW2W, _hDirect, _hOdd⟩
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base, _hNotation10, _h52⟩
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hW1ne1 : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne1Sub (by rw [hW1cardSub, hcard])
  have hW1gt : 1 < Nat.card W1 := by
    have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
    omega
  have hdneW1 : d ≠ Nat.card W1 := by
    intro hdw
    subst d
    rcases hδ with rfl | rfl
    · have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hnpos
      nlinarith [mul_le_mul_of_nonneg_right hn1
        (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
          (0 : ℤ) ≤ Nat.card W1)]
    · by_cases hn_eq : n = 1
      · subst n
        norm_num at hdn
      · have hn2_nat : 2 ≤ n := by omega
        have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn2_nat
        nlinarith [mul_le_mul_of_nonneg_right hn2
          (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
            (0 : ℤ) ≤ Nat.card W1)]
  have hentry_ne : μ i j ≠ ξ := by
    intro hEq
    have hdegEq : (d : ℂ) = (Nat.card W1 : ℂ) := by
      calc
        (d : ℂ) = Section1.degree (μ i j) := (hdeg i j hj).symm
        _ = Section1.degree ξ := by rw [hEq]
        _ = (Nat.card W1 : ℂ) := hξDegree
    have hdw : d = Nat.card W1 := by exact_mod_cast hdegEq
    exact hdneW1 hdw
  have hbase_ne : μ i j0 ≠ ξ := by
    intro hEq
    have hdegEq : (1 : ℂ) = (Nat.card W1 : ℂ) := by
      calc
        (1 : ℂ) = Section1.degree (μ i j0) :=
          (baseColumn_degree_one_of_section10FourSixNotationData hNotation i).symm
        _ = Section1.degree ξ := by rw [hEq]
        _ = (Nat.card W1 : ℂ) := hξDegree
    have hcard : Nat.card W1 = 1 := by exact_mod_cast hdegEq.symm
    exact hW1ne1 hcard
  have hentry :
      Section1.scalarProduct M (μ i j) ξ = 0 :=
    scalarProduct_irreducible_ne (hirr i j) hξIrr hentry_ne
  have hbase :
      Section1.scalarProduct M (μ i j0) ξ = 0 :=
    scalarProduct_irreducible_ne (hirr i j0) hξIrr hbase_ne
  have hξself : Section1.scalarProduct M ξ ξ = 1 :=
    scalarProduct_irreducible_self hξIrr
  have halpha :
      alphaChar μ ξ n δ j0 i j =
        μ i j + (-(δ : ℂ)) • μ i j0 + (-(n : ℂ)) • ξ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  rw [halpha]
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
  rw [hentry, hbase, hξself]
  simp

public theorem xi_sub_conjugate_supportedOn_a0_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Section1.supportedOn
      (ξ - Section1.conjugateCharacter ξ)
      (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis_10_1 h10
  have hξbarS : Section1.conjugateCharacter ξ ∈ S := (h52a ⟨ξ, hξS⟩).1
  have hdeg : Section1.degree ξ =
      Section1.degree (Section1.conjugateCharacter ξ) := by
    calc
      Section1.degree ξ = (Nat.card W1 : ℂ) := hξDegree
      _ = star (Nat.card W1 : ℂ) := by simp
      _ = Section1.degree (Section1.conjugateCharacter ξ) := by
        rw [← hξDegree]
        simp [Section1.degree, Section1.conjugateCharacter]
  have hpunct :
      Section4Scratch.puncturedSet ⊆
        Section4Scratch.a0Set (W2.subgroupOf M) W A := by
    rcases hNotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    intro x hx
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46 hx
  have hdeg0 :
      Section1.degree (ξ - Section1.conjugateCharacter ξ) = 0 := by
    have hdegSub :
        Section1.degree ξ -
          Section1.degree (Section1.conjugateCharacter ξ) = 0 :=
      sub_eq_zero.mpr hdeg
    simpa [Section1.degree] using hdegSub
  exact supportedOn_of_degree_eq_zero_of_punctured_subset hpunct hdeg0

public theorem alphaChar_tau_plus_tauOne_xi_pairing_integral_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    ∃ a : ℤ,
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ) := by
  have hατvirt :
      IsVirtualCharacter (τ (alphaChar μ ξ n δ j0 i0 j)) :=
    alphaChar_tau_isVirtualCharacter_of_hypothesis_10_4_data h hj
  have hξτvirt :
      IsVirtualCharacter (τ₁ ξ) :=
    tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_data h
  have hYvirt :
      IsVirtualCharacter
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) :=
    Section3.isVirtualCharacter_add hατvirt
      (isVirtualCharacter_natCast_smul_sec10_base n hξτvirt)
  exact Section3.scalarProduct_isVirtualCharacter_eq_int hYvirt hξτvirt

public theorem alphaChar_tau_scalarProduct_tauOne_xi_eq_sub_of_pairing
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ a : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (_hj : j ≠ j0)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ)) :
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i0 j))
      (τ₁ ξ) = (a : ℂ) - (n : ℂ) := by
  have hself :=
    tauOne_xi_scalarProduct_self_of_hypothesis_10_4_data h
  have hsum :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) =
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j))
        (τ₁ ξ) + (n : ℂ) := by
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      hself]
    ring
  calc
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i0 j))
      (τ₁ ξ) =
        (Section1.scalarProduct G
          (τ (alphaChar μ ξ n δ j0 i0 j))
          (τ₁ ξ) + (n : ℂ)) - (n : ℂ) := by ring
    _ = (a : ℂ) - (n : ℂ) := by rw [← hsum, ha]

public theorem alphaChar_tau_scalarProduct_tauOne_conjugate_xi_eq_of_pairing
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ a : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ)) :
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i0 j))
      (τ₁ (Section1.conjugateCharacter ξ)) = (a : ℂ) := by
  let α : Section1.ClassFunction M := alphaChar μ ξ n δ j0 i0 j
  let ξbar : Section1.ClassFunction M := Section1.conjugateCharacter ξ
  have hαA0 :
      Section1.supportedOn α
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
    have hA0 :
        A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hNotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hA0
    have hαA0' :
        Section1.supportedOn (alphaChar μ ξ n δ j0 i0 j) A0 :=
      alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
        (hypothesis_10_4_a_of_hypothesis_10_4_data h) hj
    simpa [α, hA0] using hαA0'
  have hdiffA0 :
      Section1.supportedOn (ξ - ξbar)
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    simpa [ξbar] using xi_sub_conjugate_supportedOn_a0_of_hypothesis_10_4_data h
  have hαClass : Section1.IsClassFunction α :=
    Section1.isVirtualCharacter_isClassFunction
      (by
        simpa [α] using
          alphaChar_isVirtualCharacter_of_hypothesis_10_4_data h i0 j)
  have hdiffClass : Section1.IsClassFunction (ξ - ξbar) := by
    rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
      ⟨_h10, _hNotation, _hξS, hξIrr, _hξDegree, _hUniform⟩
    have hξClass : Section1.IsClassFunction ξ :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
    have hξbarClass : Section1.IsClassFunction ξbar := by
      intro x g
      change star (ξ (x * g * x⁻¹)) = star (ξ g)
      rw [hξClass x g]
    intro x g
    simp [hξClass x g, hξbarClass x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_a0_statement (W2.subgroupOf M) W A τ := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt⟩
    exact hτiso
  have hsourceDiff :
      Section1.scalarProduct M α (ξ - ξbar) = -(n : ℂ) := by
    have hαξ :
        Section1.scalarProduct M α ξ = -(n : ℂ) := by
      simpa [α] using
        alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_data h hj
    have hαbar :
        Section1.scalarProduct M α ξbar = 0 := by
      simpa [α, ξbar] using
        alphaChar_scalarProduct_conjugate_xi_eq_zero_of_hypothesis_10_4_data h hj
    rw [Section5.scalarProduct_sub_right, hαξ, hαbar]
    simp
  have htargetDiff :
      Section1.scalarProduct G (τ α) (τ₁ (ξ - ξbar)) = -(n : ℂ) := by
    have hagree := xi_sub_conjugate_tauOne_eq_tau_of_hypothesis_10_4_data h
    rw [hagree]
    exact (hτiso α (ξ - ξbar) hαClass hdiffClass hαA0 hdiffA0).trans hsourceDiff
  have hsplit :
      Section1.scalarProduct G (τ α) (τ₁ (ξ - ξbar)) =
        Section1.scalarProduct G (τ α) (τ₁ ξ) -
          Section1.scalarProduct G (τ α) (τ₁ ξbar) := by
    rw [map_sub, Section5.scalarProduct_sub_right]
  have hξ :
      Section1.scalarProduct G (τ α) (τ₁ ξ) = (a : ℂ) - (n : ℂ) := by
    simpa [α] using
      alphaChar_tau_scalarProduct_tauOne_xi_eq_sub_of_pairing h hj ha
  have htargetDiffSplit :
      Section1.scalarProduct G (τ α) (τ₁ ξ) -
          Section1.scalarProduct G (τ α) (τ₁ ξbar) = -(n : ℂ) := by
    rw [← hsplit]
    exact htargetDiff
  have htmp :
      (a : ℂ) - (n : ℂ) -
          Section1.scalarProduct G (τ α) (τ₁ ξbar) = -(n : ℂ) := by
    simpa [hξ] using htargetDiffSplit
  calc
    Section1.scalarProduct G (τ α) (τ₁ ξbar) =
        ((a : ℂ) - (n : ℂ)) -
          (((a : ℂ) - (n : ℂ)) -
            Section1.scalarProduct G (τ α) (τ₁ ξbar)) := by ring
    _ = ((a : ℂ) - (n : ℂ)) - (-(n : ℂ)) := by rw [htmp]
    _ = (a : ℂ) := by ring

public theorem tauOne_muColumn_sub_smul_conjugate_xi_eq_tau_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {k : J}
    (hk : k ≠ j0) :
    τ₁ (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ) =
      τ (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ) := by
  have hExt := coherentExtension_of_hypothesis_10_4_data h
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis_10_1 h10
  have hξbarS : Section1.conjugateCharacter ξ ∈ S := (h52a ⟨ξ, hξS⟩).1
  have hspan_col : Section5.integerSpan S (muColumn μ k) :=
    integerSpan_of_mem S (muColumn_mem_of_hypothesis_10_4_data h hk)
  have hspan_xibar : Section5.integerSpan S (Section1.conjugateCharacter ξ) :=
    integerSpan_of_mem S hξbarS
  have hspan_dxibar :
      Section5.integerSpan S ((d : ℂ) • Section1.conjugateCharacter ξ) := by
    simpa using
      integerSpan_int_smul (S := S) (φ := Section1.conjugateCharacter ξ)
        (z := (d : ℤ)) hspan_xibar
  have hspan :
      Section5.integerSpan S
        (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ) :=
    integerSpan_sub hspan_col hspan_dxibar
  have hξbarDegree :
      Section1.degree (Section1.conjugateCharacter ξ) = (Nat.card W1 : ℂ) := by
    calc
      Section1.degree (Section1.conjugateCharacter ξ) = star (Section1.degree ξ) :=
        by simp [Section1.degree, Section1.conjugateCharacter]
      _ = (Nat.card W1 : ℂ) := by
        rw [hξDegree]
        simp
  have hsupp :
      Section1.supportedOn
        (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ)
        Section5.puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero
      (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ)).2
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_data h hk
    have hcol1 : muColumn μ k 1 = (d : ℂ) * (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hcoldeg
    have hbar1 :
        Section1.conjugateCharacter ξ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hξbarDegree
    rw [Section1.degree]
    simp [Pi.sub_apply, Pi.smul_apply, hcol1, hbar1]
  exact hExt.2.2
    (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ)
    ⟨hspan, hsupp⟩

public theorem scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    (i : I) (j k : J) :
    Section1.scalarProduct M (μ i j) (muColumn μ k) =
      if j = k then 1 else 0 := by
  classical
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0⟩
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

public theorem alphaChar_scalarProduct_muColumn_eq_zero_of_ne_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j k : J}
    (_hj : j ≠ j0)
    (hk : k ≠ j0)
    (hjk : j ≠ k) :
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) (muColumn μ k) = 0 := by
  classical
  have hentry :
      Section1.scalarProduct M (μ i j) (muColumn μ k) = 0 := by
    simpa [hjk] using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_data h i j k
  have hbase :
      Section1.scalarProduct M (μ i j0) (muColumn μ k) = 0 := by
    simpa [hk.symm] using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_data h i j0 k
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, _hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hcolS : muColumn μ k ∈ S := muColumn_mem_of_hypothesis_10_4_data h hk
  have hne : ξ ≠ muColumn μ k := by
    intro hEq
    have hdegEq :
        Section1.degree (muColumn μ k) = Section1.degree ξ := by
      rw [← hEq]
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_data h hk
    rw [hcoldeg, hξDegree] at hdegEq
    have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
      have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
      have hW1natNe : Nat.card W1 ≠ 0 := Nat.ne_of_gt hW1pos
      exact_mod_cast hW1natNe
    have hdEq : (d : ℂ) = 1 := by
      exact mul_right_cancel₀ hW1ne (by simpa using hdegEq)
    have hdne : (d : ℂ) ≠ 1 := by
      exact_mod_cast (ne_of_gt hdpos)
    exact hdne hdEq
  rcases hypothesis_5_2_of_hypothesis_10_1 h10 with
    ⟨_hSetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
  have hξcol :
      Section1.scalarProduct M ξ (muColumn μ k) = 0 :=
    h52c hξS hcolS hne
  have halpha :
      alphaChar μ ξ n δ j0 i j =
        μ i j + (-(δ : ℂ)) • μ i j0 + (-(n : ℂ)) • ξ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  rw [halpha]
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
  rw [hentry, hbase, hξcol]
  simp

public theorem alphaChar_scalarProduct_muColumn_sub_smul_conjugate_xi_eq_zero
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j k : J}
    (hj : j ≠ j0)
    (hk : k ≠ j0)
    (hjk : j ≠ k) :
    Section1.scalarProduct M
      (alphaChar μ ξ n δ j0 i j)
      (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ) = 0 := by
  have hcol :
      Section1.scalarProduct M
        (alphaChar μ ξ n δ j0 i j) (muColumn μ k) = 0 :=
    alphaChar_scalarProduct_muColumn_eq_zero_of_ne_of_hypothesis_10_4_data
      h hj hk hjk
  have hbar :
      Section1.scalarProduct M
        (alphaChar μ ξ n δ j0 i j) (Section1.conjugateCharacter ξ) = 0 :=
    alphaChar_scalarProduct_conjugate_xi_eq_zero_of_hypothesis_10_4_data h hj
  rw [Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right,
    hcol, hbar]
  simp

public theorem muColumn_sub_smul_conjugate_xi_supportedOn_a0_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {k : J}
    (hk : k ≠ j0) :
    Section1.supportedOn
      (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ)
      (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨_h10, hNotation, _hξS, _hξIrr, hξDegree, _hUniform⟩
  have hξbarDegree :
      Section1.degree (Section1.conjugateCharacter ξ) = (Nat.card W1 : ℂ) := by
    calc
      Section1.degree (Section1.conjugateCharacter ξ) = star (Section1.degree ξ) :=
        by simp [Section1.degree, Section1.conjugateCharacter]
      _ = (Nat.card W1 : ℂ) := by
        rw [hξDegree]
        simp
  have hpunct :
      Section4Scratch.puncturedSet ⊆
        Section4Scratch.a0Set (W2.subgroupOf M) W A := by
    rcases hNotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    intro x hx
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46 hx
  have hdeg0 :
      Section1.degree
        (muColumn μ k - (d : ℂ) • Section1.conjugateCharacter ξ) = 0 := by
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_data h hk
    have hcol1 : muColumn μ k 1 = (d : ℂ) * (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hcoldeg
    have hbar1 :
        Section1.conjugateCharacter ξ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hξbarDegree
    rw [Section1.degree]
    simp [Pi.sub_apply, Pi.smul_apply, hcol1, hbar1]
  exact supportedOn_of_degree_eq_zero_of_punctured_subset hpunct hdeg0

public theorem alphaChar_tau_scalarProduct_tauOne_muColumn_eq_d_mul_of_pairing
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ a : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j k : J}
    (hj : j ≠ j0)
    (hk : k ≠ j0)
    (hjk : j ≠ k)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ)) :
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i0 j))
      (τ₁ (muColumn μ k)) = (d : ℂ) * (a : ℂ) := by
  let α : Section1.ClassFunction M := alphaChar μ ξ n δ j0 i0 j
  let ξbar : Section1.ClassFunction M := Section1.conjugateCharacter ξ
  let diff : Section1.ClassFunction M := muColumn μ k - (d : ℂ) • ξbar
  have hαA0 :
      Section1.supportedOn α
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
    have hA0 :
        A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hNotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hA0
    have hαA0' :
        Section1.supportedOn (alphaChar μ ξ n δ j0 i0 j) A0 :=
      alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
        (hypothesis_10_4_a_of_hypothesis_10_4_data h) hj
    simpa [α, hA0] using hαA0'
  have hdiffA0 :
      Section1.supportedOn diff
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    simpa [diff, ξbar] using
      muColumn_sub_smul_conjugate_xi_supportedOn_a0_of_hypothesis_10_4_data h hk
  have hαClass : Section1.IsClassFunction α :=
    Section1.isVirtualCharacter_isClassFunction
      (by
        simpa [α] using
          alphaChar_isVirtualCharacter_of_hypothesis_10_4_data h i0 j)
  have hdiffClass : Section1.IsClassFunction diff := by
    rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
      ⟨_h10, hNotation, _hξS, hξIrr, _hξDegree, _hUniform⟩
    rcases fullFourSixData_of_section10FourSixNotationData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        _h22A0, _hDadeA0, hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    have hmuClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (h43b.2.2.1 i j))
    have hcolClass : Section1.IsClassFunction (muColumn μ k) := by
      intro x g
      unfold muColumn
      simpa using Finset.sum_congr rfl (fun i _hi => hmuClass i k x g)
    have hξClass : Section1.IsClassFunction ξ :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
    have hξbarClass : Section1.IsClassFunction ξbar := by
      intro x g
      change star (ξ (x * g * x⁻¹)) = star (ξ g)
      rw [hξClass x g]
    have hsmulClass : Section1.IsClassFunction ((d : ℂ) • ξbar) :=
      Section1.isClassFunction_smul (d : ℂ) ξbar hξbarClass
    intro x g
    simp [diff, hcolClass x g, hsmulClass x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_a0_statement (W2.subgroupOf M) W A τ := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt⟩
    exact hτiso
  have hsource :
      Section1.scalarProduct M α diff = 0 := by
    simpa [α, diff, ξbar] using
      alphaChar_scalarProduct_muColumn_sub_smul_conjugate_xi_eq_zero h hj hk hjk
  have htarget :
      Section1.scalarProduct G (τ α) (τ₁ diff) = 0 := by
    have hagree : τ₁ diff = τ diff := by
      simpa [diff, ξbar] using
        tauOne_muColumn_sub_smul_conjugate_xi_eq_tau_of_hypothesis_10_4_data h hk
    rw [hagree]
    exact (hτiso α diff hαClass hdiffClass hαA0 hdiffA0).trans hsource
  have hsplit :
      Section1.scalarProduct G (τ α) (τ₁ diff) =
        Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) -
          (d : ℂ) *
            Section1.scalarProduct G (τ α) (τ₁ ξbar) := by
    dsimp [diff]
    rw [map_sub, map_smul, Section5.scalarProduct_sub_right,
      Section1.scalarProduct_smul_right]
    simp
  have hbar :
      Section1.scalarProduct G (τ α) (τ₁ ξbar) = (a : ℂ) := by
    simpa [α, ξbar] using
      alphaChar_tau_scalarProduct_tauOne_conjugate_xi_eq_of_pairing h hj ha
  have htmp :
      Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) -
          (d : ℂ) * (a : ℂ) = 0 := by
    simpa [hsplit, hbar] using htarget
  calc
    Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) =
        (Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) -
          (d : ℂ) * (a : ℂ)) + (d : ℂ) * (a : ℂ) := by ring
    _ = (d : ℂ) * (a : ℂ) := by rw [htmp]; ring

public theorem alphaChar_scalarProduct_self_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M
        (alphaChar μ ξ n δ j0 i j)
        (alphaChar μ ξ n δ j0 i j) =
      (2 : ℂ) + (n : ℂ) ^ 2 := by
  classical
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, hnpos, hdeg, _hsign, hdn⟩
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt⟩
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  rcases h46.1 with
    ⟨_hSemidirect, _hHall, _hCyclicW1, hW1ne1Sub, _hCyclicW2, _hW2ne1,
      _hCentralizer, _hW1W, _hW2W, _hDirect, _hOdd⟩
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hW1ne1 : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne1Sub (by rw [hW1cardSub, hcard])
  have hW1gt : 1 < Nat.card W1 := by
    have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
    omega
  have hdneW1 : d ≠ Nat.card W1 := by
    intro hdw
    subst d
    rcases hδ with rfl | rfl
    · have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hnpos
      nlinarith [mul_le_mul_of_nonneg_right hn1
        (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
          (0 : ℤ) ≤ Nat.card W1)]
    · by_cases hn_eq : n = 1
      · subst n
        norm_num at hdn
      · have hn2_nat : 2 ≤ n := by omega
        have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn2_nat
        nlinarith [mul_le_mul_of_nonneg_right hn2
          (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
            (0 : ℤ) ≤ Nat.card W1)]
  have hentry_ne : μ i j ≠ ξ := by
    intro hEq
    have hdegEq : (d : ℂ) = (Nat.card W1 : ℂ) := by
      calc
        (d : ℂ) = Section1.degree (μ i j) := (hdeg i j hj).symm
        _ = Section1.degree ξ := by rw [hEq]
        _ = (Nat.card W1 : ℂ) := hξDegree
    have hdw : d = Nat.card W1 := by exact_mod_cast hdegEq
    exact hdneW1 hdw
  have hbase_ne : μ i j0 ≠ ξ := by
    intro hEq
    have hdegEq : (1 : ℂ) = (Nat.card W1 : ℂ) := by
      calc
        (1 : ℂ) = Section1.degree (μ i j0) :=
          (baseColumn_degree_one_of_section10FourSixNotationData hNotation i).symm
        _ = Section1.degree ξ := by rw [hEq]
        _ = (Nat.card W1 : ℂ) := hξDegree
    have hcard : Nat.card W1 = 1 := by exact_mod_cast hdegEq.symm
    exact hW1ne1 hcard
  have hμbase_ne : μ i j ≠ μ i j0 := by
    intro hEq
    exact (hdistinct (i, j) (i, j0) (by
      intro hpair
      exact hj (congrArg Prod.snd hpair))) hEq
  have hα :
      alphaChar μ ξ n δ j0 i j =
        μ i j + (-(δ : ℂ)) • μ i j0 + (-(n : ℂ)) • ξ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  have hμself : Section1.scalarProduct M (μ i j) (μ i j) = 1 :=
    scalarProduct_irreducible_self (hirr i j)
  have hbaseself : Section1.scalarProduct M (μ i j0) (μ i j0) = 1 :=
    scalarProduct_irreducible_self (hirr i j0)
  have hξself : Section1.scalarProduct M ξ ξ = 1 :=
    scalarProduct_irreducible_self hξIrr
  have hμbase : Section1.scalarProduct M (μ i j) (μ i j0) = 0 :=
    scalarProduct_irreducible_ne (hirr i j) (hirr i j0) hμbase_ne
  have hbaseμ : Section1.scalarProduct M (μ i j0) (μ i j) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hμbase
  have hμξ : Section1.scalarProduct M (μ i j) ξ = 0 :=
    scalarProduct_irreducible_ne (hirr i j) hξIrr hentry_ne
  have hξμ : Section1.scalarProduct M ξ (μ i j) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hμξ
  have hbaseξ : Section1.scalarProduct M (μ i j0) ξ = 0 :=
    scalarProduct_irreducible_ne (hirr i j0) hξIrr hbase_ne
  have hξbase : Section1.scalarProduct M ξ (μ i j0) = 0 := by
    simpa [Section1.scalarProduct_star_swap] using congrArg star hbaseξ
  rw [hα]
  simp only [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
    Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    hμself, hbaseself, hξself, hμbase, hbaseμ, hμξ, hξμ, hbaseξ, hξbase]
  rcases hδ with rfl | rfl <;> norm_num [pow_two]

public theorem alphaChar_tau_cfNormSq_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section5.cfNormSq (τ (alphaChar μ ξ n δ j0 i j)) =
      (2 : ℝ) + (n : ℝ) ^ 2 := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i j)
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hA0 :
        A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hNotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hA0
    have hαA0' :
        Section1.supportedOn (alphaChar μ ξ n δ j0 i j) A0 :=
      alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
        (hypothesis_10_4_a_of_hypothesis_10_4_data h) hj
    simpa [hA0] using hαA0'
  have hτiso :
      Section4Scratch.tau_isometry_on_a0_statement (W2.subgroupOf M) W A τ := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt⟩
    exact hτiso
  have hself :
      Section1.scalarProduct G
          (τ (alphaChar μ ξ n δ j0 i j))
          (τ (alphaChar μ ξ n δ j0 i j)) =
        (2 : ℂ) + (n : ℂ) ^ 2 := by
    have hαClass : Section1.IsClassFunction (alphaChar μ ξ n δ j0 i j) :=
      Section1.isVirtualCharacter_isClassFunction
        (alphaChar_isVirtualCharacter_of_hypothesis_10_4_data h i j)
    rw [hτiso (alphaChar μ ξ n δ j0 i j)
      (alphaChar μ ξ n δ j0 i j) hαClass hαClass hαA0 hαA0]
    exact alphaChar_scalarProduct_self_of_hypothesis_10_4_data h hj
  unfold Section5.cfNormSq
  rw [hself]
  simp [pow_two]

public theorem inner_self_re_eq_card_mul_cfNormSq
    {G : Type*} [Group G] [Finite G]
    (ψ : Section1.ClassFunction G) :
    RCLike.re (inner ℂ (WithLp.toLp 2 ψ : EuclideanSpace ℂ G)
      (WithLp.toLp 2 ψ : EuclideanSpace ℂ G)) =
      (Nat.card G : ℝ) * Section5.cfNormSq ψ := by
  classical
  rw [Section5.cfNormSq_eq_inv_card_mul_sum_normSq]
  rw [PiLp.inner_apply]
  simp
  have hcard : (Nat.card G : ℝ) ≠ 0 := by
    have hpos : 0 < Nat.card G := Nat.card_pos (α := G)
    exact_mod_cast (ne_of_gt hpos)
  field_simp [hcard]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [Complex.normSq_eq_norm_sq]
  norm_num [pow_two]

public theorem scalarProduct_normSq_le_cfNormSq_mul
    {G : Type*} [Group G] [Finite G]
    (φ ψ : Section1.ClassFunction G) :
    Complex.normSq (Section1.scalarProduct G φ ψ) ≤
      Section5.cfNormSq φ * Section5.cfNormSq ψ := by
  classical
  let x : EuclideanSpace ℂ G := WithLp.toLp 2 ψ
  let y : EuclideanSpace ℂ G := WithLp.toLp 2 φ
  let s : ℂ := ∑ g : G, φ g * star (ψ g)
  let t : ℂ := ∑ g : G, ψ g * star (φ g)
  have hxy : inner ℂ x y = s := by simp [x, y, s, PiLp.inner_apply]
  have hyx : inner ℂ y x = t := by simp [x, y, t, PiLp.inner_apply]
  have hxx : RCLike.re (inner ℂ x x) =
      (Nat.card G : ℝ) * Section5.cfNormSq ψ := by
    simpa [x] using inner_self_re_eq_card_mul_cfNormSq (G := G) ψ
  have hyy : RCLike.re (inner ℂ y y) =
      (Nat.card G : ℝ) * Section5.cfNormSq φ := by
    simpa [y] using inner_self_re_eq_card_mul_cfNormSq (G := G) φ
  have hcs := @inner_mul_inner_self_le ℂ (EuclideanSpace ℂ G) _ _ _ x y
  rw [hxy, hyx, hxx, hyy] at hcs
  have ht : t = star s := by
    dsimp [s, t]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro g _
    simp [mul_comm]
  have hsleft : ‖s‖ * ‖t‖ = Complex.normSq s := by
    rw [ht, norm_star, Complex.normSq_eq_norm_sq]
    ring
  have hraw : Complex.normSq s ≤
      ((Nat.card G : ℝ) * Section5.cfNormSq ψ) *
        ((Nat.card G : ℝ) * Section5.cfNormSq φ) := by
    rw [← hsleft]
    exact hcs
  have hcard : (Nat.card G : ℝ) ≠ 0 := by
    have hpos : 0 < Nat.card G := Nat.card_pos (α := G)
    exact_mod_cast (ne_of_gt hpos)
  have hsp : Section1.scalarProduct G φ ψ = ((Nat.card G : ℂ)⁻¹) * s := by
    rfl
  rw [hsp]
  rw [Complex.normSq_mul, Complex.normSq_inv, Complex.normSq_natCast]
  field_simp [hcard]
  nlinarith [hraw]

public theorem muColumn_scalarProduct_self_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    (k : J) :
    Section1.scalarProduct M (muColumn μ k) (muColumn μ k) =
      (Fintype.card I : ℂ) := by
  classical
  unfold muColumn
  have hsum :
      ((∑ i : I, μ i k : Section1.ClassFunction M)) =
        fun x => ∑ i : I, μ i k x := by
    ext x
    simp
  nth_rw 1 [hsum]
  rw [Section1.scalarProduct_fintype_sum_left]
  rw [show (Fintype.card I : ℂ) = ∑ _i : I, (1 : ℂ) by simp]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change Section1.scalarProduct M (μ i k) (muColumn μ k) = 1
  simpa using scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_data h i k k

public theorem tauOne_muColumn_cfNormSq_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {k : J}
    (hk : k ≠ j0) :
    Section5.cfNormSq (τ₁ (muColumn μ k)) = (Fintype.card I : ℝ) := by
  have hcolS : muColumn μ k ∈ S := muColumn_mem_of_hypothesis_10_4_data h hk
  have hspanCol : Section5.integerSpan S (muColumn μ k) :=
    integerSpan_of_mem S hcolS
  have hself :
      Section1.scalarProduct G (τ₁ (muColumn μ k)) (τ₁ (muColumn μ k)) =
        (Fintype.card I : ℂ) := by
    calc
      Section1.scalarProduct G (τ₁ (muColumn μ k)) (τ₁ (muColumn μ k)) =
          Section1.scalarProduct M (muColumn μ k) (muColumn μ k) :=
        (extensionInterfaces_of_hypothesis_10_4_data h).1
          (muColumn μ k) (muColumn μ k) hspanCol hspanCol
      _ = (Fintype.card I : ℂ) :=
        muColumn_scalarProduct_self_of_hypothesis_10_4_data h k
  unfold Section5.cfNormSq
  rw [hself]
  simp

public theorem alphaChar_tau_muColumn_pairing_normSq_le_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ a : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j k : J}
    (hj : j ≠ j0)
    (hk : k ≠ j0)
    (hjk : j ≠ k)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ)) :
    Complex.normSq ((d : ℂ) * (a : ℂ)) ≤
      ((2 : ℝ) + (n : ℝ) ^ 2) * (Fintype.card I : ℝ) := by
  have hpair :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j))
        (τ₁ (muColumn μ k)) = (d : ℂ) * (a : ℂ) :=
    alphaChar_tau_scalarProduct_tauOne_muColumn_eq_d_mul_of_pairing
      h hj hk hjk ha
  have hle :=
    scalarProduct_normSq_le_cfNormSq_mul
      (G := G)
      (τ (alphaChar μ ξ n δ j0 i0 j))
      (τ₁ (muColumn μ k))
  rw [hpair,
    alphaChar_tau_cfNormSq_of_hypothesis_10_4_data h hj,
    tauOne_muColumn_cfNormSq_of_hypothesis_10_4_data h hk] at hle
  simpa using hle

public theorem card_W1_ge_three_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    3 ≤ Nat.card W1 := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hcardSub : 3 ≤ Nat.card (W1.subgroupOf M) :=
    Section3.natCard_left_ge_three_of_hypothesis_3_1 h31
  rcases hypothesis_10_1_of_hypothesis_10_4_data h with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hcard : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  rw [← hcard]
  exact hcardSub


public theorem odd_card_W1_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    Odd (Nat.card W1) := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hoddSub : Odd (Nat.card (W1.subgroupOf M)) :=
    Section3.odd_natCard_left_of_hypothesis_3_1 h31
  rcases hypothesis_10_1_of_hypothesis_10_4_data h with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hcard : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  rw [hcard] at hoddSub
  exact hoddSub

public theorem card_W1_ge_three_of_hypothesis_10_4_supported_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    3 ≤ Nat.card W1 := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hcardSub : 3 ≤ Nat.card (W1.subgroupOf M) :=
    Section3.natCard_left_ge_three_of_hypothesis_3_1 h31
  rcases hypothesis_10_1_of_hypothesis_10_4_supported_data h with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hcard : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  rw [← hcard]
  exact hcardSub

public theorem card_W2_ge_three_of_hypothesis_10_4_supported_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    3 ≤ Nat.card W2 := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, _hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hcardSub : 3 ≤ Nat.card (W2.subgroupOf M) :=
    Section3.natCard_right_ge_three_of_hypothesis_3_1 h31
  rcases hypothesis_10_1_of_hypothesis_10_4_supported_data h with
    ⟨_hM, _hType, _hS, _hW1M, hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hcard : Nat.card (W2.subgroupOf M) = Nat.card W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).toEquiv
  rw [← hcard]
  exact hcardSub

public theorem odd_card_W1_of_hypothesis_10_4_supported_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    Odd (Nat.card W1) := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hoddSub : Odd (Nat.card (W1.subgroupOf M)) :=
    Section3.odd_natCard_left_of_hypothesis_3_1 h31
  rcases hypothesis_10_1_of_hypothesis_10_4_supported_data h with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hcard : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  rw [hcard] at hoddSub
  exact hoddSub

public theorem even_n_of_odd_degree_uniform_pf105
    {w d n : ℕ} {δ : ℤ}
    (hwodd : Odd w) (hdodd : Odd d)
    (hδ : δ = 1 ∨ δ = -1)
    (hdn : (d : ℤ) = (n : ℤ) * (w : ℤ) + δ) :
    Even n := by
  rw [← Nat.not_odd_iff_even]
  intro hnodd
  rcases hδ with rfl | rfl
  · have hdnNat : d = n * w + 1 := by omega
    have hprodOdd : Odd (n * w) := hnodd.mul hwodd
    have heven : Even (n * w + 1) := hprodOdd.add_one
    rw [← hdnNat] at heven
    exact (Nat.not_odd_iff_even.mpr heven) hdodd
  · have hdnNat : d + 1 = n * w := by omega
    have hprodOdd : Odd (n * w) := hnodd.mul hwodd
    have heven : Even (d + 1) := hdodd.add_one
    rw [hdnNat] at heven
    exact (Nat.not_odd_iff_even.mpr heven) hprodOdd

public theorem odd_degree_nat_of_irreducible_of_odd_card_pf105
    {L : Type u} [Group L] [Finite L]
    {χ : Section1.ClassFunction L} {d : ℕ}
    (hodd : Odd (Nat.card L))
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hdeg : Section1.degree χ = (d : ℂ)) :
    Odd d := by
  have hbook := isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup_sec10 hχ
  rcases Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter χ hbook with
    ⟨d0, hdeg0, hdvd⟩
  have hd : d = d0 := by
    exact_mod_cast hdeg.symm.trans hdeg0
  rw [hd]
  exact odd_of_card_dvd hodd hdvd

public theorem mu_entry_irreducible_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    (i : I) (j : J) :
    Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt⟩
  exact h43b.2.2.1 i j

public theorem even_n_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    Even n := by
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, _hnpos, hdeg, _hsign, hdn⟩
  have hoddM : Odd (Nat.card M) :=
    odd_card_M_of_hypothesis_10_4_data h
  have hdodd : Odd d :=
    odd_degree_nat_of_irreducible_of_odd_card_pf105 hoddM
      (mu_entry_irreducible_of_hypothesis_10_4_data h i0 j)
      (hdeg i0 j hj)
  exact even_n_of_odd_degree_uniform_pf105
    (odd_card_W1_of_hypothesis_10_4_data h) hdodd hδ hdn

public theorem one_le_normSq_intCast_of_ne_zero_pf105
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

public theorem degree_sq_le_of_pairing_cauchy_nonzero_pf105
    {d : ℕ} {a : ℤ} {B : ℝ}
    (ha : (a : ℂ) ≠ 0)
    (hle : Complex.normSq ((d : ℂ) * (a : ℂ)) ≤ B) :
    ((d : ℝ) ^ 2) ≤ B := by
  have ha1 : (1 : ℝ) ≤ Complex.normSq (a : ℂ) :=
    one_le_normSq_intCast_of_ne_zero_pf105 a ha
  have hd0 : 0 ≤ Complex.normSq (d : ℂ) := Complex.normSq_nonneg _
  have hmul : Complex.normSq (d : ℂ) ≤
      Complex.normSq (d : ℂ) * Complex.normSq (a : ℂ) := by
    nlinarith
  have hda : Complex.normSq (d : ℂ) * Complex.normSq (a : ℂ) ≤ B := by
    simpa [Complex.normSq_mul] using hle
  have hdB : Complex.normSq (d : ℂ) ≤ B := le_trans hmul hda
  simpa [Complex.normSq_natCast, pow_two] using hdB

public theorem n_lt_two_of_uniform_cauchy_bound_pf105
    {w d n : ℕ} {δ : ℤ}
    (hw : 3 ≤ w) (hδ : δ = 1 ∨ δ = -1)
    (hdn : (d : ℤ) = (n : ℤ) * (w : ℤ) + δ)
    (hbound : ((d : ℝ) ^ 2) ≤ (w : ℝ) * (2 + (n : ℝ) ^ 2)) :
    n < 2 := by
  by_contra hnot
  have hn2 : 2 ≤ n := by omega
  have hdnR : (d : ℝ) = (n : ℝ) * (w : ℝ) + (δ : ℝ) := by
    exact_mod_cast hdn
  rw [hdnR] at hbound
  have hwr : (3 : ℝ) ≤ w := by exact_mod_cast hw
  have hnr2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  rcases hδ with rfl | rfl
  · norm_num at hbound
    have hpoly : ((w : ℝ) ^ 2 - (w : ℝ)) * (n : ℝ) ^ 2 +
        2 * (w : ℝ) * (n : ℝ) + 1 - 2 * (w : ℝ) ≤ 0 := by
      nlinarith [hbound]
    have hnonneg : 0 ≤ (((w : ℝ) ^ 2 - (w : ℝ)) * (n : ℝ) ^ 2) := by
      exact mul_nonneg (sub_nonneg.mpr (by nlinarith)) (sq_nonneg (n : ℝ))
    have hpos : 0 < ((w : ℝ) ^ 2 - (w : ℝ)) * (n : ℝ) ^ 2 +
        2 * (w : ℝ) * (n : ℝ) + 1 - 2 * (w : ℝ) := by
      nlinarith [hnonneg]
    linarith
  · norm_num at hbound
    have hpoly : ((w : ℝ) ^ 2 - (w : ℝ)) * (n : ℝ) ^ 2 -
        2 * (w : ℝ) * (n : ℝ) + 1 - 2 * (w : ℝ) ≤ 0 := by
      nlinarith [hbound]
    have hmain :
        4 * (w : ℝ) * (n : ℝ) ≤ ((w : ℝ) ^ 2 - (w : ℝ)) * (n : ℝ) ^ 2 := by
      nlinarith
        [mul_nonneg
          (sub_nonneg.mpr (show (1 : ℝ) ≤ (w : ℝ) by linarith))
          (sub_nonneg.mpr (show (2 : ℝ) ≤ (n : ℝ) by linarith))]
    have hpos : 0 < ((w : ℝ) ^ 2 - (w : ℝ)) * (n : ℝ) ^ 2 -
        2 * (w : ℝ) * (n : ℝ) + 1 - 2 * (w : ℝ) := by
      nlinarith
    linarith

public theorem coefficient_eq_zero_of_even_uniform_cauchy_bound_pf105
    {w d n : ℕ} {δ a : ℤ}
    (hw : 3 ≤ w) (hn : 0 < n) (heven : Even n)
    (hδ : δ = 1 ∨ δ = -1)
    (hdn : (d : ℤ) = (n : ℤ) * (w : ℤ) + δ)
    (hle : Complex.normSq ((d : ℂ) * (a : ℂ)) ≤
      ((2 : ℝ) + (n : ℝ) ^ 2) * (w : ℝ)) :
    a = 0 := by
  by_contra ha0
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  have hbound : ((d : ℝ) ^ 2) ≤ (w : ℝ) * (2 + (n : ℝ) ^ 2) := by
    have h := degree_sq_le_of_pairing_cauchy_nonzero_pf105 haC hle
    nlinarith [h]
  have hnlt : n < 2 :=
    n_lt_two_of_uniform_cauchy_bound_pf105 hw hδ hdn hbound
  have hn1 : n = 1 := by omega
  subst n
  norm_num at heven

public theorem exists_other_nonbase_column_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    ∃ k : J, k ≠ j0 ∧ k ≠ j := by
  classical
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
  have hcard : 3 ≤ Nat.card (W2.subgroupOf M) :=
    Section3.natCard_right_ge_three_of_hypothesis_3_1 h31
  exact Section3.exists_other_col_ne_base_of_card_right_ge_three
    (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M) (W := W)
    (i0 := i0) (j0 := j0) (ω := ω) hω hj hcard

public theorem alphaChar_tau_pairing_coefficient_eq_zero_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ a : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ)) :
    a = 0 := by
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨hI, _hJ, _hPrime, _hdpos, hδ, hnpos, _hdeg, _hsign, hdn⟩
  rcases exists_other_nonbase_column_of_hypothesis_10_4_data h hj with
    ⟨k, hk, hkj⟩
  have hle :=
    alphaChar_tau_muColumn_pairing_normSq_le_of_hypothesis_10_4_data
      h hj hk hkj.symm ha
  have hleW :
      Complex.normSq ((d : ℂ) * (a : ℂ)) ≤
        ((2 : ℝ) + (n : ℝ) ^ 2) * (Nat.card W1 : ℝ) := by
    have hcardIR : (Fintype.card I : ℝ) = (Nat.card W1 : ℝ) := by
      exact_mod_cast (by simpa [Nat.card_eq_fintype_card] using hI)
    simpa [hcardIR] using hle
  exact coefficient_eq_zero_of_even_uniform_cauchy_bound_pf105
    (card_W1_ge_three_of_hypothesis_10_4_data h)
    hnpos
    (even_n_of_hypothesis_10_4_data h hj)
    hδ
    hdn
    hleW

public theorem alphaChar_corrected_tau_pairing_eq_zero_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
      (τ₁ ξ) = 0 := by
  rcases alphaChar_tau_plus_tauOne_xi_pairing_integral_of_hypothesis_10_4_data
      h hj with
    ⟨a, ha⟩
  have ha0 : a = 0 :=
    alphaChar_tau_pairing_coefficient_eq_zero_of_hypothesis_10_4_data h hj ha
  simpa [ha0] using ha

public theorem alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    Section5.cfNormSq
      (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) = 2 := by
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ξ n δ j0 i0 j)
  let Z : Section1.ClassFunction G := τ₁ ξ
  let Y : Section1.ClassFunction G := Aτ + (n : ℂ) • Z
  have hYZ : Section1.scalarProduct G Y Z = 0 := by
    dsimp [Y, Z, Aτ]
    exact alphaChar_corrected_tau_pairing_eq_zero_of_hypothesis_10_4_data h hj
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
    exact alphaChar_tau_cfNormSq_of_hypothesis_10_4_data h hj
  have hZZ : Section1.scalarProduct G Z Z = 1 := by
    dsimp [Z]
    exact tauOne_xi_scalarProduct_self_of_hypothesis_10_4_data h
  have hZnorm : Section5.cfNormSq Z = 1 := by
    unfold Section5.cfNormSq
    rw [hZZ]
    simp
  have hnZnorm : Section5.cfNormSq ((n : ℂ) • Z) = (n : ℝ) ^ 2 := by
    rw [Section5.cfNormSq_smul, hZnorm]
    simp [pow_two]
  change Section5.cfNormSq Y = 2
  nlinarith

public theorem classFunction_eq_of_norm_eq_and_sub_orthogonal_pf105
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

public theorem classFunction_eq_signed_sub_of_norm_two_and_residual_orthogonal_pf105
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
  exact classFunction_eq_of_norm_eq_and_sub_orthogonal_pf105
    (Y := Y) (Z := Z) (by rw [hYnorm, hZnorm]) hRZ hZR

public theorem cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf105
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
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
            apply Finset.sum_congr
            · ext i
              simp
            · intro i _hi
              rfl
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

public theorem finite_orthonormal_virtual_coeff_support_card_le_two_pf105
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
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
    exact cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf105 w χ horth
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
    exact one_le_normSq_intCast_of_ne_zero_pf105 z hz_ne
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

public theorem finite_orthonormal_coeff_normSq_sum_le_two_pf105
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    {Y : Section1.ClassFunction G}
    (hYnorm : Section5.cfNormSq Y = 2) :
    (∑ i : ι, Complex.normSq (Section1.scalarProduct G Y (χ i))) ≤ 2 := by
  classical
  let w : ι → ℂ := fun i => Section1.scalarProduct G Y (χ i)
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
    simp [w]
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
    exact cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf105 w χ horth
  simpa [w, hPnorm] using hPnorm_le

public theorem coefficientNonzeroCount_sigma_omega_le_two_of_virtual_norm_two_pf105
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
    (hnotation : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
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
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
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
    finite_orthonormal_virtual_coeff_support_card_le_two_pf105
      χ horth hχvirt hYvirt hYnorm
  simpa [Section3.coefficientNonzeroCount, χ] using hcount

public theorem sigma_omega_coeff_normSq_sum_le_two_of_virtual_norm_two_pf105
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
    (hnotation : section10FourSixNotationData M W1 W2 W A A0 i0 j0 μ δSign ω σ τ)
    {Y : Section1.ClassFunction G}
    (hYnorm : Section5.cfNormSq Y = 2) :
    (∑ p : I × J,
      Complex.normSq (Section1.scalarProduct G Y (σ (ω p.1 p.2)))) ≤ 2 := by
  classical
  let χ : I × J → Section1.ClassFunction G := fun p => σ (ω p.1 p.2)
  have horth : ∀ p q : I × J,
      Section1.scalarProduct G (χ p) (χ q) = if p = q then 1 else 0 := by
    intro p q
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    dsimp [χ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
        hnotation i i' j j'
  simpa [χ] using
    finite_orthonormal_coeff_normSq_sum_le_two_pf105 χ horth hYnorm

public theorem finite_orthonormal_virtual_coeff_support_card_le_cfNormSq_pf109
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (χ : ι → Section1.ClassFunction G)
    (horth : ∀ i j : ι,
      Section1.scalarProduct G (χ i) (χ j) = if i = j then 1 else 0)
    (hχvirt : ∀ i, IsVirtualCharacter (χ i))
    {Y : Section1.ClassFunction G}
    (hYvirt : IsVirtualCharacter Y) :
    (Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} : ℝ) ≤
      Section5.cfNormSq Y := by
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
  have hPnorm_le : Section5.cfNormSq P ≤ Section5.cfNormSq Y := by
    have hRnonneg : 0 ≤ Section5.cfNormSq R := Section5.cfNormSq_nonneg R
    nlinarith
  have hPnorm :
      Section5.cfNormSq P = ∑ i : ι, Complex.normSq (w i) := by
    dsimp [P]
    exact cfNormSq_weightedFamilySum_orthonormal_eq_sum_normSq_pf105 w χ horth
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
    exact one_le_normSq_intCast_of_ne_zero_pf105 z hz_ne
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
  have hcard_real_le : (nz.card : ℝ) ≤ Section5.cfNormSq Y := by
    rw [← hPnorm] at hsum_nz_le_univ
    nlinarith
  have hcard_eq :
      Fintype.card {i : ι // Section1.scalarProduct G Y (χ i) ≠ 0} =
        nz.card := by
    dsimp [nz]
    rw [Fintype.card_subtype]
  simpa [hcard_eq] using hcard_real_le


public theorem coefficientNonzeroCount_sigma_omega_le_cfNormSq_pf109_supported
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
    (hYvirt : IsVirtualCharacter Y) :
    (Section3.coefficientNonzeroCount
        (fun i j => Section1.scalarProduct G Y (σ (ω i j))) : ℝ) ≤
      Section5.cfNormSq Y := by
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
    finite_orthonormal_virtual_coeff_support_card_le_cfNormSq_pf109
      χ horth hχvirt hYvirt
  simpa [Section3.coefficientNonzeroCount, χ] using hcount

public theorem coefficientNonzeroCount_le_four_of_two_cell_update_pf105
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a b : I → J → ℂ) {i0 : I} {j1 j2 : J}
    (hzero : ∀ i j, b i j ≠ 0 →
      a i j ≠ 0 ∨ (i, j) = (i0, j1) ∨ (i, j) = (i0, j2))
    (ha : Section3.coefficientNonzeroCount a ≤ 2) :
    Section3.coefficientNonzeroCount b ≤ 4 := by
  classical
  let suppA : Finset (I × J) :=
    Finset.univ.filter fun p : I × J => a p.1 p.2 ≠ 0
  let suppB : Finset (I × J) :=
    Finset.univ.filter fun p : I × J => b p.1 p.2 ≠ 0
  let extra : Finset (I × J) := {(i0, j1), (i0, j2)}
  have hsubset : suppB ⊆ suppA ∪ extra := by
    intro p hp
    rcases p with ⟨i, j⟩
    have hb : b i j ≠ 0 := (Finset.mem_filter.mp hp).2
    rcases hzero i j hb with haij | hcell | hcell
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨by simp, haij⟩)
    · exact Finset.mem_union_right _ (by simp [extra, hcell])
    · exact Finset.mem_union_right _ (by simp [extra, hcell])
  have hcardB : suppB.card ≤ (suppA ∪ extra).card :=
    Finset.card_le_card hsubset
  have hcard_union : (suppA ∪ extra).card ≤ suppA.card + extra.card :=
    Finset.card_union_le suppA extra
  have hextra : extra.card ≤ 2 := by
    dsimp [extra]
    by_cases h : (i0, j1) = (i0, j2)
    · simp [h]
    · simp [h]
  have hsuppA : Section3.coefficientNonzeroCount a = suppA.card := by
    dsimp [Section3.coefficientNonzeroCount, suppA]
    rw [Fintype.card_subtype]
  have hsuppB : Section3.coefficientNonzeroCount b = suppB.card := by
    dsimp [Section3.coefficientNonzeroCount, suppB]
    rw [Fintype.card_subtype]
  rw [hsuppB]
  rw [hsuppA] at ha
  omega

public theorem exists_two_ne_of_card_ge_three_pf105
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

public theorem three_le_coefficientNonzeroCount_of_three_nonzero_cells_pf105
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

public theorem normSq_add_sub_self_gt_two_of_normSq_one_pf105
    {c δ : ℂ} (hc : c ≠ 0) (hδ : Complex.normSq δ = 1) :
    (2 : ℝ) < Complex.normSq (c + δ) + Complex.normSq (c - δ) +
      Complex.normSq c := by
  have hcpos : 0 < Complex.normSq c := by
    have hnonneg := Complex.normSq_nonneg c
    have hne : Complex.normSq c ≠ 0 := by
      intro h0
      exact hc ((Complex.normSq_eq_zero).mp h0)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  rw [Complex.normSq_add, Complex.normSq_sub, hδ]
  nlinarith

public theorem normSq_three_cells_le_sum_pf105
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a : I → J → ℂ) (p q r : I × J)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Complex.normSq (a p.1 p.2) + Complex.normSq (a q.1 q.2) +
      Complex.normSq (a r.1 r.2) ≤
        ∑ x : I × J, Complex.normSq (a x.1 x.2) := by
  classical
  let s : Finset (I × J) := {p, q, r}
  have hs_sub : s ⊆ Finset.univ := by
    intro x _hx
    simp
  have hsum_s :
      Finset.sum s (fun x => Complex.normSq (a x.1 x.2)) =
        Complex.normSq (a p.1 p.2) + Complex.normSq (a q.1 q.2) +
          Complex.normSq (a r.1 r.2) := by
    simp [s, hpq, hpr, hqr, add_comm, add_left_comm]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hs_sub
    (by intro x _hxuniv _hxs; exact Complex.normSq_nonneg (a x.1 x.2))
  rw [← hsum_s]
  exact hle

public theorem two_cell_update_base_row_vanish_of_small_shape_pf105
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (a b : I → J → ℂ) {i0 : I} {j j0 : J} {δ : ℂ}
    (hj : j ≠ j0)
    (hδnorm : Complex.normSq δ = 1)
    (hI3 : 3 ≤ Fintype.card I)
    (hJ3 : 3 ≤ Fintype.card J)
    (ha_count : Section3.coefficientNonzeroCount a ≤ 2)
    (ha_norm : (∑ p : I × J, Complex.normSq (a p.1 p.2)) ≤ 2)
    (hshape :
      (∀ i k, b i k = 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ k : J,
          ∀ i q, b i q = if q = k then c else 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
          ∀ p q, b p q = if p = i then c else 0))
    (hupdate_j : a i0 j = b i0 j + δ)
    (hupdate_j0 : a i0 j0 = b i0 j0 - δ)
    (hupdate_other : ∀ i k, (i, k) ≠ (i0, j) → (i, k) ≠ (i0, j0) →
      a i k = b i k) :
    b i0 j = 0 ∧ b i0 j0 = 0 := by
  classical
  have hδne : δ ≠ 0 := by
    intro hδ0
    subst δ
    norm_num at hδnorm
  rcases hshape with hzero | hshape
  · exact ⟨hzero i0 j, hzero i0 j0⟩
  rcases hshape with hcol | hrow
  · rcases hcol with ⟨c, hc, k, hcol⟩
    by_cases hkj : k = j
    · subst k
      rcases exists_two_ne_of_card_ge_three_pf105 i0 hI3 with
        ⟨i1, i2, hi1, hi2, hi21⟩
      have hi1j_ne_active : (i1, j) ≠ (i0, j) := by
        intro hp
        exact hi1 (congrArg Prod.fst hp)
      have hi1j_ne_base : (i1, j) ≠ (i0, j0) := by
        intro hp
        exact hi1 (congrArg Prod.fst hp)
      have hi2j_ne_active : (i2, j) ≠ (i0, j) := by
        intro hp
        exact hi2 (congrArg Prod.fst hp)
      have hi2j_ne_base : (i2, j) ≠ (i0, j0) := by
        intro hp
        exact hi2 (congrArg Prod.fst hp)
      have h1 : a i1 j ≠ 0 := by
        rw [hupdate_other i1 j hi1j_ne_active hi1j_ne_base, hcol i1 j,
          if_pos rfl]
        exact hc
      have h2 : a i2 j ≠ 0 := by
        rw [hupdate_other i2 j hi2j_ne_active hi2j_ne_base, hcol i2 j,
          if_pos rfl]
        exact hc
      have hbase : a i0 j0 ≠ 0 := by
        rw [hupdate_j0, hcol i0 j0, if_neg (fun h => hj h.symm)]
        simpa using (neg_ne_zero.mpr hδne)
      have hthree : 3 ≤ Section3.coefficientNonzeroCount a :=
        three_le_coefficientNonzeroCount_of_three_nonzero_cells_pf105
          a (i1, j) (i2, j) (i0, j0)
          (by intro hp; exact hi21 (congrArg Prod.fst hp).symm)
          (by intro hp; exact hi1 (congrArg Prod.fst hp))
          (by intro hp; exact hi2 (congrArg Prod.fst hp))
          h1 h2 hbase
      omega
    · by_cases hkj0 : k = j0
      · subst k
        rcases exists_two_ne_of_card_ge_three_pf105 i0 hI3 with
          ⟨i1, i2, hi1, hi2, hi21⟩
        have hi1j0_ne_active : (i1, j0) ≠ (i0, j) := by
          intro hp
          exact hi1 (congrArg Prod.fst hp)
        have hi1j0_ne_base : (i1, j0) ≠ (i0, j0) := by
          intro hp
          exact hi1 (congrArg Prod.fst hp)
        have hi2j0_ne_active : (i2, j0) ≠ (i0, j) := by
          intro hp
          exact hi2 (congrArg Prod.fst hp)
        have hi2j0_ne_base : (i2, j0) ≠ (i0, j0) := by
          intro hp
          exact hi2 (congrArg Prod.fst hp)
        have h1 : a i1 j0 ≠ 0 := by
          rw [hupdate_other i1 j0 hi1j0_ne_active hi1j0_ne_base,
            hcol i1 j0, if_pos rfl]
          exact hc
        have h2 : a i2 j0 ≠ 0 := by
          rw [hupdate_other i2 j0 hi2j0_ne_active hi2j0_ne_base,
            hcol i2 j0, if_pos rfl]
          exact hc
        have hbase : a i0 j ≠ 0 := by
          rw [hupdate_j, hcol i0 j, if_neg hj]
          simpa using hδne
        have hthree : 3 ≤ Section3.coefficientNonzeroCount a :=
          three_le_coefficientNonzeroCount_of_three_nonzero_cells_pf105
            a (i1, j0) (i2, j0) (i0, j)
            (by intro hp; exact hi21 (congrArg Prod.fst hp).symm)
            (by intro hp; exact hi1 (congrArg Prod.fst hp))
            (by intro hp; exact hi2 (congrArg Prod.fst hp))
            h1 h2 hbase
        omega
      · constructor
        · rw [hcol i0 j, if_neg (fun h => hkj h.symm)]
        · rw [hcol i0 j0, if_neg (fun h => hkj0 h.symm)]
  · rcases hrow with ⟨c, hc, i, hrow⟩
    by_cases hii0 : i = i0
    · subst i
      rcases Section3.exists_other_ne_base_of_fintype_card_ge_three j0 j hj hJ3 with
        ⟨k, hk0, hkj⟩
      have hcell_kj : (i0, k) ≠ (i0, j) := by
        intro hp
        exact hkj (congrArg Prod.snd hp)
      have hcell_kj0 : (i0, k) ≠ (i0, j0) := by
        intro hp
        exact hk0 (congrArg Prod.snd hp)
      have haj : a i0 j = c + δ := by
        rw [hupdate_j, hrow i0 j, if_pos rfl]
      have haj0 : a i0 j0 = c - δ := by
        rw [hupdate_j0, hrow i0 j0, if_pos rfl]
      have hak : a i0 k = c := by
        rw [hupdate_other i0 k hcell_kj hcell_kj0, hrow i0 k, if_pos rfl]
      have hpq : (i0, j) ≠ (i0, j0) := by
        intro hp
        exact hj (congrArg Prod.snd hp)
      have hpr : (i0, j) ≠ (i0, k) := by
        intro hp
        exact hkj (congrArg Prod.snd hp).symm
      have hqr : (i0, j0) ≠ (i0, k) := by
        intro hp
        exact hk0 (congrArg Prod.snd hp).symm
      have hle :=
        normSq_three_cells_le_sum_pf105 a (i0, j) (i0, j0) (i0, k)
          hpq hpr hqr
      have hgt :
          (2 : ℝ) <
            Complex.normSq (a i0 j) + Complex.normSq (a i0 j0) +
              Complex.normSq (a i0 k) := by
        rw [haj, haj0, hak]
        exact normSq_add_sub_self_gt_two_of_normSq_one_pf105 hc hδnorm
      have hsum_gt : (2 : ℝ) <
          ∑ p : I × J, Complex.normSq (a p.1 p.2) :=
        lt_of_lt_of_le hgt hle
      exact False.elim ((not_lt_of_ge ha_norm) hsum_gt)
    · have hi0_ne_i : i0 ≠ i := fun h => hii0 h.symm
      exact ⟨by rw [hrow i0 j, if_neg hi0_ne_i],
        by rw [hrow i0 j0, if_neg hi0_ne_i]⟩

public theorem alphaChar_corrected_tau_residual_sigma_omega_count_le_four_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    Section3.coefficientNonzeroCount
        (fun i k =>
          Section1.scalarProduct G (Y - Z) (σ (ω i k))) ≤ 4 := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let a : I → J → ℂ := fun i k =>
    Section1.scalarProduct G Y (σ (ω i k))
  let b : I → J → ℂ := fun i k =>
    Section1.scalarProduct G (Y - Z) (σ (ω i k))
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_data h
  have ha : Section3.coefficientNonzeroCount a ≤ 2 := by
    dsimp [a, Y]
    exact coefficientNonzeroCount_sigma_omega_le_two_of_virtual_norm_two_pf105
      (section10FourSixNotation_of_hypothesis_10_4_data h)
      (Section3.isVirtualCharacter_add
        (alphaChar_tau_isVirtualCharacter_of_hypothesis_10_4_data h hj)
        (isVirtualCharacter_natCast_smul_sec10_base _
          (tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_data h)))
      (alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_data h hj)
  have hzero : ∀ i k, b i k ≠ 0 →
      a i k ≠ 0 ∨ (i, k) = (i0, j) ∨ (i, k) = (i0, j0) := by
    intro i k hb
    by_cases hcell : (i, k) = (i0, j)
    · exact Or.inr (Or.inl hcell)
    by_cases hcell0 : (i, k) = (i0, j0)
    · exact Or.inr (Or.inr hcell0)
    left
    intro ha0
    have hZik : Section1.scalarProduct G Z (σ (ω i k)) = 0 := by
      have hleft :
          Section1.scalarProduct G (σ (ω i0 j)) (σ (ω i k)) = 0 := by
        have hnot : ¬ (i0 = i ∧ j = k) := by
          rintro ⟨hi, hk⟩
          exact hcell (by simp [hi, hk])
        simpa [hnot] using
          scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
            hnotation i0 i j k
      have hright :
          Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i k)) = 0 := by
        have hnot : ¬ (i0 = i ∧ j0 = k) := by
          rintro ⟨hi, hk⟩
          exact hcell0 (by simp [hi, hk])
        simpa [hnot] using
          scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
            hnotation i0 i j0 k
      dsimp [Z]
      rw [Section1.scalarProduct_smul_left, Section5.scalarProduct_sub_left,
        hleft, hright]
      simp
    apply hb
    dsimp [b, a] at ha0 ⊢
    rw [Section5.scalarProduct_sub_left, ha0, hZik]
    simp
  simpa [Y, Z, b] using
    coefficientNonzeroCount_le_four_of_two_cell_update_pf105 a b hzero ha

public theorem alphaChar_fourTenTerm_pairing_eq_signed_rectangle_pairing_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0)
    (i : I) (k : J) :
    let B : Section1.ClassFunction M :=
      (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let R : Section1.ClassFunction G :=
      (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i0 j) B =
      Section1.scalarProduct G Z R := by
  classical
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let R : Section1.ClassFunction G :=
    (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_data h
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_data h
  rcases h104a with ⟨h10, _hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, hdeg, hsign, _hdn⟩
  rcases fullFourSixData_of_hypothesis_10_4_data h with
    ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt⟩
  have h43bAll := h43b
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigma⟩
  rcases h46.1 with
    ⟨_hSemidirect, _hHall, _hCyclicW1, hW1ne1Sub, _hCyclicW2, _hW2ne1,
      _hCentralizer, _hW1W, _hW2W, _hDirect, _hOdd⟩
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hW1ne1 : Nat.card W1 ≠ 1 := by
    intro hcard
    exact hW1ne1Sub (by rw [hW1cardSub, hcard])
  have hW1gt : 1 < Nat.card W1 := by
    have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
    omega
  have hdneW1 : d ≠ Nat.card W1 := by
    intro hdw
    subst d
    rcases hδsign with rfl | rfl
    · have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast _hnpos
      nlinarith [mul_le_mul_of_nonneg_right hn1
        (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
          (0 : ℤ) ≤ Nat.card W1)]
    · by_cases hn_eq : n = 1
      · subst n
        norm_num at _hdn
      · have hn2_nat : 2 ≤ n := by omega
        have hn2 : (2 : ℤ) ≤ n := by exact_mod_cast hn2_nat
        nlinarith [mul_le_mul_of_nonneg_right hn2
          (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_succ_lt hW1gt) :
            (0 : ℤ) ≤ Nat.card W1)]
  have hξμ : ∀ a b, Section1.scalarProduct M ξ (μ a b) = 0 := by
    intro a b
    by_cases hb : b = j0
    · subst b
      have hbase_ne : μ a j0 ≠ ξ := by
        intro hEq
        have hdegEq : (1 : ℂ) = (Nat.card W1 : ℂ) := by
          calc
            (1 : ℂ) = Section1.degree (μ a j0) :=
              (baseColumn_degree_one_of_section10FourSixNotationData hnotation a).symm
            _ = Section1.degree ξ := by rw [hEq]
            _ = (Nat.card W1 : ℂ) := hξDegree
        have hcard : Nat.card W1 = 1 := by exact_mod_cast hdegEq.symm
        exact hW1ne1 hcard
      have hμξ : Section1.scalarProduct M (μ a j0) ξ = 0 :=
        scalarProduct_irreducible_ne (hirr a j0) hξIrr hbase_ne
      simpa [Section1.scalarProduct_star_swap] using congrArg star hμξ
    · have hentry_ne : μ a b ≠ ξ := by
        intro hEq
        have hdegEq : (d : ℂ) = (Nat.card W1 : ℂ) := by
          calc
            (d : ℂ) = Section1.degree (μ a b) := (hdeg a b hb).symm
            _ = Section1.degree ξ := by rw [hEq]
            _ = (Nat.card W1 : ℂ) := hξDegree
        have hdw : d = Nat.card W1 := by exact_mod_cast hdegEq
        exact hdneW1 hdw
      have hμξ : Section1.scalarProduct M (μ a b) ξ = 0 :=
        scalarProduct_irreducible_ne (hirr a b) hξIrr hentry_ne
      simpa [Section1.scalarProduct_star_swap] using congrArg star hμξ
  have hμorth : ∀ a b c e,
      Section1.scalarProduct M (μ a b) (μ c e) =
        if (a, b) = (c, e) then (1 : ℂ) else 0 := by
    intro a b c e
    by_cases hp : (a, b) = (c, e)
    · have hac : a = c := congrArg Prod.fst hp
      have hbe : b = e := congrArg Prod.snd hp
      subst c
      subst e
      simp [scalarProduct_irreducible_self (hirr a b)]
    · have hne : μ a b ≠ μ c e := hdistinct (a, b) (c, e) hp
      simp [hp, scalarProduct_irreducible_ne (hirr a b) (hirr c e) hne]
  have hσorth : ∀ a b c e,
      Section1.scalarProduct G (σ (ω a b)) (σ (ω c e)) =
        if (a, b) = (c, e) then (1 : ℂ) else 0 := by
    intro a b c e
    exact scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
      hnotation a c b e
  have hδj : (δSign j : ℂ) = (δ : ℂ) := by
    rw [hsign j hj]
  have hδsq : (δ : ℂ) * (δ : ℂ) = 1 := by
    rcases hδsign with rfl | rfl <;> norm_num
  have hδ0 : (δSign j0 : ℂ) = (1 : ℂ) := by
    rcases hnotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, h46, _hω33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    exact (Section4.proposition_4_4_base
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      (I := I)
      (J := J)
      (i0 := i0)
      (j0 := j0)
      (ω := ω)
      (σ := _σM)
      (piChar := μ)
      (deltaSign := fun j => (δSign j : ℂ))
      hω h43bAll).1
  have hα :
      alphaChar μ ξ n δ j0 i0 j =
        μ i0 j + (-(δ : ℂ)) • μ i0 j0 + (-(n : ℂ)) • ξ := by
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
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i0 j) B =
      Section1.scalarProduct G Z R
  rw [hα, hB, hZ, hR]
  simp only [Section1.scalarProduct_add_left, Section5.scalarProduct_add_right,
    Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
    hμorth, hξμ, hσorth]
  by_cases hkj : k = j
  · subst k
    have hj' : j0 ≠ j := fun h => hj h.symm
    by_cases hi : i0 = i
    · simp [hδj, hj, hj', hi]
    · simp [hδj, hj, hj', hi]
  · by_cases hk0 : k = j0
    · subst k
      simp [hδ0, hj]
    · have hδk : (δSign k : ℂ) = (δ : ℂ) := by
        rw [hsign k hk0]
      simp [hδk, hj]
      have hjk : j ≠ k := fun h => hkj h.symm
      have hj0k : j0 ≠ k := fun h => hk0 h.symm
      simp [hjk, hj0k]

public theorem fourTenTerm_supportedOn_a0_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    (i : I) (k : J) :
    Section1.supportedOn
      ((δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0)
      (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
  classical
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_data h
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, _hδsign, _hnpos, hdeg, _hsign, _hdn⟩
  have hdegCol : Section1.degree (μ i k) = Section1.degree (μ i0 k) := by
    by_cases hk : k = j0
    · subst k
      rw [baseColumn_degree_one_of_section10FourSixNotationData hnotation i,
        baseColumn_degree_one_of_section10FourSixNotationData hnotation i0]
    · rw [hdeg i k hk, hdeg i0 k hk]
  have hbase_i : μ i j0 1 = (1 : ℂ) := by
    simpa [Section1.degree] using
      baseColumn_degree_one_of_section10FourSixNotationData hnotation i
  have hbase_i0 : μ i0 j0 1 = (1 : ℂ) := by
    simpa [Section1.degree] using
      baseColumn_degree_one_of_section10FourSixNotationData hnotation i0
  have hcol_eval : μ i k 1 = μ i0 k 1 := by
    simpa [Section1.degree] using hdegCol
  have hBdeg : Section1.degree B = 0 := by
    unfold Section1.degree
    simp [B, hcol_eval, hbase_i, hbase_i0, Pi.sub_apply, Pi.smul_apply]
  have hpunct :
      Section4Scratch.puncturedSet ⊆
        Section4Scratch.a0Set (W2.subgroupOf M) W A := by
    rcases hnotation with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    intro x hx
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46 hx
  simpa [B] using supportedOn_of_degree_eq_zero_of_punctured_subset hpunct hBdeg

public theorem alphaChar_corrected_tau_residual_sigma_omega_base_rectangle_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0)
    (i : I) (k : J) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let R : Section1.ClassFunction G :=
      (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
    Section1.scalarProduct G (Y - Z) R = 0 := by
  classical
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ξ n δ j0 i0 j)
  let Y : Section1.ClassFunction G := Aτ + (n : ℂ) • τ₁ ξ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let R : Section1.ClassFunction G :=
    (σ (ω i k) - σ (ω i0 k)) - (σ (ω i j0) - σ (ω i0 j0))
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  have hτ₁R : Section1.scalarProduct G (τ₁ ξ) R = 0 := by
    have h1 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i k)) = 0 :=
      tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data h i k
    have h2 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i0 k)) = 0 :=
      tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data h i0 k
    have h3 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i j0)) = 0 :=
      tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data h i j0
    have h4 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i0 j0)) = 0 :=
      tauOne_xi_orthogonal_omega_of_hypothesis_10_4_data h i0 j0
    dsimp [R]
    rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, h1, h2, h3, h4]
    simp
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i0 j)
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hnotation := section10FourSixNotation_of_hypothesis_10_4_data h
    have hA0 :
        A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hnotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hA0
    have hαA0' : Section1.supportedOn (alphaChar μ ξ n δ j0 i0 j) A0 :=
      alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
        (hypothesis_10_4_a_of_hypothesis_10_4_data h) hj
    simpa [hA0] using hαA0'
  have hBA0 :
      Section1.supportedOn B
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    simpa [B] using fourTenTerm_supportedOn_a0_of_hypothesis_10_4_data h i k
  have hαClass : Section1.IsClassFunction (alphaChar μ ξ n δ j0 i0 j) :=
    Section1.isVirtualCharacter_isClassFunction
      (alphaChar_isVirtualCharacter_of_hypothesis_10_4_data h i0 j)
  have hBClass : Section1.IsClassFunction B := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        _h22A0, _hDadeA0, hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    have hmuClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (h43b.2.2.1 i j))
    intro x g
    simp [B, hmuClass i k x g, hmuClass i0 k x g,
      hmuClass i j0 x g, hmuClass i0 j0 x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_a0_statement (W2.subgroupOf M) W A τ := by
    rcases fullFourSixData_of_hypothesis_10_4_data h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt⟩
    exact hτiso
  have hRτB : τ B = R := by
    have h410 := theorem_4_10_of_section10FourSixNotationData
      (section10FourSixNotation_of_hypothesis_10_4_data h) i k
    simpa [B, R] using h410
  have hAτR : Section1.scalarProduct G Aτ R = Section1.scalarProduct G Z R := by
    have hsource :=
      alphaChar_fourTenTerm_pairing_eq_signed_rectangle_pairing_of_hypothesis_10_4_data
        h hj i k
    calc
      Section1.scalarProduct G Aτ R =
          Section1.scalarProduct G (τ (alphaChar μ ξ n δ j0 i0 j)) (τ B) := by
            simp [Aτ, hRτB]
      _ = Section1.scalarProduct M (alphaChar μ ξ n δ j0 i0 j) B := by
            exact hτiso (alphaChar μ ξ n δ j0 i0 j) B hαClass hBClass hαA0 hBA0
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

public theorem alphaChar_corrected_tau_residual_sigma_omega_rectangle_relation_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    let b : I → J → ℂ := fun i k =>
      Section1.scalarProduct G (Y - Z) (σ (ω i k))
    ∀ i i' k k', b i k + b i' k' = b i k' + b i' k := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let b : I → J → ℂ := fun i k =>
    Section1.scalarProduct G (Y - Z) (σ (ω i k))
  have hbase : ∀ i k, b i k = b i0 k + b i j0 - b i0 j0 := by
    intro i k
    have hzero :=
      alphaChar_corrected_tau_residual_sigma_omega_base_rectangle_of_hypothesis_10_4_data
        h hj i k
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

public theorem alphaChar_corrected_tau_residual_sigma_omega_orthogonal_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    let Y : Section1.ClassFunction G :=
      τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
    let Z : Section1.ClassFunction G :=
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
    Section1.scalarProduct G (Y - Z) (σ (ω i0 j)) = 0 ∧
      Section1.scalarProduct G (Y - Z) (σ (ω i0 j0)) = 0 := by
  classical
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
  let Z : Section1.ClassFunction G :=
    (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0))
  let a : I → J → ℂ := fun i k =>
    Section1.scalarProduct G Y (σ (ω i k))
  let b : I → J → ℂ := fun i k =>
    Section1.scalarProduct G (Y - Z) (σ (ω i k))
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_data h
  have hnotationData := hnotation
  rcases hnotationData with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource, _hW, _hA0, _h46, hω,
      _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _hTauA0, _hfull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W _h46.1).2
  have hI3 : 3 ≤ Fintype.card I := by
    rw [hω.card_left]
    exact Section3.natCard_left_ge_three_of_hypothesis_3_1 h31
  have hJ3 : 3 ≤ Fintype.card J := by
    rw [hω.card_right]
    exact Section3.natCard_right_ge_three_of_hypothesis_3_1 h31
  have hoddI : Odd (Fintype.card I) := by
    rw [hω.card_left]
    exact Section3.odd_natCard_left_of_hypothesis_3_1 h31
  have hoddJ : Odd (Fintype.card J) := by
    rw [hω.card_right]
    exact Section3.odd_natCard_right_of_hypothesis_3_1 h31
  have hcards_ne : Fintype.card I ≠ Fintype.card J := by
    intro hEq
    have hcop : Nat.Coprime (Fintype.card I) (Fintype.card J) := by
      simpa [hω.card_left, hω.card_right] using
        Section3.natCard_left_right_coprime_of_hypothesis_3_1 h31
    rw [hEq] at hcop
    have hgt : 1 < Fintype.card J := by omega
    exact (Nat.not_coprime_of_dvd_of_dvd hgt (dvd_refl _) (dvd_refl _)) hcop
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by
    rcases uniformMuData_of_hypothesis_10_4_data h with
      ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
    rcases hδsign with rfl | rfl <;> norm_num
  have hYnorm : Section5.cfNormSq Y = 2 := by
    dsimp [Y]
    exact alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_data h hj
  have ha_count : Section3.coefficientNonzeroCount a ≤ 2 := by
    dsimp [a, Y]
    exact coefficientNonzeroCount_sigma_omega_le_two_of_virtual_norm_two_pf105
      (section10FourSixNotation_of_hypothesis_10_4_data h)
      (Section3.isVirtualCharacter_add
        (alphaChar_tau_isVirtualCharacter_of_hypothesis_10_4_data h hj)
        (isVirtualCharacter_natCast_smul_sec10_base _
          (tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_data h)))
      (alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_data h hj)
  have ha_norm : (∑ p : I × J, Complex.normSq (a p.1 p.2)) ≤ 2 := by
    dsimp [a]
    exact sigma_omega_coeff_normSq_sum_le_two_of_virtual_norm_two_pf105
      hnotation hYnorm
  have hb_count : Section3.coefficientNonzeroCount b ≤ 4 := by
    dsimp [b, Y, Z]
    simpa using
      alphaChar_corrected_tau_residual_sigma_omega_count_le_four_of_hypothesis_10_4_data
        h hj
  have hrect : ∀ i i' k k', b i k + b i' k' = b i k' + b i' k := by
    dsimp [b, Y, Z]
    simpa using
      alphaChar_corrected_tau_residual_sigma_omega_rectangle_relation_of_hypothesis_10_4_data
        h hj
  have hshape :
      (∀ i k, b i k = 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ k : J,
          ∀ i q, b i q = if q = k then c else 0) ∨
        (∃ c : ℂ, c ≠ 0 ∧ ∃ i : I,
          ∀ p q, b p q = if p = i then c else 0) := by
    by_cases hltIJ : Fintype.card I < Fintype.card J
    · have hb_lt : Section3.coefficientNonzeroCount b < 2 * Fintype.card I := by
        omega
      exact Section3.coefficient_rectangle_small_shape b hrect hb_lt hoddI hoddJ
        hltIJ hI3
    · have hltJI : Fintype.card J < Fintype.card I := by omega
      let bT : J → I → ℂ := fun k i => b i k
      have hrectT : ∀ k k' i i', bT k i + bT k' i' = bT k i' + bT k' i := by
        intro k k' i i'
        simpa [bT, add_comm, add_left_comm] using hrect i i' k k'
      have hcountT : Section3.coefficientNonzeroCount bT =
          Section3.coefficientNonzeroCount b := by
        simpa [bT] using Section3.coefficientNonzeroCount_swap b
      have hbT_lt : Section3.coefficientNonzeroCount bT < 2 * Fintype.card J := by
        rw [hcountT]
        omega
      rcases Section3.coefficient_rectangle_small_shape bT hrectT hbT_lt hoddJ hoddI
          hltJI hJ3 with hzero | hshapeT
      · exact Or.inl (fun i k => hzero k i)
      · rcases hshapeT with hcolT | hrowT
        · rcases hcolT with ⟨c, hc, i, hcolT⟩
          exact Or.inr <| Or.inr ⟨c, hc, i, fun p q => hcolT q p⟩
        · rcases hrowT with ⟨c, hc, k, hrowT⟩
          exact Or.inr <| Or.inl ⟨c, hc, k, fun i q => hrowT q i⟩
  have hZ_j :
      Section1.scalarProduct G Z (σ (ω i0 j)) = (δ : ℂ) := by
    have hφφ : Section1.scalarProduct G (σ (ω i0 j)) (σ (ω i0 j)) = 1 := by
      simpa using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
          hnotation i0 i0 j j
    have hψφ :
        Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i0 j)) = 0 := by
      have hj' : j0 ≠ j := fun hEq => hj hEq.symm
      simpa [hj'] using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
          hnotation i0 i0 j0 j
    dsimp [Z]
    rw [Section1.scalarProduct_smul_left, Section5.scalarProduct_sub_left,
      hφφ, hψφ]
    ring
  have hZ_j0 :
      Section1.scalarProduct G Z (σ (ω i0 j0)) = -(δ : ℂ) := by
    have hφψ : Section1.scalarProduct G (σ (ω i0 j)) (σ (ω i0 j0)) = 0 := by
      simpa [hj] using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
          hnotation i0 i0 j j0
    have hψψ :
        Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i0 j0)) = 1 := by
      simpa using
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
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
          scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
            hnotation i0 i j k
      have hright :
          Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i k)) = 0 := by
        have hnot : ¬ (i0 = i ∧ j0 = k) := by
          rintro ⟨hi, hk⟩
          exact hcell0 (by simp [hi, hk])
        simpa [hnot] using
          scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
            hnotation i0 i j0 k
      dsimp [Z]
      rw [Section1.scalarProduct_smul_left, Section5.scalarProduct_sub_left,
        hleft, hright]
      simp
    dsimp [a, b]
    rw [Section5.scalarProduct_sub_left, hZik]
    simp
  simpa [Y, Z, b] using
    two_cell_update_base_row_vanish_of_small_shape_pf105
      a b hj hδnorm hI3 hJ3 ha_count ha_norm hshape
      hupdate_j hupdate_j0 hupdate_other

public theorem alphaChar_corrected_tau_residual_eq_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ =
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) := by
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
  let φ : Section1.ClassFunction G := σ (ω i0 j)
  let ψ : Section1.ClassFunction G := σ (ω i0 j0)
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by
    rcases hδsign with rfl | rfl <;> norm_num
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_data h
  have hφφ : Section1.scalarProduct G φ φ = 1 := by
    dsimp [φ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
        hnotation i0 i0 j j
  have hψψ : Section1.scalarProduct G ψ ψ = 1 := by
    dsimp [ψ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
        hnotation i0 i0 j0 j0
  have hφψ : Section1.scalarProduct G φ ψ = 0 := by
    dsimp [φ, ψ]
    simpa [hj] using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
        hnotation i0 i0 j j0
  have hψφ : Section1.scalarProduct G ψ φ = 0 := by
    have hj' : j0 ≠ j := fun hEq => hj hEq.symm
    dsimp [φ, ψ]
    simpa [hj'] using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationData
        hnotation i0 i0 j0 j
  have hYnorm : Section5.cfNormSq Y = 2 := by
    dsimp [Y]
    exact alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_data h hj
  rcases alphaChar_corrected_tau_residual_sigma_omega_orthogonal_of_hypothesis_10_4_data
      h hj with
    ⟨hRφ, hRψ⟩
  have hYeq : Y = (δ : ℂ) • (φ - ψ) :=
    classFunction_eq_signed_sub_of_norm_two_and_residual_orthogonal_pf105
      hδnorm hφφ hψψ hφψ hψφ hYnorm
      (by simpa [Y, φ, ψ] using hRφ)
      (by simpa [Y, φ, ψ] using hRψ)
  simpa [Y, φ, ψ] using hYeq

public theorem alphaChar_baseRow_tau_formula_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    τ (alphaChar μ ξ n δ j0 i0 j) =
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) - (n : ℂ) • τ₁ ξ := by
  have hY :=
    alphaChar_corrected_tau_residual_eq_of_hypothesis_10_4_data h hj
  calc
    τ (alphaChar μ ξ n δ j0 i0 j) =
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) -
          (n : ℂ) • τ₁ ξ := by
          ext x
          simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    _ = (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) - (n : ℂ) • τ₁ ξ := by
          rw [hY]

public theorem alphaChar_tau_formula_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    τ (alphaChar μ ξ n δ j0 i j) =
      (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) - (n : ℂ) • τ₁ ξ := by
  have hbase :=
    alphaChar_baseRow_tau_formula_of_hypothesis_10_4_data h hj
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_data h
  have h410 := theorem_4_10_of_hypothesis_10_4_a_data h104a
  rcases h104a with
    ⟨_h10, _hNotation, _hξS, _hξIrr, _hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, _hdeg, hsign, _hdn⟩
  have hδsq : ((δ : ℂ) * (δ : ℂ) = 1) := by
    rcases hδsign with rfl | rfl <;> norm_num
  have hδj : δSign j = δ := hsign j hj
  have hfour :
      τ ((δ : ℂ) • μ i j - (δ : ℂ) • μ i0 j - μ i j0 + μ i0 j0) =
        (σ (ω i j) - σ (ω i0 j)) - (σ (ω i j0) - σ (ω i0 j0)) := by
    simpa [hδj] using h410 i j
  have hdiff_arg :
      alphaChar μ ξ n δ j0 i j - alphaChar μ ξ n δ j0 i0 j =
        (δ : ℂ) •
          ((δ : ℂ) • μ i j - (δ : ℂ) • μ i0 j - μ i j0 + μ i0 j0) :=
    alphaChar_sub_baseRow_eq_sign_smul_fourTenTerm μ ξ n δ j0 i i0 j hδsq
  have hdiff :
      τ (alphaChar μ ξ n δ j0 i j - alphaChar μ ξ n δ j0 i0 j) =
        (δ : ℂ) • ((σ (ω i j) - σ (ω i0 j)) -
          (σ (ω i j0) - σ (ω i0 j0))) := by
    rw [hdiff_arg, map_smul, hfour]
  have hadd :
      τ (alphaChar μ ξ n δ j0 i j) =
        τ (alphaChar μ ξ n δ j0 i j - alphaChar μ ξ n δ j0 i0 j) +
          τ (alphaChar μ ξ n δ j0 i0 j) := by
    rw [← map_add]
    congr 1
    abel
  rw [hadd, hdiff, hbase]
  ext x
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring


public theorem alphaChar_scalarProduct_muColumn_eq_one_of_hypothesis_10_4_data
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) (muColumn μ j) = 1 := by
  classical
  have hentry :
      Section1.scalarProduct M (μ i j) (muColumn μ j) = 1 := by
    simpa using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_data h i j j
  have hbase :
      Section1.scalarProduct M (μ i j0) (muColumn μ j) = 0 := by
    simpa [hj.symm] using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_data h i j0 j
  rcases hypothesis_10_4_a_of_hypothesis_10_4_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, _hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hcolS : muColumn μ j ∈ S := muColumn_mem_of_hypothesis_10_4_data h hj
  have hne : ξ ≠ muColumn μ j := by
    intro hEq
    have hdegEq :
        Section1.degree (muColumn μ j) = Section1.degree ξ := by
      rw [← hEq]
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_data h hj
    rw [hcoldeg, hξDegree] at hdegEq
    have hW1ne : (Nat.card W1 : ℂ) ≠ 0 := by
      have hW1pos : 0 < Nat.card W1 := Nat.card_pos (α := W1)
      have hW1natNe : Nat.card W1 ≠ 0 := Nat.ne_of_gt hW1pos
      exact_mod_cast hW1natNe
    have hdEq : (d : ℂ) = 1 := by
      exact mul_right_cancel₀ hW1ne (by simpa using hdegEq)
    have hdne : (d : ℂ) ≠ 1 := by
      exact_mod_cast (ne_of_gt hdpos)
    exact hdne hdEq
  rcases hypothesis_5_2_of_hypothesis_10_1 h10 with
    ⟨_hSetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
  have hξcol :
      Section1.scalarProduct M ξ (muColumn μ j) = 0 :=
    h52c hξS hcolS hne
  have halpha :
      alphaChar μ ξ n δ j0 i j =
        μ i j + (-(δ : ℂ)) • μ i j0 + (-(n : ℂ)) • ξ := by
    ext x
    simp [alphaChar, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
    ring
  rw [halpha]
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_add_left]
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
  rw [hentry, hbase, hξcol]
  simp

public theorem alphaChar_mixed_scalarProduct_muColumn_transfer_obligation
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i j))
      (τ₁ (muColumn μ j)) =
    Section1.scalarProduct M
      (alphaChar μ ξ n δ j0 i j)
      (muColumn μ j) := by
  classical
  let α : Section1.ClassFunction M := alphaChar μ ξ n δ j0 i j
  let col : Section1.ClassFunction M := muColumn μ j
  let diff : Section1.ClassFunction M := col - (d : ℂ) • ξ
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_data _h
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data _h
  rcases h104a with ⟨_h10, _hNotation', hξS, hξIrr, hξDegree, _hUniform⟩
  have hαA0 :
      Section1.supportedOn α
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hA0 :
        A0 = Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hNotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      exact hA0
    have hαA0' :
        Section1.supportedOn (alphaChar μ ξ n δ j0 i j) A0 :=
      alphaChar_supportedOn_a0_of_hypothesis_10_4_a_data
        (hypothesis_10_4_a_of_hypothesis_10_4_data _h) hj
    simpa [α, hA0] using hαA0'
  have hdiffA0 :
      Section1.supportedOn diff
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    have hpunct :
        Section4Scratch.puncturedSet ⊆
          Section4Scratch.a0Set (W2.subgroupOf M) W A := by
      rcases hNotation with
        ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
          _hW, _hA0, h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
            _hFull⟩
      intro x hx
      exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46 hx
    have hdeg : Section1.degree diff = 0 := by
      have hcoldeg := degree_muColumn_of_hypothesis_10_4_data _h hj
      have hcol1 : col 1 = (d : ℂ) * (Nat.card W1 : ℂ) := by
        simpa [col, Section1.degree] using hcoldeg
      have hxi1 : ξ 1 = (Nat.card W1 : ℂ) := by
        simpa [Section1.degree] using hξDegree
      rw [Section1.degree]
      simp [diff, col, Pi.sub_apply, Pi.smul_apply, hcol1, hxi1]
    exact supportedOn_of_degree_eq_zero_of_punctured_subset hpunct hdeg
  have hτiso :
      Section4Scratch.tau_isometry_on_a0_statement (W2.subgroupOf M) W A τ := by
    rcases fullFourSixData_of_hypothesis_10_4_data _h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, _h22A0, _hDadeA0,
        hFullRest⟩
    rcases hFullRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt⟩
    exact hτiso
  have hαClass : Section1.IsClassFunction α :=
    Section1.isVirtualCharacter_isClassFunction
      (by
        simpa [α] using
          alphaChar_isVirtualCharacter_of_hypothesis_10_4_data _h i j)
  have hdiffClass : Section1.IsClassFunction diff := by
    rcases fullFourSixData_of_hypothesis_10_4_data _h with
      ⟨_σM, _xChar, _H_A, _H_A0, hFull⟩
    rcases hFull with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        _h22A0, _hDadeA0, hFullRest⟩
    rcases hFullRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    have hmuClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (h43b.2.2.1 i j))
    have hcolClass : Section1.IsClassFunction col := by
      subst col
      intro x g
      unfold muColumn
      simpa using Finset.sum_congr rfl (fun i _hi => hmuClass i j x g)
    have hξClass : Section1.IsClassFunction ξ :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
    have hsmulClass : Section1.IsClassFunction ((d : ℂ) • ξ) :=
      Section1.isClassFunction_smul (d : ℂ) ξ hξClass
    intro x g
    simp [diff, hcolClass x g, hsmulClass x g]
  have hτdiff : τ₁ diff = τ diff := by
    simpa [diff, col] using
      tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_data _h hj
  have hτξself : Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) = 1 := by
    have hspanξ : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
    calc
      Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) =
          Section1.scalarProduct M ξ ξ :=
        (extensionInterfaces_of_hypothesis_10_4_data _h).1 ξ ξ hspanξ hspanξ
      _ = 1 := scalarProduct_irreducible_self hξIrr
  have hτξ :
      Section1.scalarProduct G (τ α) (τ₁ ξ) = -(n : ℂ) := by
    have hformula :=
      alphaChar_tau_formula_of_hypothesis_10_4_data _h (i := i) hj
    have homega :
        Section1.scalarProduct G (σ (ω i j) - σ (ω i j0)) (τ₁ ξ) = 0 := by
      rw [Section5.scalarProduct_sub_left]
      rw [sigma_omega_orthogonal_tauOne_xi_of_hypothesis_10_4_data _h i j]
      rw [sigma_omega_orthogonal_tauOne_xi_of_hypothesis_10_4_data _h i j0]
      simp
    change
      Section1.scalarProduct G (τ (alphaChar μ ξ n δ j0 i j)) (τ₁ ξ) =
        -(n : ℂ)
    rw [hformula]
    rw [show (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) - (n : ℂ) • τ₁ ξ =
        (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) + (-(n : ℂ)) • τ₁ ξ by
          ext x
          simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
          ring]
    rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left]
    rw [homega, hτξself]
    simp
  have hαξ :
      Section1.scalarProduct M α ξ = -(n : ℂ) := by
    simpa [α] using
      alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_data _h hj
  have hiso :
      Section1.scalarProduct G (τ α) (τ diff) =
        Section1.scalarProduct M α diff :=
    hτiso α diff hαClass hdiffClass hαA0 hdiffA0
  have hcol_decomp : col = diff + (d : ℂ) • ξ := by
    ext x
    simp [diff, col, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  have hleft :
      Section1.scalarProduct G (τ α) (τ₁ col) =
        Section1.scalarProduct M α diff + (d : ℂ) * (-(n : ℂ)) := by
    calc
      Section1.scalarProduct G (τ α) (τ₁ col) =
          Section1.scalarProduct G (τ α) (τ₁ (diff + (d : ℂ) • ξ)) := by
            rw [hcol_decomp]
      _ = Section1.scalarProduct G (τ α) (τ₁ diff + (d : ℂ) • τ₁ ξ) := by
            rw [map_add, map_smul]
      _ = Section1.scalarProduct G (τ α) (τ₁ diff) +
            Section1.scalarProduct G (τ α) ((d : ℂ) • τ₁ ξ) := by
            rw [Section5.scalarProduct_add_right]
      _ = Section1.scalarProduct G (τ α) (τ diff) +
            (d : ℂ) * Section1.scalarProduct G (τ α) (τ₁ ξ) := by
            rw [hτdiff, Section1.scalarProduct_smul_right]
            simp
      _ = Section1.scalarProduct M α diff + (d : ℂ) * (-(n : ℂ)) := by
            rw [hiso, hτξ]
  have hright :
      Section1.scalarProduct M α col =
        Section1.scalarProduct M α diff + (d : ℂ) * (-(n : ℂ)) := by
    calc
      Section1.scalarProduct M α col =
          Section1.scalarProduct M α (diff + (d : ℂ) • ξ) := by
            rw [hcol_decomp]
      _ = Section1.scalarProduct M α diff +
            Section1.scalarProduct M α ((d : ℂ) • ξ) := by
            rw [Section5.scalarProduct_add_right]
      _ = Section1.scalarProduct M α diff +
            (d : ℂ) * Section1.scalarProduct M α ξ := by
            rw [Section1.scalarProduct_smul_right]
            simp
      _ = Section1.scalarProduct M α diff + (d : ℂ) * (-(n : ℂ)) := by
            rw [hαξ]
  simpa [α, col] using hleft.trans hright.symm

public theorem theorem_10_6_nonbase_column_formula_of_pairing
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0)
    (hpair : ∀ i : I,
      Section1.scalarProduct G
        ((δ : ℂ) • (σ (ω i j) - σ (ω i j0)))
        (τ₁ (muColumn μ j)) = 1) :
    τ₁ (muColumn μ j) =
      (δ : ℂ) • (∑ i : I, σ (ω i j)) := by
  classical
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_data h
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, _hδsign, _hnpos, _hdeg, hsign, _hdn⟩
  have hδj : δSign j = δ := hsign j hj
  rcases fiveEightAlternative_muColumn_of_hypothesis_10_4_data h hj with hpos | hneg
  · simpa [Section4Scratch.omegaColumnSigma, hδj] using hpos
  · rcases hneg with ⟨j', hj'0, _hconj, hne, hnegFormula, _hunique⟩
    have hjj' : j ≠ j' := by
      intro hEq
      subst j'
      exact hne rfl
    have hzero :
        Section1.scalarProduct G
          ((δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)))
          (τ₁ (muColumn μ j)) = 0 := by
      rw [hnegFormula]
      rw [Section1.scalarProduct_smul_right, Section1.scalarProduct_smul_left]
      rw [show σ (ω i0 j) - σ (ω i0 j0) =
          σ (ω i0 j) + (-1 : ℂ) • σ (ω i0 j0) by
            ext x
            simp [Pi.sub_apply, Pi.add_apply]
            ring]
      rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]
      have hsame :=
        Section10.scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationData
          hNotation i0 j j'
      have hbase :=
        Section10.scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationData
          hNotation i0 j0 j'
      rw [hsame, hbase]
      have hj0j' : j0 ≠ j' := fun hEq => hj'0 hEq.symm
      simp [hjj', hj0j']
    have hone := hpair i0
    rw [hzero] at hone
    norm_num at hone

public theorem theorem_10_6_nonbase_column_formula_obligation
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∀ j, j ≠ j0 →
      τ₁ (muColumn μ j) =
        (δ : ℂ) • (∑ i : I, σ (ω i j)) := by
  -- PF (10.6.a), docs/PFsection10.tex lines 150-159: use `(10.5)` and
  -- the scalar-product computation to choose the positive `(5.8)` branch.
  intro j hj
  refine theorem_10_6_nonbase_column_formula_of_pairing _h hj ?_
  intro i
  have htauPair :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i j))
        (τ₁ (muColumn μ j)) = 1 := by
    rw [alphaChar_mixed_scalarProduct_muColumn_transfer_obligation _h hj]
    exact alphaChar_scalarProduct_muColumn_eq_one_of_hypothesis_10_4_data _h hj
  have halpha :=
    alphaChar_tau_formula_of_hypothesis_10_4_data _h (i := i) hj
  have horth :=
    tauOne_xi_orthogonal_muColumn_of_hypothesis_10_4_data _h hj
  have hdelta :
      (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) =
        τ (alphaChar μ ξ n δ j0 i j) + (n : ℂ) • τ₁ ξ := by
    rw [halpha]
    ext x
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [hdelta]
  rw [Section1.scalarProduct_add_left, Section1.scalarProduct_smul_left]
  rw [horth, htauPair]
  simp

public theorem theorem_10_6_base_column_from_nonbase_and_alpha_formula
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hnon : τ₁ (muColumn μ j) = (δ : ℂ) • (∑ i : I, σ (ω i j)))
    (hagree : τ (muColumn μ j - (d : ℂ) • ξ) =
      τ₁ (muColumn μ j) - (d : ℂ) • τ₁ ξ)
    (halpha : ∀ i : I,
      τ (alphaChar μ ξ n δ j0 i j) =
        (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) - (n : ℂ) • τ₁ ξ) :
    τ (muColumn μ j0 - ξ) =
      (∑ i : I, σ (ω i j0)) - τ₁ ξ := by
  classical
  rcases uniformMuData_of_hypothesis_10_4_data h with
    ⟨hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, _hdeg, _hsign, hdn⟩
  have hIcard : (Fintype.card I : ℂ) = (Nat.card W1 : ℂ) := by
    rw [← Nat.card_eq_fintype_card, hI]
  have hdnC : (d : ℂ) = (n : ℂ) * (Nat.card W1 : ℂ) + (δ : ℂ) := by
    exact_mod_cast hdn
  have hδne : (δ : ℂ) ≠ 0 := by
    rcases hδsign with rfl | rfl <;> norm_num
  have hsum_alpha :
      (∑ i : I, alphaChar μ ξ n δ j0 i j) =
        (muColumn μ j - (d : ℂ) • ξ) -
          (δ : ℂ) • (muColumn μ j0 - ξ) := by
    ext x
    simp [alphaChar, muColumn, Pi.sub_apply, Pi.smul_apply,
      Finset.sum_sub_distrib, hIcard, hdnC]
    simp_rw [← Finset.mul_sum]
    ring
  have hsum_tau :
      τ (∑ i : I, alphaChar μ ξ n δ j0 i j) =
        (δ : ℂ) • ((∑ i : I, σ (ω i j)) - (∑ i : I, σ (ω i j0))) -
          ((Fintype.card I : ℂ) * (n : ℂ)) • τ₁ ξ := by
    calc
      τ (∑ i : I, alphaChar μ ξ n δ j0 i j)
          = ∑ i : I, τ (alphaChar μ ξ n δ j0 i j) := by
            rw [map_sum]
      _ = ∑ i : I,
          ((δ : ℂ) • (σ (ω i j) - σ (ω i j0)) - (n : ℂ) • τ₁ ξ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact halpha i
      _ = (δ : ℂ) • ((∑ i : I, σ (ω i j)) - (∑ i : I, σ (ω i j0))) -
          ((Fintype.card I : ℂ) * (n : ℂ)) • τ₁ ξ := by
            ext x
            simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            rw [← Finset.mul_sum]
            rw [Finset.sum_sub_distrib]
            ring
  have hsource_tau :
      τ (∑ i : I, alphaChar μ ξ n δ j0 i j) =
        τ (muColumn μ j - (d : ℂ) • ξ) -
          (δ : ℂ) • τ (muColumn μ j0 - ξ) := by
    rw [hsum_alpha, map_sub, map_smul]
  have hdeltaY :
      (δ : ℂ) • τ (muColumn μ j0 - ξ) =
        τ (muColumn μ j - (d : ℂ) • ξ) -
          τ (∑ i : I, alphaChar μ ξ n δ j0 i j) := by
    rw [hsource_tau]
    abel
  have hdeltaY_formula :
      (δ : ℂ) • τ (muColumn μ j0 - ξ) =
        (δ : ℂ) • ((∑ i : I, σ (ω i j0)) - τ₁ ξ) := by
    rw [hdeltaY, hagree, hnon, hsum_tau]
    ext x
    simp [Pi.sub_apply, Pi.smul_apply, hIcard, hdnC, smul_eq_mul]
    ring
  ext x
  have hx := congrFun hdeltaY_formula x
  change (δ : ℂ) * (τ (muColumn μ j0 - ξ) x) =
      (δ : ℂ) * (((∑ i : I, σ (ω i j0)) - τ₁ ξ) x) at hx
  exact mul_left_cancel₀ hδne hx

public theorem theorem_10_6_base_column_formula_obligation
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
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    τ (muColumn μ j0 - ξ) =
      (∑ i : I, σ (ω i j0)) - τ₁ ξ := by
  -- PF (10.6.a), docs/PFsection10.tex lines 160-177: sum the `(10.5)`
  -- formulas and use `d = n * w1 + δ`.
  rcases exists_ne_base_column_of_hypothesis_10_4_data _h with ⟨j, hj⟩
  refine theorem_10_6_base_column_from_nonbase_and_alpha_formula _h
    (theorem_10_6_nonbase_column_formula_obligation _h j hj) ?_ ?_
  · have hagree :=
      tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_data _h hj
    rw [← hagree, map_sub, map_smul]
  · intro i
    exact alphaChar_tau_formula_of_hypothesis_10_4_data _h (i := i) hj

public theorem theorem_10_6_tildeA_lower_bound_obligation
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
    {tildeA : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_hTilde : section10TildeAData M MF tildeA)
    (_h : hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∀ g : G, g ∉ tildeA → Nat.Coprime (orderOf g) (Nat.card W1) →
      1 ≤ Complex.normSq (τ₁ ξ g) := by
  -- PF (10.6.b), docs/PFsection10.tex lines 179-191: combine Dade-map
  -- vanishing off `\widetilde A(M)` with `(3.9)` integrality/parity.
  intro g hg hcop
  have hbase := theorem_10_6_base_column_formula_obligation _h
  have hvanish :
      τ (muColumn μ j0 - ξ) g = 0 :=
    tildeAVanishing_of_hypothesis_10_4_data _h tildeA _hTilde g hg
  have hvalue :
      τ₁ ξ g = ∑ i : I, σ (ω i j0) g := by
    have hzero :
        (0 : ℂ) = (∑ i : I, σ (ω i j0) g) - τ₁ ξ g := by
      calc
        (0 : ℂ) = τ (muColumn μ j0 - ξ) g := hvanish.symm
        _ = ((∑ i : I, σ (ω i j0)) - τ₁ ξ) g := congrFun hbase g
        _ = (∑ i : I, σ (ω i j0) g) - τ₁ ξ g := by simp
    exact (sub_eq_zero.mp hzero.symm).symm
  rcases baseColumnParity_of_hypothesis_10_4_data _h g hcop with
    ⟨z, hzsum, hzodd⟩
  have hz_ne : z ≠ 0 := by
    intro hz0
    subst z
    norm_num at hzodd
  have hz_neC : (z : ℂ) ≠ 0 := by
    exact_mod_cast hz_ne
  have hτz : τ₁ ξ g = (z : ℂ) := hvalue.trans hzsum
  rw [hτz]
  exact one_le_normSq_intCast_of_ne_zero_pf105 z hz_neC

/-- Proof placeholder for `theorem_10_6_statement`. -/
public theorem theorem_10_6
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (W : Subgroup M)
    (A A0 : Set M)
    (tildeA : Set G)
    (S : Finset (Section1.ClassFunction M))
    (τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ξ : Section1.ClassFunction M)
    (i0 : I)
    (j0 : J)
    (μ : I → J → Section1.ClassFunction M)
    (δSign : J → ℤ)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d n : ℕ)
    (δ : ℤ)
    : section10TildeAData M MF tildeA →
      hypothesis_10_4_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ →
        (∀ j, j ≠ j0 →
          τ₁ (muColumn μ j) =
            (δ : ℂ) • (∑ i : I, σ (ω i j))) ∧
          τ (muColumn μ j0 - ξ) =
            (∑ i : I, σ (ω i j0)) - τ₁ ξ ∧
          ∀ g : G, g ∉ tildeA → Nat.Coprime (orderOf g) (Nat.card W1) →
            1 ≤ Complex.normSq (τ₁ ξ g) := by
  intro hTilde h104
  refine ⟨?_, ?_, ?_⟩
  · exact theorem_10_6_nonbase_column_formula_obligation h104
  · exact theorem_10_6_base_column_formula_obligation h104
  · exact theorem_10_6_tildeA_lower_bound_obligation hTilde h104


public theorem theorem_10_7_semidirectProduct_of_mf_complement
    {G : Type u}
    [Group G]
    [Finite G]
    {S SF U : Subgroup G}
    (hSF : section16MFSubgroup S SF)
    (hcomp : section12ComplementIn (ambientDerivedSubgroup S) SF U) :
    Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup S) SF U := by
  rcases hSF with ⟨⟨hSFS, hSFnorm, _hnil, _hhall⟩, _hmax⟩
  rcases hcomp with ⟨hSFD, hUD, hsup, hdisj⟩
  refine
    { left_le := hSFD
      right_le := hUD
      right_normalizes_left := ?_
      inf_eq_bot := ?_
      mul_surjective := ?_ }
  · intro k hk h hh
    let kS : S := ⟨k, section12_ambientDerivedSubgroup_le (hUD hk)⟩
    let hS : S := ⟨h, hSFS hh⟩
    have hhSub : hS ∈ SF.subgroupOf S := hh
    have hconj : kS * hS * kS⁻¹ ∈ SF.subgroupOf S :=
      hSFnorm.conj_mem hS hhSub kS
    simpa [Section2.conjBy, kS, hS, Subgroup.mem_subgroupOf] using hconj
  · exact disjoint_iff.mp hdisj
  · intro c hc
    let D : Subgroup G := ambientDerivedSubgroup S
    let cD : D := ⟨c, hc⟩
    have hDleS : D ≤ S := section12_ambientDerivedSubgroup_le
    have hDnormSF : D ≤ Subgroup.normalizer (SF : Set G) := by
      exact hDleS.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hSFS).1 hSFnorm)
    have _ : (SF.subgroupOf D).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := SF) (K := D) hSFD).2 hDnormSF
    have hsupD : SF.subgroupOf D ⊔ U.subgroupOf D = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hSFD hUD]
      exact Subgroup.subgroupOf_eq_top.mpr (le_of_eq hsup)
    have hcSup : cD ∈ SF.subgroupOf D ⊔ U.subgroupOf D := by
      rw [hsupD]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left.mp hcSup) with
      ⟨sD, hsD, uD, huD, hmul⟩
    refine ⟨(sD : G), hsD, (uD : G), huD, ?_⟩
    exact (congrArg Subtype.val hmul).symm

public theorem theorem_10_7_frobenius_bridge_of_hypothesis_9_5
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (Smax SF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u : ℕ)
    (S SH0Cprime : Finset (Section1.ClassFunction Smax)) :
    Section9.Hypothesis_9_5 Smax SF U W1 W2 H0 C Cprime T S →
      (∃ hp : Nat.Primes, hp.val = p ∧ Section9.hoReductionData Smax SF U W2 H0 hp) →
        q = Nat.card W1 →
          Section9.quotientBarUCardinality U C u →
            Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF
                (H0 ⊔ Cprime) SH0Cprime →
              (¬ ∃ χ : Section1.ClassFunction Smax,
                χ ∈ SH0Cprime ∧ Section9.degreeQuIrreducibleFromLinearHC Smax SF C q u χ) →
                  section16TypeII Smax SF → section12FrobeniusJoinWithKernel SF U := by
  intro h95 hp hq hBarU hSH0Cprime hno hTypeII
  have h910 :=
    Section9.theorem_9_10 Smax SF U W1 W2 H0 C Cprime T p q u S SH0Cprime
      h95 hp hq hBarU hSH0Cprime hno
  exact h910.2.2.2.2 hTypeII

public theorem theorem_10_7_frobenius_bridge_of_hypothesis_9_5_canonical
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (Smax SF U W1 W2 H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction Smax)) :
    Section9.Hypothesis_9_5 Smax SF U W1 W2 H0 C Cprime T S →
      (∀ u : ℕ, Section9.quotientBarUCardinality U C u →
        ¬ ∃ χ : Section1.ClassFunction Smax,
          χ ∈
              Section9.kernelInducedSubfamily_sec9 Smax
                (ambientDerivedSubgroup Smax) SF (H0 ⊔ Cprime) S ∧
            Section9.degreeQuIrreducibleFromLinearHC
              Smax SF C (Nat.card W1) u χ) →
        section16TypeII Smax SF → section12FrobeniusJoinWithKernel SF U := by
  intro h95 hno hTypeII
  have h95full := h95
  rcases h95 with
    ⟨h92, hp95, hCU, hBarU95, hCprimeC, _hCprimeEq, _hDade, hS, _h52b⟩
  rcases hp95 with ⟨p, hpData⟩
  rcases hBarU95 with ⟨u, hBarU⟩
  let N : Subgroup G := ambientDerivedSubgroup Smax
  have hUN : U ≤ N := by
    rcases h92 with ⟨_hMmax, _hMF, htypeP, _hsource, _htypes, _hq⟩
    rcases htypeP with ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hhall, _hMFder, hcomp, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer⟩
    simpa [N] using Section9.complement_le_right_sec9 hcomp
  have hCN : C ≤ N := hCU.1.trans hUN
  have hCprimeN : Cprime ≤ N := hCprimeC.trans hCN
  have hH0N : H0 ≤ N := by
    simpa [N] using hS.1
  have hH0CprimeN : H0 ⊔ Cprime ≤ N := sup_le hH0N hCprimeN
  let SH0Cprime : Finset (Section1.ClassFunction Smax) :=
    Section9.kernelInducedSubfamily_sec9 Smax N SF (H0 ⊔ Cprime) S
  have hSH0CprimeN :
      Section9.kernelInducedFamily Smax N SF (H0 ⊔ Cprime) SH0Cprime :=
    Section9.kernelInducedFamily_subfamily_of_le_sec9
      Smax N SF H0 (H0 ⊔ Cprime) S hH0CprimeN le_sup_left hS
  have hSH0Cprime :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF
        (H0 ⊔ Cprime) SH0Cprime := by
    simpa [N, SH0Cprime] using hSH0CprimeN
  exact theorem_10_7_frobenius_bridge_of_hypothesis_9_5
    Smax SF U W1 W2 H0 C Cprime T p.val (Nat.card W1) u S SH0Cprime
    h95full ⟨p, rfl, hpData⟩ rfl hBarU hSH0Cprime (hno u hBarU) hTypeII

public theorem theorem_10_7_hypothesis_9_2_pair_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S U1 U0 : Subgroup G}
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (_hPData : Section8.typePData Smax SF U W1S W2S)
    (_hTypeP : Section8.typePDefinitionData Smax SF U W1S W2S)
    (_hTypeIIToIV : Section8.typeIIToIVSourceCondition Smax U W1S)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ Smax)
    (_hF : Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0) :
    Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S) := by
  have hnotIIIIV : ¬ (section16TypeIII Smax SF ∨ section16TypeIV Smax SF) :=
    Section8.section16_not_typeIII_or_typeIV_of_typeII _hSmax _hSF _hTypeII
  exact
    { maximal := _hSmax
      mf := _hSF
      typeP := _hPData
      typePDefinitionData := _hTypeP
      typeIIToIVSourceCondition := _hTypeIIToIV
      typeIISource := by
        intro _hII
        exact ⟨_hUcomm, _hUnorm, U1, U0, _hF⟩
      typeIIISource := by
        intro hIII
        exact False.elim (hnotIIIIV (Or.inl hIII))
      typeIVSource := by
        intro hIV
        exact False.elim (hnotIIIIV (Or.inr hIV))
      typeCases := Or.inl _hTypeII
      q_eq := rfl }

public theorem theorem_10_7_hypothesis_9_5_of_tail_fields
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax SF U W1S W2S H0 C Cprime : Subgroup G}
    {T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {S9 : Finset (Section1.ClassFunction Smax)}
    (h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (hHo : ∃ p : Nat.Primes, Section9.hoReductionData Smax SF U W2S H0 p)
    (hC : Section9.quotientCentralizerIn SF H0 U C)
    (hBarU : ∃ u : ℕ, Section9.quotientBarUCardinality U C u)
    (hCprime_le : Cprime ≤ C)
    (hCprime_eq : Cprime = (_root_.commutator C).map C.subtype)
    (hDade : Section9.dadeIsometryRelativeToASet Smax U T)
    (hKernel :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF H0 S9)
    (h52b : Section5.hypothesis_5_2_b_statement S9 T) :
    Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9 where
  hypothesis92 := h92
  hoReduction := hHo
  quotientCentralizer := hC
  quotientBarU := hBarU
  Cprime_le_C := hCprime_le
  Cprime_eq_commutator := hCprime_eq
  dade := hDade
  kernelInduced := hKernel
  hypothesis52b := h52b

public theorem theorem_10_7_commutator_map_subtype_le_self
    {G : Type u}
    [Group G]
    (C : Subgroup G) :
    (_root_.commutator C).map C.subtype ≤ C := by
  intro x hx
  rcases hx with ⟨y, _hy, rfl⟩
  exact y.property

public theorem theorem_10_7_exists_kernelInducedFamily
    {G : Type u}
    [Group G]
    [Finite G]
    (M N H Y : Subgroup G)
    (hYN : Y ≤ N)
    (hHN : H ≤ N) :
    ∃ S : Finset (Section1.ClassFunction M),
      Section9.kernelInducedFamily M N H Y S := by
  classical
  rcases exists_completeIrreducibleCharacterFamily_sum_degree_normSq
      (G := N.subgroupOf M) with
    ⟨ι, hι, χrep, hχrep, _hsum⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let θ : ι → Section1.ClassFunction (N.subgroupOf M) :=
    fun i => Section1.ofConjClassFunction (χrep i)
  let S : Finset (Section1.ClassFunction M) :=
    (Finset.univ.filter fun i =>
      ¬ Section1.subgroupInKernel' (θ i)
          ((H.subgroupOf M).subgroupOf (N.subgroupOf M)) ∧
        Section1.subgroupInKernel' (θ i)
          ((Y.subgroupOf M).subgroupOf (N.subgroupOf M))).image
      (fun i => Section1.inducedCF (N.subgroupOf M) (θ i))
  have hθirr :
      ∀ i, Section1.IsIrreducibleCharacterOnGroup (θ i) := by
    intro i
    exact ofConjClassFunction_isIrreducibleCharacterOnGroup_sec10 (hχrep.1 i)
  have hθcomplete :
      ∀ ψ : Section1.ClassFunction (N.subgroupOf M),
        Section1.IsIrreducibleCharacterOnGroup ψ → ∃ i, θ i = ψ := by
    intro ψ hψirr
    let ψrep : ConjClassFunction (N.subgroupOf M) :=
      Section1.toConjClassFunction ψ
        (isClassFunction_of_irreducibleCharacterOnGroup_sec10 hψirr)
    have hψrepirr : IsIrreducibleConjCharacter ψrep :=
      toConjClassFunction_isIrreducibleCharacter_of_onGroup_sec10 hψirr
    rcases hχrep.2.1 ψrep hψrepirr with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext g
    change χrep i (ConjClasses.mk g) = ψ g
    rw [hi]
    rfl
  refine ⟨S, hYN, hHN, ?_⟩
  intro χ
  constructor
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨i, hi, rfl⟩
    have hi' :
        ¬ Section1.subgroupInKernel' (θ i)
            ((H.subgroupOf M).subgroupOf (N.subgroupOf M)) ∧
          Section1.subgroupInKernel' (θ i)
            ((Y.subgroupOf M).subgroupOf (N.subgroupOf M)) := by
      simpa [S] using hi
    exact ⟨θ i, hθirr i, hi'.1, hi'.2, rfl⟩
  · rintro ⟨ψ, hψirr, hψnonkernel, hψkernel, rfl⟩
    rcases hθcomplete ψ hψirr with ⟨i, hi⟩
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · simpa [S, hi] using And.intro hψnonkernel hψkernel
    · simp [hi]

public theorem theorem_10_7_kernelInducedFamily_tail_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax SF U W1S W2S H0 : Subgroup G}
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (p : Nat.Primes)
    (_hpData : Section9.hoReductionData Smax SF U W2S H0 p) :
    ∃ S9 : Finset (Section1.ClassFunction Smax),
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF H0 S9 := by
  have hSF_le_D :
      SF ≤ ambientDerivedSubgroup Smax :=
    Section9.MF_le_ambientDerived_of_hypothesis_9_2_sec9
      Smax SF U W1S W2S (Nat.card W1S) _h92
  have hH0_le_D : H0 ≤ ambientDerivedSubgroup Smax := by
    rcases _hpData with ⟨hH0_le_SF, _hrest⟩
    exact hH0_le_SF.trans hSF_le_D
  exact theorem_10_7_exists_kernelInducedFamily
    Smax (ambientDerivedSubgroup Smax) SF H0 hH0_le_D hSF_le_D

public theorem theorem_10_7_exists_quotientBarUCardinality_of_quotientCentralizerIn
    {G : Type u}
    [Group G]
    [Finite G]
    {MF H0 U C : Subgroup G}
    (hUcomm : IsMulCommutative U)
    (hC : Section9.quotientCentralizerIn MF H0 U C) :
    ∃ u : ℕ, Section9.quotientBarUCardinality U C u := by
  classical
  let _ : IsMulCommutative U := hUcomm
  let _ : (C.subgroupOf U).Normal :=
    Subgroup.normal_of_isMulCommutative (C.subgroupOf U)
  exact ⟨Nat.card (U ⧸ C.subgroupOf U), hC.1, inferInstance, rfl⟩


public theorem theorem_10_7_quotientCentralizerIn_tail_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 : Subgroup G}
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (_hTypeP : Section8.typePDefinitionData Smax SF U W1S W2S)
    (_hTypeIIToIV : Section8.typeIIToIVSourceCondition Smax U W1S)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ Smax)
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (p : Nat.Primes)
    (_hpData : Section9.hoReductionData Smax SF U W2S H0 p) :
    ∃ C : Subgroup G, Section9.quotientCentralizerIn SF H0 U C := by
  rcases Section9.theorem_9_3_action_normalizes_and_solvable_sec9
      Smax SF U W1S W2S (Nat.card W1S) _h92 with
    ⟨hUW1_norm_SF, _hsolvSF⟩
  have hU_norm_SF : U ≤ Subgroup.normalizer (SF : Set G) :=
    le_sup_left.trans hUW1_norm_SF
  let _ : Subgroup.Normalizes U SF := ⟨hU_norm_SF⟩
  rcases _hpData with
    ⟨_hH0_le_SF, hSF_le_Smax, hH0_normal_Smax, hH0_normal_SF,
      _hH0_lt_SF, _hElementary, _hBranch⟩
  rcases _hTypeP with
    ⟨_hSFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompSmaxW1, hU_le_D,
      _hUnil, _hW1normU, _hcompDU, _hSFnotcyc, _hSmax2le, _hFitEq,
      _hFitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hU_le_Smax : U ≤ Smax :=
    hU_le_D.trans (section12_ambientDerivedSubgroup_le (G := G) (E := Smax))
  have hH0_inv_U : IsInvariant U SF (H0.subgroupOf SF) :=
    Section9.subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9
      Smax SF U H0 hSF_le_Smax hU_le_Smax hH0_normal_Smax hU_norm_SF
  exact
    Section9.exists_quotientCentralizerIn_of_invariant_sec9
      (MF := SF) (H0 := H0) (U := U) hH0_normal_SF hH0_inv_U

public theorem theorem_10_7_msChoice_eq_mf_of_typeII
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF Ms : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (hMs : Section8.msChoice Smax SF Ms) :
    Ms = SF := by
  rcases hMs with hEarly | hLate
  · exact hEarly.2
  · exfalso
    exact Section8.section16_not_typeIII_or_typeIV_of_typeII hSmax hSF hTypeII hLate.1

public theorem theorem_10_7_section8_fullData_dade_typeII_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S : Subgroup G}
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S)) :
    ∃ d52 : Section8.section8Hypothesis52FullData Smax SF W1S W2S
        (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) SF),
      Section9.dadeIsometryRelativeToASet Smax U d52.tau := by
  rcases _h92.typeIISource _hTypeII with ⟨hUcomm, hUnorm, hF⟩
  rcases Section8.section8Hypothesis52FullData_dadeRelative_of_typeII_source_data
      _hSmax _hSF _hTypeII _h92.typePDefinitionData
      _h92.typeIIToIVSourceCondition hUcomm hUnorm hF with
    ⟨d52, hDade⟩
  refine ⟨d52, ?_⟩
  simpa [Section9.dadeIsometryRelativeToASet] using hDade


public theorem theorem_10_7_section8_fullData_dade_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S Ms : Subgroup G}
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (_hMs : Section8.msChoice Smax SF Ms) :
    ∃ d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
        (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms),
      Section9.dadeIsometryRelativeToASet Smax U d52.tau := by
  have hMs_eq : Ms = SF :=
    theorem_10_7_msChoice_eq_mf_of_typeII _hSmax _hSF _hTypeII _hMs
  subst Ms
  exact
    theorem_10_7_section8_fullData_dade_typeII_source_data
      _hSmax _hSF _hTypeII _h92


public theorem theorem_10_7_section8_fullData_dade_tail_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S Ms : Subgroup G}
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (_hMs : Section8.msChoice Smax SF Ms) :
    ∃ d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
        (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms),
      Section9.dadeIsometryRelativeToASet Smax U d52.tau := by
  rcases theorem_10_7_section8_fullData_dade_source_data
      _hSmax _hSF _hTypeII _h92 _hMs with
    ⟨d52, hDade⟩
  exact ⟨d52, hDade⟩

public theorem theorem_10_7_kernelInducedFamily_nonempty_of_witness
    {G : Type u}
    [Group G]
    [Finite G]
    {M N H Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hKernel : Section9.kernelInducedFamily M N H Y S)
    (θ : Section1.ClassFunction (N.subgroupOf M))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnonkernel :
      ¬ Section1.subgroupInKernel' θ
          ((H.subgroupOf M).subgroupOf (N.subgroupOf M)))
    (hθkernel :
      Section1.subgroupInKernel' θ
        ((Y.subgroupOf M).subgroupOf (N.subgroupOf M))) :
    S.Nonempty := by
  classical
  refine ⟨Section1.inducedCF (N.subgroupOf M) θ, ?_⟩
  exact (hKernel.2.2 (Section1.inducedCF (N.subgroupOf M) θ)).mpr
    ⟨θ, hθirr, hθnonkernel, hθkernel, rfl⟩

public theorem theorem_10_7_kernelInducedFamily_witness_tail_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 : Subgroup G}
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (p : Nat.Primes)
    (_hpData : Section9.hoReductionData Smax SF U W2S H0 p) :
    ∃ θ : Section1.ClassFunction ((ambientDerivedSubgroup Smax).subgroupOf Smax),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        ¬ Section1.subgroupInKernel' θ
            ((SF.subgroupOf Smax).subgroupOf
              ((ambientDerivedSubgroup Smax).subgroupOf Smax)) ∧
          Section1.subgroupInKernel' θ
            ((H0.subgroupOf Smax).subgroupOf
              ((ambientDerivedSubgroup Smax).subgroupOf Smax)) := by
  classical
  have hSF_le_D :
      SF ≤ ambientDerivedSubgroup Smax :=
    Section9.MF_le_ambientDerived_of_hypothesis_9_2_sec9
      Smax SF U W1S W2S (Nat.card W1S) _h92
  rcases _hpData with
    ⟨hH0_le_SF, hSF_le_Smax, hH0_normal_Smax, _hH0_normal_SF,
      hH0_lt_SF, _hElementary, _hBranch⟩
  let H : Subgroup Smax := (ambientDerivedSubgroup Smax).subgroupOf Smax
  let Z : Subgroup Smax := H0.subgroupOf Smax
  let A : Subgroup Smax := SF.subgroupOf Smax
  have _ : Z.Normal := by
    simpa [Z] using hH0_normal_Smax
  have hA_le_H : A ≤ H := by
    intro x hx
    change (x : G) ∈ ambientDerivedSubgroup Smax
    exact hSF_le_D (by simpa [A, Subgroup.mem_subgroupOf] using hx)
  have hZ_lt_A : Z < A := by
    constructor
    · intro x hx
      change (x : G) ∈ SF
      exact hH0_le_SF (by simpa [Z, Subgroup.mem_subgroupOf] using hx)
    · intro hA_le_Z
      have hSF_le_H0 : SF ≤ H0 := by
        intro x hxSF
        have hxA : (⟨x, hSF_le_Smax hxSF⟩ : Smax) ∈ A := by
          simpa [A, Subgroup.mem_subgroupOf] using hxSF
        have hxZ : (⟨x, hSF_le_Smax hxSF⟩ : Smax) ∈ Z :=
          hA_le_Z hxA
        simpa [Z, Subgroup.mem_subgroupOf] using hxZ
      exact hH0_lt_SF.not_ge hSF_le_H0
  rcases
      exists_irreducibleCharacterOnGroup_kernel_not_subgroup_kernel_of_lt_sec10
        (H := H) (Z := Z) (A := A) hA_le_H hZ_lt_A with
    ⟨θ, hθirr, hθnonkernel, hθkernel⟩
  exact ⟨θ, hθirr, hθnonkernel, hθkernel⟩

public theorem theorem_10_7_kernelInducedFamily_nonempty_tail_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 : Subgroup G}
    (_h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (p : Nat.Primes)
    (_hpData : Section9.hoReductionData Smax SF U W2S H0 p)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_hKernel :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF H0 S9) :
    S9.Nonempty := by
  rcases theorem_10_7_kernelInducedFamily_witness_tail_source_data
      _h92 p _hpData with
    ⟨θ, hθirr, hθnonkernel, hθkernel⟩
  exact theorem_10_7_kernelInducedFamily_nonempty_of_witness
    (M := Smax) (N := ambientDerivedSubgroup Smax) (H := SF) (Y := H0)
    (S := S9) _hKernel θ hθirr hθnonkernel hθkernel


@[expose] public def theorem_10_7_selectedSection8FullDataForT
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax SF W1S W2S : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ Ms : Subgroup G,
    Section8.msChoice Smax SF Ms ∧
      ∃ d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
          (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms),
        T = d52.tau


public theorem theorem_10_7_scalarProduct_eq_zero_of_disjoint_supports
    {G : Type u}
    [Finite G]
    {A B : Set G}
    {φ ψ : Section1.ClassFunction G}
    (hφ : Section1.supportedOn φ A)
    (hψ : Section1.supportedOn ψ B)
    (hdisj : Disjoint A B) :
    Section1.scalarProduct G φ ψ = 0 := by
  classical
  have hsum : ∑ g : G, φ g * star (ψ g) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro g _hg
    by_cases hgA : g ∈ A
    · have hgB : g ∉ B :=
        (Set.disjoint_left.mp hdisj) hgA
      have hzero : ψ g = 0 := (Section1.supportedOn_iff.mp hψ) g hgB
      simp [hzero]
    · have hzero : φ g = 0 := (Section1.supportedOn_iff.mp hφ) g hgA
      simp [hzero]
  rw [Section1.scalarProduct, hsum]
  simp

public theorem theorem_10_7_late_source_type_of_typeIIIIVVData
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    (hType : typeIIIIVVData M MF W1 W2 V) :
    Section8.typeIIIDefinitionData M MF ∨
      Section8.typeIVDefinitionData M MF ∨
        Section8.typeVDefinitionData M MF := by
  rcases hType with ⟨_hVeq, U, hP, hCases⟩
  rcases hCases with hIII | hIV | hV
  · exact Or.inl
      ⟨U, W1, W2, hP, hIII.1, hIII.2.1, hIII.2.2⟩
  · exact Or.inr (Or.inl
      ⟨U, W1, W2, hP, hIV.1, hIV.2.1, hIV.2.2⟩)
  · exact Or.inr (Or.inr
      ⟨U, W1, W2, hP, hV.1, hV.2⟩)


public theorem derivedSupportedFourSixData_of_hypothesis_10_1_supported_data
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
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {mu : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℤ}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S tau)
    (hNotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        mu deltaSign omega sigma tau) :
    ∃ sigmaM : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction M,
      ∃ xChar : J → Section1.ClassFunction (derivedSubgroup M),
        ∃ H_A _H_A0 : G → Subgroup G,
          Section4Scratch.hypothesis_4_6_supported_statement M
            (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
            (derivedSubgroup M) A i0 j0 omega sigmaM sigma mu xChar
            (fun j => (deltaSign j : ℂ)) tau H_A := by
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  have hLate := theorem_10_7_late_source_type_of_typeIIIIVVData hType
  rcases hType with ⟨_hV, U, hP, _hCases⟩
  exact
    derivedSupportedFourSixData_of_section10FourSixNotationSupportedData_of_late
      hP.1 hLate hNotation

public theorem hypothesis_4_6_derived_of_hypothesis_10_1_supported_data
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
    {tau : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I}
    {j0 : J}
    {mu : I → J → Section1.ClassFunction M}
    {deltaSign : J → ℤ}
    {omega : I → J → Section1.ClassFunction W}
    {sigma : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S tau)
    (hNotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        mu deltaSign omega sigma tau) :
    Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
      (derivedSubgroup M) A := by
  rcases derivedSupportedFourSixData_of_hypothesis_10_1_supported_data
      h10 hNotation with
    ⟨_sigmaM, _xChar, _H_A, _H_A0, hSupported⟩
  exact hSupported.1

public theorem theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    A1 = section16NonidentityElements (ambientDerivedSubgroup M : Set G) := by
  have hNot :=
    section10_source_not_typeI_typeII_of_msChoice_tail hNotation.2.2.1 hTail
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hBranch⟩
  rcases hBranch with hI | hP
  · exact False.elim (hNot.1 hI.1)
  · rcases hP with ⟨_U, _W1, _W2, _hP, _hType, _hA, _hA0, hLate⟩
    exact (hLate hTail).1

public theorem theorem_10_7_supportedOn_of_integerSpan_generators
    {L : Type u}
    [Group L]
    {S : Finset (Section1.ClassFunction L)}
    {A : Set L}
    {φ : Section1.ClassFunction L}
    (hgen : ∀ χ : Section1.ClassFunction L, χ ∈ S → Section1.supportedOn χ A)
    (hspan : Section5.integerSpan S φ) :
    Section1.supportedOn φ A := by
  classical
  rcases hspan with ⟨v, rfl⟩
  rw [Section1.supportedOn_iff]
  intro g hgA
  change (∑ χ : S, (v χ : ℂ) • (χ : Section1.ClassFunction L)) g = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero ?_
  intro χ _hχ
  have hzero : (χ : Section1.ClassFunction L) g = 0 :=
    (Section1.supportedOn_iff.mp (hgen χ χ.property)) g hgA
  simp [hzero]


public theorem theorem_10_7_A_subset_A0_of_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1) :
    A ⊆ A0 := by
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hBranch⟩
  rcases hBranch with hI | hP
  · rcases hI with ⟨_hTypeI, _hA, hA0⟩
    intro x hx
    simpa [hA0] using hx
  · rcases hP with ⟨_U, _W1, _W2, _hP, _hType, _hA, hA0, _hLateImp⟩
    intro x hx
    rw [hA0]
    exact Or.inl hx


public theorem theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    A = A1 := by
  have hNot :=
    section10_source_not_typeI_typeII_of_msChoice_tail hNotation.2.2.1 hTail
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hBranch⟩
  rcases hBranch with hI | hP
  · exact False.elim (hNot.1 hI.1)
  · rcases hP with ⟨_U, _W1, _W2, _hP, _hType, _hA, _hA0, hLate⟩
    exact (hLate hTail).2


public theorem theorem_10_7_A1_subset_A_of_late_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    A1 ⊆ A := by
  have hA :
      A = A1 :=
    theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data hNotation hTail
  intro x hx
  simpa [hA] using hx


public theorem theorem_10_7_hypothesis2_complement_le_bot_of_centralizer_le
    {G : Type u}
    [Group G]
    [Finite G]
    {A : Set G}
    {M : Subgroup G}
    {H : G → Subgroup G}
    (hA0M : Section2.Hypothesis2 A M H)
    {a : G}
    (ha : a ∈ A)
    (hCentM : Subgroup.centralizer ({a} : Set G) ≤ M) :
    H a ≤ ⊥ := by
  intro h hh
  have hprod := hA0M.centralizer_eq_product ha
  have hhCent : h ∈ Section2.elementCentralizer a := hprod.left_le hh
  have hhM : h ∈ M := hCentM (by
    simpa [Section2.elementCentralizer] using hhCent)
  have hhCentIn : h ∈ Section2.centralizerIn M a := by
    exact ⟨hhM, hhCent⟩
  have hInf : h ∈ H a ⊓ Section2.centralizerIn M a := ⟨hh, hhCentIn⟩
  simpa [hprod.inf_eq_bot] using hInf


public theorem theorem_10_7_section12ComplementIn_isComplement'_subgroupOf_right
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    (L.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hKM, hLM, hsup, hdisj⟩
  have hsup_local : L.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    calc
      L.subgroupOf M ⊔ K.subgroupOf M = (L ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := M) hLM hKM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf M) (K.subgroupOf M)).symm

public theorem theorem_10_7_section12ComplementIn_left_relIndex_eq_card_right
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    K.relIndex M = Nat.card L := by
  have hcompLocal : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    theorem_10_7_section12ComplementIn_isComplement'_subgroupOf_right hcomp
  calc
    K.relIndex M = (K.subgroupOf M).index := rfl
    _ = Nat.card (L.subgroupOf M) := hcompLocal.index_eq_card
    _ = Nat.card L :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := L) (K := M) hcomp.2.1).toEquiv

public theorem theorem_10_7_section12ComplementIn_left_isHall_of_coprime
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card L)) :
    IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf M) := by
  classical
  have hcompLocal : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    theorem_10_7_section12ComplementIn_isComplement'_subgroupOf_right hcomp
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet K)
    (H := K.subgroupOf M) ?_ ?_
  · intro p hpK
    have hcardK : Nat.card (K.subgroupOf M) = Nat.card K :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hcomp.1).toEquiv
    rw [hcardK] at hpK
    exact hpK
  · intro p hpK hpidxK
    have hpLcardSub : p.val ∣ Nat.card (L.subgroupOf M) := by
      simpa [hcompLocal.index_eq_card] using hpidxK
    have hpLcard : p.val ∣ Nat.card L := by
      have hcardL : Fintype.card (L.subgroupOf M) = Fintype.card L := by
        simpa [Nat.card_eq_fintype_card] using
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := L) (K := M) hcomp.2.1).toEquiv
      simpa [Nat.card_eq_fintype_card, hcardL] using hpLcardSub
    exact (p.property.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hpK) hpLcard

public theorem theorem_10_7_internalSemidirectProduct_left_isHall_of_coprime
    {G : Type u}
    [Group G]
    [Finite G]
    {C H K : Subgroup G}
    (hprod : Section2.IsInternalSemidirectProduct C H K)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf C) := by
  classical
  refine isHallSubgroup_of (G := C) (π := subgroupPrimeSet H)
    (H := H.subgroupOf C) ?_ ?_
  · intro p hpH
    have hcardH : Nat.card (H.subgroupOf C) = Nat.card H :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := C) hprod.left_le).toEquiv
    rw [hcardH] at hpH
    exact hpH
  · intro p hpH hpidxH
    have hidx : (H.subgroupOf C).index = Nat.card K := by
      simpa [Subgroup.relIndex] using
        Section2.internalSemidirectProduct_left_relIndex_eq_card_right hprod
    have hpK : p.val ∣ Nat.card K := by
      simpa [hidx] using hpidxH
    exact (p.property.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hpH) hpK

public theorem theorem_10_7_left_le_left_of_common_coprime_complement
    {G : Type u}
    [Group G]
    [Finite G]
    {C H F K : Subgroup G}
    (hHprod : Section2.IsInternalSemidirectProduct C H K)
    (hFsemi : Section8.section8SemidirectProductIn C F K)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    H ≤ F := by
  classical
  rcases hFsemi with ⟨hFcomp, _hFleC, hFnormal⟩
  have hHrel : H.relIndex C = Nat.card K :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hHprod
  let _ : (F.subgroupOf C).Normal := hFnormal
  have hFrel : F.relIndex C = Nat.card K :=
    theorem_10_7_section12ComplementIn_left_relIndex_eq_card_right hFcomp
  have hHmul :
      Nat.card K * Nat.card H = Nat.card C := by
    have hlag :=
      relIndex_mul_card_eq_card_of_le (H := C) (H' := H) hHprod.left_le
    simpa [hHrel] using hlag
  have hFmul :
      Nat.card K * Nat.card F = Nat.card C := by
    have hlag :=
      relIndex_mul_card_eq_card_of_le (H := C) (H' := F) hFcomp.1
    simpa [hFrel] using hlag
  have hcardHF : Nat.card H = Nat.card F :=
    Nat.mul_left_cancel (Nat.card_pos (α := K)) (hHmul.trans hFmul.symm)
  have hcardHFF : Fintype.card H = Fintype.card F := by
    simpa [Nat.card_eq_fintype_card] using hcardHF
  have hcopF : Nat.Coprime (Nat.card F) (Nat.card K) := by
    simpa [Nat.card_eq_fintype_card, ← hcardHFF] using hcop
  have hHallH :
      IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf C) :=
    theorem_10_7_internalSemidirectProduct_left_isHall_of_coprime hHprod hcop
  have hPrimeSet : subgroupPrimeSet H = subgroupPrimeSet F := by
    ext p
    simp [subgroupPrimeSet, hcardHFF]
  have hHallH' :
      IsHallSubgroup (subgroupPrimeSet F) (H.subgroupOf C) := by
    simpa [hPrimeSet] using hHallH
  have hHallF :
      IsHallSubgroup (subgroupPrimeSet F) (F.subgroupOf C) :=
    theorem_10_7_section12ComplementIn_left_isHall_of_coprime hFcomp hcopF
  have hHleFSub : H.subgroupOf C ≤ F.subgroupOf C :=
    IsHallSubgroup.le_of_normal hHallF hHallH'
  intro x hx
  have hxSub : (⟨x, hHprod.left_le hx⟩ : C) ∈ H.subgroupOf C := hx
  exact hHleFSub hxSub


public theorem theorem_10_7_dadeTransform_supportedOn_of_dadeSupport_subset
    {G : Type u}
    [Group G]
    {A tildeA : Set G}
    {L : Subgroup G}
    {H : G → Subgroup G}
    (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L)
    (hSupport : Section2.dadeSupport A H ⊆ tildeA) :
    Section1.supportedOn (Section2.dadeTransform H hAL α) tildeA := by
  rw [Section1.supportedOn_iff]
  intro g hg
  exact Section2.dadeTransform_eq_zero_of_not_mem_support H hAL α
    (fun hgSupport => hg (hSupport hgSupport))

public theorem theorem_10_7_dadeSupport_subset_tildeA_of_notation_8_14_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R) :
    Section2.dadeSupport A R ⊆ tildeA := by
  intro g hg
  rcases h14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hUnique, _hReq, htildeA, _htildeA0,
      _htildeA1⟩
  rcases hg with ⟨a, ha, r, hr, hconj⟩
  rcases hconj with ⟨y, hy⟩
  rw [htildeA]
  refine ⟨a, ha, ?_⟩
  refine ⟨a * r, ?_, y⁻¹, by simp, ?_⟩
  · exact ⟨r, hr, rfl⟩
  · calc
      g = y⁻¹ * (y * g * y⁻¹) * y := by group
      _ = y⁻¹ * (a * r) * y := by
        rw [show y * g * y⁻¹ = a * r by simpa [Section2.conjBy] using hy]
      _ = y⁻¹ * (a * r) * (y⁻¹)⁻¹ := by simp

public theorem theorem_10_7_dadeSupport_subset_tildeA_of_notation_8_14_and_H_le
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {Abook A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {H R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hAbookA : Abook ⊆ A)
    (hHle : ∀ a : G, a ∈ Abook → H a ≤ R a) :
    Section2.dadeSupport Abook H ⊆ tildeA := by
  intro g hg
  rcases hg with ⟨a, ha, h, hh, hconj⟩
  exact theorem_10_7_dadeSupport_subset_tildeA_of_notation_8_14_source_data h14
    ⟨a, hAbookA ha, h, hHle a ha hh, hconj⟩

public theorem theorem_10_7_dadeSupport_subset_tildeA1_of_notation_8_14_and_H_le
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {H R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hHle : ∀ a : G, a ∈ A1 → H a ≤ R a) :
    Section2.dadeSupport A1 H ⊆ tildeA1 := by
  intro g hg
  rcases h14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hUnique, _hReq, _htildeA, _htildeA0,
      htildeA1⟩
  rcases hg with ⟨a, ha, h, hh, hconj⟩
  rcases hconj with ⟨y, hy⟩
  rw [htildeA1]
  refine ⟨a, ha, ?_⟩
  refine ⟨a * h, ?_, y⁻¹, by simp, ?_⟩
  · exact ⟨h, hHle a ha hh, rfl⟩
  · calc
      g = y⁻¹ * (y * g * y⁻¹) * y := by group
      _ = y⁻¹ * (a * h) * y := by
        rw [show y * g * y⁻¹ = a * h by simpa [Section2.conjBy] using hy]
      _ = y⁻¹ * (a * h) * (y⁻¹)⁻¹ := by simp

public theorem theorem_10_7_dadeTransform_eq_zero_of_supportedOn_of_not_mem_dadeSupport
    {G : Type u}
    [Group G]
    {L : Subgroup G}
    {A A0 : Set G}
    {H : G → Subgroup G}
    (hA0L : ∀ a ∈ A0, a ∈ L)
    {α : Section1.ClassFunction L}
    (hα : Section1.supportedOn α (Section8.section8SubgroupSetPreimage L A))
    {g : G}
    (hg : g ∉ Section2.dadeSupport A H) :
    Section2.dadeTransform H hA0L α g = 0 := by
  classical
  by_cases hmem : ∃ a ∈ A0, ∃ h ∈ H a, Section2.conjugateIn g (a * h)
  · let a : G := Classical.choose hmem
    have ha0 : a ∈ A0 := (Classical.choose_spec hmem).1
    let h : G := Classical.choose (Classical.choose_spec hmem).2
    have hh : h ∈ H a := (Classical.choose_spec (Classical.choose_spec hmem).2).1
    have hconj : Section2.conjugateIn g (a * h) :=
      (Classical.choose_spec (Classical.choose_spec hmem).2).2
    have ha_not : a ∉ A := by
      intro ha
      exact hg ⟨a, ha, h, hh, hconj⟩
    have hαzero : α ⟨a, hA0L a ha0⟩ = 0 := by
      rw [Section1.supportedOn_iff] at hα
      exact hα ⟨a, hA0L a ha0⟩ (by
        simpa [Section8.section8SubgroupSetPreimage] using ha_not)
    simpa [Section2.dadeTransform, hmem, a] using hαzero
  · simp [Section2.dadeTransform, hmem]

private theorem
    theorem_10_7_dadeTransform_supportedOn_of_supportedOn_subgroup_preimage_of_dadeSupport_subset
    {G : Type u}
    [Group G]
    {L : Subgroup G}
    {A A0 tildeA : Set G}
    {H : G → Subgroup G}
    (hA0L : ∀ a ∈ A0, a ∈ L)
    (α : Section1.ClassFunction L)
    (hα : Section1.supportedOn α (Section8.section8SubgroupSetPreimage L A))
    (hSupport : Section2.dadeSupport A H ⊆ tildeA) :
    Section1.supportedOn (Section2.dadeTransform H hA0L α) tildeA := by
  rw [Section1.supportedOn_iff]
  intro g hg
  exact theorem_10_7_dadeTransform_eq_zero_of_supportedOn_of_not_mem_dadeSupport
    hA0L hα (fun hgSupport => hg (hSupport hgSupport))

public theorem theorem_10_7_isClassFunction_evalCoeff
    {L : Type u}
    [Group L]
    {ι : Type*}
    [Fintype ι]
    (μ : ι → Section1.ClassFunction L)
    (hμ : ∀ i, Section1.IsClassFunction (μ i))
    (v : Section1.CoeffVector ι) :
    Section1.IsClassFunction (Section1.evalCoeff μ v) := by
  classical
  unfold Section1.evalCoeff
  intro x g
  have hterm :
      ∀ i, (v i : ℂ) * μ i (x * g * x⁻¹) = (v i : ℂ) * μ i g := by
    intro i
    rw [hμ i x g]
  simpa using Finset.sum_congr rfl (fun i _ => hterm i)

public theorem theorem_10_7_support_on_A_of_punctured_and_withOne
    {G : Type u}
    [Group G]
    (M : Subgroup G)
    {A : Set G}
    {χ : Section1.ClassFunction M}
    (hpunct : Section1.supportedOn χ Section5.puncturedSet)
    (hwithOne :
      ∀ l : M, (l : G) ∉ Section4Scratch.withOne A → χ l = 0) :
    ∀ l : M, (l : G) ∉ A → χ l = 0 := by
  intro l hlA
  by_cases hl1 : l = 1
  · exact (Section1.supportedOn_iff.mp hpunct) l
      (by simp [Section5.puncturedSet, hl1])
  · have hl1G : (l : G) ≠ 1 := by
      intro hco
      apply hl1
      ext
      simpa using hco
    exact hwithOne l (by
      simp [Section4Scratch.withOne, hlA, hl1G])

public theorem theorem_10_7_CFon_of_integerSpanOn_of_withOne_support
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {A : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {χ : Section1.ClassFunction M}
    (hSclass :
      ∀ φ : Section1.ClassFunction M, φ ∈ S → Section1.IsClassFunction φ)
    (hSwithOne :
      ∀ φ : Section1.ClassFunction M, φ ∈ S →
        ∀ l : M, (l : G) ∉ Section4Scratch.withOne A → φ l = 0)
    (hχOn : Section5.integerSpanOn S Section5.puncturedSet χ) :
    Section2.CFOn M A χ := by
  rcases hχOn with ⟨hχspan, hχpunct⟩
  refine ⟨?_, ?_⟩
  · rcases hχspan with ⟨v, rfl⟩
    refine theorem_10_7_isClassFunction_evalCoeff
      (fun X : S => (X : Section1.ClassFunction M)) ?_ v
    intro X
    exact hSclass (X : Section1.ClassFunction M) X.property
  · have hχwithOne :
        ∀ l : M, (l : G) ∉ Section4Scratch.withOne A → χ l = 0 := by
      rcases hχspan with ⟨v, rfl⟩
      intro l hl
      have hzero :
          ∀ X : S, (X : Section1.ClassFunction M) l = 0 := by
        intro X
        exact hSwithOne (X : Section1.ClassFunction M) X.property l hl
      simp [Section1.evalCoeff, hzero]
    exact theorem_10_7_support_on_A_of_punctured_and_withOne
      M hχpunct hχwithOne

public theorem theorem_10_7_kernelInducedFamily_member_isClassFunction
    {G : Type u}
    [Group G]
    [Finite G]
    {M N H Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (hS : Section9.kernelInducedFamily M N H Y S) :
    ∀ χ : Section1.ClassFunction M, χ ∈ S → Section1.IsClassFunction χ := by
  intro χ hχ
  rcases hS with ⟨_hYN, _hHN, hmem⟩
  rcases (hmem χ).mp hχ with ⟨θ, _hθirr, _hθne, _hθker, hχeq⟩
  rw [hχeq]
  exact Section1.inducedCF_isClassFunction (N.subgroupOf M) θ

public theorem theorem_10_7_kernelInducedFamily_withOne_ASet_support
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    (h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1))
    (hS : Section9.kernelInducedFamily M (ambientDerivedSubgroup M) MF Y S) :
    ∀ χ : Section1.ClassFunction M, χ ∈ S →
      ∀ l : M, (l : G) ∉ Section4Scratch.withOne (section16ASet M U) →
        χ l = 0 := by
  intro χ hχS l hl
  have hsection4Support :
      Section4Scratch.hypothesis_4_6_statement
        ((ambientDerivedSubgroup M).subgroupOf M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (MF.subgroupOf M)
        (Section8.section8SubgroupSetPreimage M (section16ASet M U)) := by
    exact Section9.hypothesis_4_6_ASet_of_hypothesis_9_2_sec9
      M MF U W1 W2 (Nat.card W1) h92
  have h47 :
      Section4Scratch.theorem_4_7_statement
        ((ambientDerivedSubgroup M).subgroupOf M)
        (MF.subgroupOf M)
        (Section8.section8SubgroupSetPreimage M (section16ASet M U)) := by
    exact
      Section4Scratch.theorem_4_7
        ((ambientDerivedSubgroup M).subgroupOf M)
        (W1.subgroupOf M)
        (W2.subgroupOf M)
        ((W1 ⊔ W2).subgroupOf M)
        (MF.subgroupOf M)
        (Section8.section8SubgroupSetPreimage M (section16ASet M U))
        hsection4Support
  have hInd :
      Section5.inducedFromNonkernelFamily_statement
        ((ambientDerivedSubgroup M).subgroupOf M)
        (MF.subgroupOf M) S :=
    Section9.inducedFromNonkernelFamily_of_kernelInducedFamily_sec9
      M (ambientDerivedSubgroup M) MF Y S hS
  rcases hInd χ hχS with ⟨θ, hθirr, hθnonker, hχeq⟩
  have hχSupport :
      Section1.supportedOn χ
        (Section4Scratch.withOne
          (Section8.section8SubgroupSetPreimage M (section16ASet M U))) := by
    simpa [hχeq] using (h47 θ hθirr hθnonker).2
  have hlM :
      l ∉ Section4Scratch.withOne
        (Section8.section8SubgroupSetPreimage M (section16ASet M U)) := by
    simpa [Section4Scratch.withOne, Section8.section8SubgroupSetPreimage] using hl
  exact (Section1.supportedOn_iff.mp hχSupport) l hlM

public theorem theorem_10_7_CFon_of_integerSpanOn_kernelInducedFamily_ASet
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {χ : Section1.ClassFunction M}
    (h92 : Section9.hypothesis_9_2_statement M MF U W1 W2 (Nat.card W1))
    (hS : Section9.kernelInducedFamily M (ambientDerivedSubgroup M) MF Y S)
    (hχOn : Section5.integerSpanOn S Section5.puncturedSet χ) :
    Section2.CFOn M (section16ASet M U) χ :=
  theorem_10_7_CFon_of_integerSpanOn_of_withOne_support
    (theorem_10_7_kernelInducedFamily_member_isClassFunction hS)
    (theorem_10_7_kernelInducedFamily_withOne_ASet_support h92 hS)
    hχOn

public theorem theorem_10_7_hypothesis2_le_supportingElementCentralizer
    {G : Type u}
    [Group G]
    [Finite G]
    {A A0 : Set G}
    {M MF L LF : Subgroup G}
    {H : G → Subgroup G}
    (hHyp : Section2.Hypothesis2 A M H)
    {a : G}
    (ha : a ∈ A)
    (hSupp : Section8.supportConclusionDataSource M MF M A0 a L LF) :
    H a ≤ elementCentralizerIn LF a := by
  rcases hSupp with
    ⟨_hLmax, _hLF, _hSet, _hSemiL, hSemiC, _hCoprime, _hType⟩
  have hHprod :
      Section2.IsInternalSemidirectProduct (Section2.elementCentralizer a)
        (H a) (Section2.centralizerIn M a) :=
    hHyp.centralizer_eq_product ha
  have hSemiC' :
      Section8.section8SemidirectProductIn (Section2.elementCentralizer a)
        (elementCentralizerIn LF a) (Section2.centralizerIn M a) := by
    simpa [Section2.elementCentralizer, Section2.centralizerIn,
      elementCentralizerIn] using hSemiC
  exact theorem_10_7_left_le_left_of_common_coprime_complement
    hHprod hSemiC' (hHyp.coprime_orders ha ha)

public theorem theorem_10_7_hypothesis2_le_tildeR_of_subset_notation_8_14
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms : Subgroup G}
    {Abook AS A0S A1S DS tildeAS tildeA0S tildeA1S : Set G}
    {H RS : G → Subgroup G}
    (h10S : Section8.notation_8_10_source_data M MF Ms AS A0S A1S)
    (h14S :
      Section8.notation_8_14_source_data M AS A0S A1S DS tildeAS
        tildeA0S tildeA1S RS)
    (hAbookAS : Abook ⊆ AS)
    (hHyp : Section2.Hypothesis2 Abook M H) :
    ∀ a : G, a ∈ Abook → H a ≤ RS a := by
  rcases h14S with
    ⟨_hA1AS, hASA0S, hDS, hRSbot, _hUnique, _hReq, _htildeAS,
      _htildeA0S, _htildeA1S⟩
  intro a ha h hh
  have haA0S : a ∈ A0S := hASA0S (hAbookAS ha)
  by_cases hCentM : Subgroup.centralizer ({a} : Set G) ≤ M
  · have hHbot : H a ≤ ⊥ :=
      theorem_10_7_hypothesis2_complement_le_bot_of_centralizer_le
        hHyp ha hCentM
    have haNotD : a ∉ DS := by
      intro haD
      have haD' : a ∈ Section8.section8DSet M A0S := by
        simpa [hDS] using haD
      exact haD'.2 hCentM
    have hR : RS a = ⊥ := hRSbot a ⟨haA0S, haNotD⟩
    rw [hR]
    exact hHbot hh
  · have haD : a ∈ DS := by
      rw [hDS]
      exact ⟨haA0S, hCentM⟩
    rcases Section8.theorem_8_15_support_of_mem_D
        (G := G) (M := M) (MF := MF) (Ms := Ms)
        (A := AS) (A0 := A0S) (A1 := A1S)
        (D := DS) (tildeA := tildeAS) (tildeA0 := tildeA0S)
        (tildeA1 := tildeA1S) (R := RS)
        (hG := inferInstance) h10S
        ⟨_hA1AS, hASA0S, hDS, hRSbot, _hUnique, _hReq, _htildeAS,
          _htildeA0S, _htildeA1S⟩ haD with
      ⟨L, LF, hSupp, hR⟩
    rw [hR]
    exact
      theorem_10_7_hypothesis2_le_supportingElementCentralizer
        hHyp ha hSupp hh

public theorem theorem_10_7_section16ASet_subset_AS_of_typeII_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S : Subgroup G}
    {AS A0S A1S : Set G}
    (hTypeII : section16TypeII Smax SF)
    (h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (hNotation : Section8.notation_8_10_source_data Smax SF SF AS A0S A1S) :
    section16ASet Smax U ⊆ AS := by
  classical
  rcases h92.typeIISource hTypeII with ⟨hUcomm, hUnorm, U1, U0, hF⟩
  have hSrcII : Section8.typeIIDefinitionData Smax SF :=
    ⟨U, W1S, W2S, U1, U0, h92.typePDefinitionData,
      h92.typeIIToIVSourceCondition, hUcomm, hUnorm, hF⟩
  have hMem :
      Section8.notation_8_10_source_membership_data Smax SF AS :=
    Section8.notation_8_10_source_membership_data_of_source_data hNotation
  have hMF_eq : SF = section10Msigma Smax := by
    rcases section15_exists_KUData_for_maximal (G := G) (M := Smax)
        h92.maximal with
      ⟨K, Uc, hKU15⟩
    have hKU : section16KUData Smax K Uc := by
      simpa [section16KUData] using hKU15
    have hProp :=
      proposition_16_1 (G := G) (M := Smax) (MF := SF)
        (K := K) (U := Uc) h92.maximal h92.mf hKU
    exact hProp.2.2.2.2.2.mpr (Or.inr (Or.inl hTypeII))
  have hASetCentralizer :
      section16ASet Smax U ⊆
        Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) SF := by
    rcases h92.typePDefinitionData with
      ⟨_hSFsource, _hW1cyc, _hW1ne, _hW1hall, _hSsplit, _hUleD,
        _hUnil, _hW1norm, hUSplit, _hSFnotCyc, _hSecondLe, _hFittingEq,
        _hFittingLeD, _hW2le, _hW2cyc, _hW2ne, _hcentralizer, _hhatW⟩
    intro a ha
    rcases ha with ⟨⟨haSmax, hCentSigma_ne⟩, haProd, hane⟩
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCentSigma_ne with
      ⟨c, hcne⟩
    let x : G := c
    have hxSigma : x ∈ section10Msigma Smax := c.property.1
    have hxSF : x ∈ SF := by
      simpa [hMF_eq] using hxSigma
    have hxne : x ≠ 1 := by
      intro hx
      exact hcne (Subtype.ext hx)
    have hxCentA : x ∈ Subgroup.centralizer ({a} : Set G) := c.property.2
    have haD : a ∈ ambientDerivedSubgroup Smax := by
      rcases Set.mem_mul.mp haProd with ⟨u, huU, s, hsSigma, hus⟩
      have hsSF : s ∈ SF := by
        simpa [hMF_eq] using hsSigma
      exact hus ▸ (ambientDerivedSubgroup Smax).mul_mem
        (hUSplit.2.1 huU) (hUSplit.1 hsSF)
    rw [Section8.section8CentralizerUnion]
    refine ⟨x, ⟨hxSF, hxne⟩, ⟨?_, hane⟩⟩
    have hcomm : Commute x a :=
      Subgroup.mem_centralizer_singleton_iff.mp hxCentA
    exact ⟨haD, by
      simpa [Subgroup.mem_centralizer_singleton_iff] using hcomm.symm.eq⟩
  intro x hx
  exact hMem.2 x hSrcII (hASetCentralizer hx)

public theorem theorem_10_7_a1Set_subset_section8CentralizerUnion_of_hypothesis_9_2
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax SF U W1S W2S : Subgroup G}
    (h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S)) :
    Section8.a1Set SF ⊆
      Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) SF := by
  intro x hx
  have hxSharp : x ∈ section16NonidentityElements (SF : Set G) := by
    simpa [Section8.a1Set] using hx
  have hxSF : x ∈ SF := hxSharp.1
  have hxne : x ≠ 1 := hxSharp.2
  have hxDer : x ∈ ambientDerivedSubgroup Smax :=
    Section9.MF_le_ambientDerived_of_hypothesis_9_2_sec9
      Smax SF U W1S W2S (Nat.card W1S) h92 hxSF
  rw [Section8.section8CentralizerUnion]
  refine ⟨x, hxSharp, ?_⟩
  exact ⟨⟨hxDer, by simp [Subgroup.mem_centralizer_singleton_iff]⟩, hxne⟩


public theorem theorem_10_7_exists_notation_8_14_of_typeII_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S : Subgroup G}
    {AS A0S A1S : Set G}
    (hTypeII : section16TypeII Smax SF)
    (h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (h10S : Section8.notation_8_10_source_data Smax SF SF AS A0S A1S) :
    ∃ DS tildeAS tildeA0S tildeA1S : Set G,
    ∃ RS : G → Subgroup G,
      Section8.notation_8_14_source_data Smax AS A0S A1S DS
        tildeAS tildeA0S tildeA1S RS := by
  rcases h92.typeIISource hTypeII with ⟨hUcomm, hUnorm, U1, U0, hF⟩
  have hSrcII : Section8.typeIIDefinitionData Smax SF :=
    ⟨U, W1S, W2S, U1, U0, h92.typePDefinitionData,
      h92.typeIIToIVSourceCondition, hUcomm, hUnorm, hF⟩
  have hMem :
      Section8.notation_8_10_source_membership_data Smax SF AS :=
    Section8.notation_8_10_source_membership_data_of_source_data h10S
  have hA1_eq : A1S = Section8.a1Set SF := h10S.2.2.2.1
  have hA1A : A1S ⊆ AS := by
    intro x hx
    have hxCentralizer :
        x ∈ Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) SF :=
      theorem_10_7_a1Set_subset_section8CentralizerUnion_of_hypothesis_9_2
        h92 (by simpa [hA1_eq] using hx)
    exact hMem.2 x hSrcII hxCentralizer
  have hAA0 : AS ⊆ A0S :=
    theorem_10_7_A_subset_A0_of_notation_8_10_source_data h10S
  rcases Section8.exists_mixed_notation_8_14_source_data_of_theorem_8_13
      Smax SF SF AS A0S A1S (by infer_instance : IsMinCE G)
      h10S hA1A hAA0 with
    ⟨RS, tildeAS, tildeA0S, tildeA1S, h14S⟩
  exact ⟨Section8.section8DSet Smax A0S, tildeAS, tildeA0S, tildeA1S, RS, h14S⟩


public theorem theorem_10_7_exists_notation_8_10_of_typeII_not_typeI_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S : Subgroup G}
    (hTypeII : section16TypeII Smax SF)
    (h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S))
    (_hnotI : ¬ Section8.typeIDefinitionData Smax SF) :
    ∃ AS A0S A1S : Set G,
      Section8.notation_8_10_source_data Smax SF SF AS A0S A1S := by
  rcases h92.typeIISource hTypeII with ⟨hUcomm, hUnorm, hF⟩
  exact Section8.exists_notation_8_10_source_data_of_typeII_source_fields
    h92.maximal h92.mf hTypeII h92.typePDefinitionData
    h92.typeIIToIVSourceCondition hUcomm hUnorm hF

public theorem theorem_10_7_section16MFSubgroup_subgroupOf_normal
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF) :
    (MF.subgroupOf M).Normal := by
  rcases hMF.1 with ⟨_hMFleM, hMFnorm, _hMFnil, _hMFhall⟩
  exact hMFnorm

public theorem theorem_10_7_frobeniusWithKernel_of_section8_frobenius
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hfrob : Section8.section8FrobeniusGroupWithKernel M MF) :
    Section7.frobeniusWithKernel M MF := by
  classical
  rcases hfrob with ⟨U, hcomp, hfrobJoin⟩
  have hfrobM :
      IsFrobeniusGroupWithKernelComplement
        (MF.subgroupOf M) (U.subgroupOf M) := by
    rw [hcomp.2.2.1]
    simpa [section12FrobeniusJoinWithKernel] using hfrobJoin
  refine ⟨hcomp.1, theorem_10_7_section16MFSubgroup_subgroupOf_normal hMF,
    U.subgroupOf M, ?_, ?_, ?_, ?_⟩
  · exact IsFrobeniusGroupWithKernelComplement.isComplement' hfrobM
  · exact IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobM
  · exact IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobM
  · intro r hrne
    have hcentM :
        elementCentralizerIn (MF.subgroupOf M) (r : M) = ⊥ :=
      (lemma_3_1 (MF.subgroupOf M) (U.subgroupOf M)
        (IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobM)
        (IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobM)
        (IsFrobeniusGroupWithKernelComplement.normal hfrobM)
        (IsFrobeniusGroupWithKernelComplement.isComplement' hfrobM)).1
        hfrobM r hrne
    simpa [elementCentralizerIn, Section2.centralizerIn,
      Section2.elementCentralizer] using hcentM

public theorem theorem_10_7_typeP_not_frobeniusWithKernel
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    ¬ Section7.frobeniusWithKernel M MF := by
  classical
  intro hfrob
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, hW1Hall, hMcomp, _hUleDer,
      _hUnil, _hW1norm, hDerComp, _hMFnotcyc, _hSecond, _hFit,
      _hFitLe, hW2le, _hW2cyc, hW2ne, hCentralizer, _hNormalizer⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne with ⟨xW1, hxW1ne⟩
  let x : G := xW1
  have hxW1 : x ∈ W1 := xW1.property
  have hxne : x ≠ 1 := by
    intro hx
    exact hxW1ne (Subtype.ext hx)
  have hxM : x ∈ M := hW1Hall.1 hxW1
  have hMFleDer : MF ≤ ambientDerivedSubgroup M := hDerComp.1
  have hxnotMF : x ∉ MF := by
    intro hxMF
    have hxDer : x ∈ ambientDerivedSubgroup M := hMFleDer hxMF
    have hxBot : x ∈ (⊥ : Subgroup G) :=
      hMcomp.2.2.2.le_bot ⟨hxDer, hxW1⟩
    exact hxne (by simpa using hxBot)
  have hcentBot : Section2.centralizerIn MF x = ⊥ :=
    Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
      (L0 := M) (H := MF) hfrob x hxM hxnotMF
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW2ne with ⟨yW2, hyW2ne⟩
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  have hyMF : y ∈ MF := (hW2le hyW2).1
  have hyCentDer : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
    simpa [hCentralizer x hxW1 hxne] using hyW2
  have hyCentMF : y ∈ Section2.centralizerIn MF x := by
    exact ⟨hyMF, hyCentDer.2⟩
  have hyBot : y ∈ (⊥ : Subgroup G) := by
    simpa [hcentBot] using hyCentMF
  exact hyne (by simpa using hyBot)

public theorem theorem_10_7_typeP_not_section8FrobeniusGroupWithKernel
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    ¬ Section8.section8FrobeniusGroupWithKernel M MF := by
  intro hfrob
  exact theorem_10_7_typeP_not_frobeniusWithKernel hP
    (theorem_10_7_frobeniusWithKernel_of_section8_frobenius hP.1 hfrob)

public theorem theorem_10_7_kernelInducedSubfamily_mem_family
    {G : Type u}
    [Group G]
    [Finite G]
    {M N H Y : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {χ : Section1.ClassFunction M} :
    χ ∈ Section9.kernelInducedSubfamily_sec9 M N H Y S → χ ∈ S := by
  intro hχ
  exact Section9.kernelInducedSubfamily_subset_sec9 M N H Y S hχ

public theorem theorem_10_7_integerSpanOn_sub_of_equal_degree_mem
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S : Finset (Section1.ClassFunction M)}
    {ν χ : Section1.ClassFunction M}
    (hνS : ν ∈ S)
    (hχS : χ ∈ S)
    (hdeg : Section1.degree ν = Section1.degree χ) :
    Section5.integerSpanOn S Section5.puncturedSet (ν - χ) := by
  refine ⟨Section5.integerSpan_sub
      (Section5.integerSpan_of_mem S hνS)
      (Section5.integerSpan_of_mem S hχS), ?_⟩
  apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero (ν - χ)).2
  rw [Section1.degree]
  have hdeg_apply : ν 1 = χ 1 := by
    simpa [Section1.degree] using hdeg
  simp [Pi.sub_apply, hdeg_apply]

public theorem theorem_10_7_reducible_partner_of_subfamily_card
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {S R : Finset (Section1.ClassFunction M)}
    {p q u : ℕ}
    (hp : Nat.Prime p)
    (hRcard : R.card = p - 1)
    (hRdata : Section9.reducibleCharacterSubfamilyData M S R (q * u))
    {χ : Section1.ClassFunction M}
    (hχdeg : Section1.degree χ = (q * u : ℂ)) :
    ∃ ν : Section1.ClassFunction M,
      ν ∈ S ∧
        ¬ Section1.IsIrreducibleCharacterOnGroup ν ∧
          Section1.degree ν = Section1.degree χ := by
  classical
  rcases hRdata with ⟨hRsubS, hRred, _hRall⟩
  have hRpos : 0 < R.card := by
    rw [hRcard]
    exact Nat.sub_pos_of_lt hp.one_lt
  rcases Finset.card_pos.mp hRpos with ⟨ν, hνR⟩
  rcases hRred ν hνR with ⟨hνred, hνdeg⟩
  have hχdeg' : Section1.degree χ = ((q * u : ℕ) : ℂ) := by
    simpa [Nat.cast_mul] using hχdeg
  exact ⟨ν, hRsubS hνR, hνred, hνdeg.trans hχdeg'.symm⟩


public theorem theorem_10_7_conjugateCharacter_involutive
    {L : Type u}
    [Group L]
    (χ : Section1.ClassFunction L) :
    Section1.conjugateCharacter (Section1.conjugateCharacter χ) = χ := by
  ext g
  simp [Section1.conjugateCharacter]

public theorem theorem_10_7_four_character_subset
    {L G : Type u}
    [Group L]
    [Finite L]
    [Group G]
    [Finite G]
    {S9 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {χ ν : Section1.ClassFunction L}
    (h52 : Section5.hypothesis_5_2_statement S9 T)
    (hχS : χ ∈ S9)
    (hνS : ν ∈ S9) :
    ({χ, Section1.conjugateCharacter χ, ν, Section1.conjugateCharacter ν} :
      Finset (Section1.ClassFunction L)) ⊆ S9 := by
  classical
  rcases h52 with ⟨_hsetup, _R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  intro ψ hψ
  simp at hψ
  rcases hψ with rfl | rfl | rfl | rfl
  · exact hχS
  · exact (h52a ⟨χ, hχS⟩).1
  · exact hνS
  · exact (h52a ⟨ν, hνS⟩).1

public theorem theorem_10_7_four_character_hypothesis_5_2
    {L G : Type u}
    [Group L]
    [Finite L]
    [Group G]
    [Finite G]
    {S9 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {χ ν : Section1.ClassFunction L}
    (h52 : Section5.hypothesis_5_2_statement S9 T)
    (hχS : χ ∈ S9)
    (hνS : ν ∈ S9) :
    Section5.hypothesis_5_2_statement
      ({χ, Section1.conjugateCharacter χ, ν, Section1.conjugateCharacter ν} :
        Finset (Section1.ClassFunction L)) T := by
  classical
  let S4 : Finset (Section1.ClassFunction L) :=
    {χ, Section1.conjugateCharacter χ, ν, Section1.conjugateCharacter ν}
  have hsub : S4 ⊆ S9 := by
    simpa [S4] using theorem_10_7_four_character_subset h52 hχS hνS
  rcases h52 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hne : S4.Nonempty := by
    exact ⟨χ, by simp [S4]⟩
  have hclosed :
      ∀ ψ : Section1.ClassFunction L, ψ ∈ S4 →
        Section1.conjugateCharacter ψ ∈ S4 := by
    intro ψ hψ
    simp [S4] at hψ ⊢
    rcases hψ with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (theorem_10_7_conjugateCharacter_involutive χ)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (theorem_10_7_conjugateCharacter_involutive ν)))
  simpa [S4] using
    Section5.hypothesis_5_2_statement_subset hsub hne hclosed
      ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩

public theorem theorem_10_7_four_character_coherent
    {L G : Type u}
    [Group L]
    [Finite L]
    [Group G]
    [Finite G]
    {S9 : Finset (Section1.ClassFunction L)}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {χ ν : Section1.ClassFunction L}
    (h52 : Section5.hypothesis_5_2_statement S9 T)
    (hχS : χ ∈ S9)
    (hνS : ν ∈ S9)
    (hν_degree : Section1.degree ν = Section1.degree χ) :
    Section6.coherentFamily
      ({χ, Section1.conjugateCharacter χ, ν, Section1.conjugateCharacter ν} :
        Finset (Section1.ClassFunction L)) T := by
  classical
  let S4 : Finset (Section1.ClassFunction L) :=
    {χ, Section1.conjugateCharacter χ, ν, Section1.conjugateCharacter ν}
  have h52S4 : Section5.hypothesis_5_2_statement S4 T :=
    theorem_10_7_four_character_hypothesis_5_2 h52 hχS hνS
  rcases h52S4 with ⟨hsetup, R, h52a, h52b, h52c, h52d, h52e⟩
  have hdeg : ∀ X Y : S4,
      Section1.degree (X : Section1.ClassFunction L) =
        Section1.degree (Y : Section1.ClassFunction L) := by
    intro X Y
    have hχchar : Section1.IsCharacter χ := hsetup.2 ⟨χ, by simp [S4]⟩
    have hνchar : Section1.IsCharacter ν := hsetup.2 ⟨ν, by simp [S4]⟩
    have hX :
      Section1.degree (X : Section1.ClassFunction L) = Section1.degree χ := by
      have hmem := X.2
      simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hXχ | hXχbar | hXν | hXνbar
      · rw [hXχ]
      · rw [hXχbar, Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar]
      · rw [hXν, hν_degree]
      · rw [hXνbar, Section5.degree_conjugateCharacter_eq_of_isCharacter hνchar, hν_degree]
    have hY :
      Section1.degree (Y : Section1.ClassFunction L) = Section1.degree χ := by
      have hmem := Y.2
      simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hYχ | hYχbar | hYν | hYνbar
      · rw [hYχ]
      · rw [hYχbar, Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar]
      · rw [hYν, hν_degree]
      · rw [hYνbar, Section5.degree_conjugateCharacter_eq_of_isCharacter hνchar, hν_degree]
    exact hX.trans hY.symm
  simpa [Section6.coherentFamily, S4] using
    (Section5.theorem_5_7 S4 T R hsetup h52a h52b h52c h52d h52e hdeg)


public theorem theorem_10_7_omegaColumn_orthogonal_of_pointwise
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype I]
    {M : Subgroup G}
    {W : Subgroup M}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {Y : Section1.ClassFunction G}
    (hpoint :
      ∀ i j, Section1.scalarProduct G (σ (ω i j)) Y = 0)
    (s : J) :
    Section1.scalarProduct G (∑ i : I, σ (ω i s)) Y = 0 := by
  classical
  have hleft :
      ((∑ i : I, σ (ω i s) : Section1.ClassFunction G)) =
        fun g => ∑ i : I, σ (ω i s) g := by
    ext g
    simp
  rw [hleft, Section1.scalarProduct_fintype_sum_left]
  simp [hpoint]


@[expose] public def theorem_10_7_typeP_partner_selected_column_image_data
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax Ms W1S W2S : Subgroup G}
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ν : Section1.ClassFunction Smax) : Prop :=
  letI : Fintype d52.I := d52.instFintypeI
  ∃ k : d52.J, ∃ ε : ℤ,
    (ε = 1 ∨ ε = -1) ∧
      T4 ν = (ε : ℂ) • (∑ i : d52.I, d52.sigma (d52.omega i k))

@[expose] public def theorem_10_7_typeP_partner_selected_column_image_classification_data
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax Ms W1S W2S : Subgroup G}
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (S4 : Finset (Section1.ClassFunction Smax))
    (T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ν : Section1.ClassFunction Smax) : Prop :=
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  letI : DecidableEq d52.I := d52.instDecidableEqI
  ∃ k j : d52.J, ∃ δSignZ : d52.J → ℤ,
    d52.deltaSign = (fun j => (δSignZ j : ℂ)) ∧
      (∀ j, δSignZ j = 1 ∨ δSignZ j = -1) ∧
        k ≠ d52.j0 ∧
          Section4Scratch.piColumn d52.piChar k = ν ∧
            Section1.conjugateCharacter
                (Section4Scratch.piColumn d52.piChar k) =
              Section4Scratch.piColumn d52.piChar j ∧
            ((T4 ν =
                (δSignZ k : ℂ) •
                  (∑ i : d52.I, d52.sigma (d52.omega i k))) ∨
            (T4 ν =
                  (-(δSignZ k) : ℂ) •
                    (∑ i : d52.I, d52.sigma (d52.omega i j)) ∧
              ∀ l : d52.J, l ≠ d52.j0 →
                Section4Scratch.piColumn d52.piChar l ∈ S4 →
                  Section1.degree (Section4Scratch.piColumn d52.piChar l) =
                    Section1.degree
                      (Section4Scratch.piColumn d52.piChar k) →
                    l = j ∨ l = k))

public theorem theorem_10_7_typeP_partner_selected_column_image_of_classification
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax Ms W1S W2S : Subgroup G}
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {ν : Section1.ClassFunction Smax}
    {d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms)}
    (hClass :
      theorem_10_7_typeP_partner_selected_column_image_classification_data
        d52 S4 T4 ν) :
    theorem_10_7_typeP_partner_selected_column_image_data d52 T4 ν := by
  classical
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  rcases hClass with
    ⟨k, j, δSignZ, _hδSignZ, hδSignZ_sign, _hk0, _hνeq, _hconj, hAlt⟩
  rcases hAlt with hpos | hneg
  · exact ⟨k, δSignZ k, hδSignZ_sign k, hpos⟩
  · refine ⟨j, -δSignZ k, ?_, ?_⟩
    · rcases hδSignZ_sign k with hk | hk
      · right
        simp [hk]
      · left
        simp [hk]
    · simpa using hneg.1


public theorem theorem_10_7_section16Kstar_eq_W2_of_source_typeP
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    section16Kstar M W1 = W2 := by
  classical
  have hPFull : Section8.typePDefinitionData M MF U W1 W2 := hP
  have hMFleSigma : MF ≤ section10Msigma M :=
    (theorem_15_2_chain (G := G) hM hPFull.1).2.1
  have hSigmaD : section10Msigma M ≤ ambientDerivedSubgroup M :=
    (theorem_15_2_chain (G := G) hM hPFull.1).2.2.1
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond,
      _hFit, _hFitDer, hW2le, _hW2cyc, _hW2ne, hCentralizer,
      _hNormalizer⟩
  have hW2leSigma : W2 ≤ section10Msigma M := by
    intro y hy
    exact hMFleSigma (hW2le hy).1
  apply le_antisymm
  · intro y hy
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne with ⟨x, hxne⟩
    have hxW1 : (x : G) ∈ W1 := x.property
    have hxGne : (x : G) ≠ 1 := by
      intro hx
      exact hxne (Subtype.ext hx)
    have hyCentX :
        y ∈ elementCentralizerIn (ambientDerivedSubgroup M) (x : G) := by
      refine ⟨hSigmaD hy.1, ?_⟩
      change y ∈ Subgroup.centralizer ({(x : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hy.2 (x : G) hxW1).symm
    simpa [section16Kstar, hCentralizer (x : G) hxW1 hxGne] using hyCentX
  · intro y hyW2
    refine ⟨hW2leSigma hyW2, ?_⟩
    change y ∈ Subgroup.centralizer (W1 : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hxW1
    by_cases hx : x = 1
    · simp [hx]
    · have hyCentX : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := by
        simpa [hCentralizer x hxW1 hx] using hyW2
      exact Subgroup.mem_centralizer_iff.mp hyCentX.2 x (by simp)


@[expose] public def theorem_10_7_typeP_partner_cyclicTI_selected_column_to_transported_row_reindex_data
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    {M Smax Ms W1S W2S : Subgroup G}
    {W : Subgroup M}
    {A52 : Set G}
    (ω : I → J → Section1.ClassFunction W)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S A52)
    (e : W ≃* d52.W) : Prop :=
  ∀ k : d52.J, ∃ r : I, ∃ reindex : d52.I ≃ J,
    ∀ i : d52.I,
      d52.omega i k =
        Section6.theorem_6_8_transportClassFunction e (ω r (reindex i))

public theorem theorem_10_7_transport_row_sum_eq_source_row
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    [Fintype J]
    {M Smax Ms W1S W2S : Subgroup G}
    {A52 : Set G}
    {W : Subgroup M}
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S A52)
    (e : W ≃* d52.W)
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (hCompat :
      ∀ i : I, ∀ j : J,
        σ (ω i j) =
          d52.sigma
            (Section6.theorem_6_8_transportClassFunction e (ω i j)))
    (r : I) :
    (∑ j : J,
        d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω r j))) =
      ∑ j : J, σ (ω r j) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro j _hj
  exact (hCompat r j).symm


@[expose] public noncomputable def theorem_10_7_conjByMulEquiv
    {G : Type u} [Group G]
    (H : Subgroup G) (g : G) :
    H ≃* H.conjBy g where
  toFun x := by
    refine ⟨g * (x : G) * g⁻¹, ?_⟩
    change g * (x : G) * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨x, x.2, by simp [MulAut.conj_apply]⟩
  invFun y := by
    refine ⟨g⁻¹ * (y : G) * g, ?_⟩
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hxH, hxy⟩
    have hyx : g⁻¹ * (y : G) * g = x := by
      calc
        g⁻¹ * (y : G) * g = g⁻¹ * (g * x * g⁻¹) * g := by
          rw [← hxy]
          simp [MulAut.conj_apply]
        _ = x := by
          simp [mul_assoc]
    simpa [hyx] using hxH
  left_inv x := by
    ext
    simp [mul_assoc]
  right_inv y := by
    ext
    simp [mul_assoc]
  map_mul' x y := by
    ext
    simp [mul_assoc]

public theorem theorem_10_7_omegaSystem_transport_swap_of_conjugating_equiv
    {G : Type u} [Group G] [Finite G]
    {M Smax W1 W2 W1S W2S : Subgroup G}
    {W : Subgroup M} {Wsel : Subgroup Smax}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hW1M : W1 ≤ M) (hW2M : W2 ≤ M)
    (hW1S : W1S ≤ Smax) (hW2S : W2S ≤ Smax)
    (hω : Section3.OmegaSystem
      (W1.subgroupOf M) (W2.subgroupOf M) W I J i0 j0 ω)
    (g : G)
    (hW1S_eq : W1S = W2.conjBy g)
    (hW2S_eq : W2S = W1.conjBy g)
    (e : W ≃* Wsel)
    (he : ∀ x : W, (((e x : Wsel) : Smax) : G) =
      g * ((x : M) : G) * g⁻¹) :
    Section3.OmegaSystem
      (W1S.subgroupOf Smax) (W2S.subgroupOf Smax) Wsel
      J I j0 i0
      (fun j i => Section6.theorem_6_8_transportClassFunction e (ω i j)) := by
  classical
  have hcard1 :
      Nat.card (W1S.subgroupOf Smax) = Nat.card (W2.subgroupOf M) := by
    rw [natCard_subgroupOf_eq W1S Smax hW1S,
      natCard_subgroupOf_eq W2 M hW2M, hW1S_eq]
    exact Nat.card_congr (theorem_10_7_conjByMulEquiv W2 g).toEquiv.symm
  have hcard2 :
      Nat.card (W2S.subgroupOf Smax) = Nat.card (W1.subgroupOf M) := by
    rw [natCard_subgroupOf_eq W2S Smax hW2S,
      natCard_subgroupOf_eq W1 M hW1M, hW2S_eq]
    exact Nat.card_congr (theorem_10_7_conjByMulEquiv W1 g).toEquiv.symm
  have hmem1 : ∀ x : W,
      ((x : M) ∈ W2.subgroupOf M) ↔
        (((e x : Wsel) : Smax) ∈ W1S.subgroupOf Smax) := by
    intro x
    change (((x : M) : G) ∈ W2) ↔ ((((e x : Wsel) : Smax) : G) ∈ W1S)
    rw [hW1S_eq, he x]
    simp [Subgroup.conjBy, MulAut.conj_apply, mul_assoc]
  have hmem2 : ∀ x : W,
      ((x : M) ∈ W1.subgroupOf M) ↔
        (((e x : Wsel) : Smax) ∈ W2S.subgroupOf Smax) := by
    intro x
    change (((x : M) : G) ∈ W1) ↔ ((((e x : Wsel) : Smax) : G) ∈ W2S)
    rw [hW2S_eq, he x]
    simp [Subgroup.conjBy, MulAut.conj_apply, mul_assoc]
  exact Section6.theorem_6_8_notation_3_3_transport e hcard1 hcard2 hmem1 hmem2
    (Section3.notation_3_3_statement_swap hω)


public theorem theorem_10_7_eq_conjBy_of_subgroupOf_map_conj
    {G : Type u} [Group G] {D U V : Subgroup G}
    (hUD : U ≤ D) (hVD : V ≤ D) {d : D}
    (hconj :
      V.subgroupOf D =
        (U.subgroupOf D).map (MulAut.conj d).toMonoidHom) :
    V = U.conjBy (d : G) := by
  ext x
  constructor
  · intro hxV
    have hxloc : (⟨x, hVD hxV⟩ : D) ∈ V.subgroupOf D := by
      simpa [Subgroup.mem_subgroupOf] using hxV
    rw [hconj] at hxloc
    rcases Subgroup.mem_map.mp hxloc with ⟨y, hyUloc, hyx⟩
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf] using hyUloc
    exact Subgroup.mem_map.mpr ⟨(y : G), hyU, by
      have hyxG := congrArg Subtype.val hyx
      simpa [MulAut.conj_apply] using hyxG⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyU, hyx⟩
    have hyD : y ∈ D := hUD hyU
    have hxD : x ∈ D := by
      rw [← hyx]
      exact D.mul_mem (D.mul_mem d.property hyD) (D.inv_mem d.property)
    have hxloc : (⟨x, hxD⟩ : D) ∈ V.subgroupOf D := by
      rw [hconj]
      refine Subgroup.mem_map.mpr ⟨(⟨y, hyD⟩ : D), ?_, ?_⟩
      · simpa [Subgroup.mem_subgroupOf] using hyU
      · apply Subtype.ext
        simpa [MulAut.conj_apply] using hyx
    simpa [Subgroup.mem_subgroupOf] using hxloc

public theorem theorem_10_7_solvable_of_normal_and_quotient_source_data
    {L : Type u} [Group L]
    (N : Subgroup L) [N.Normal] :
    Group.IsSolvable N →
      Group.IsSolvable (L ⧸ N) →
        Group.IsSolvable L := by
  intro hN hQ
  let _ : Group.IsSolvable N := hN
  let _ : Group.IsSolvable (L ⧸ N) := hQ
  exact
    Group.isSolvable_of_ker_le_range
      N.subtype
      (QuotientGroup.mk' N)
      (by
        intro x hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        exact (QuotientGroup.eq_one_iff (N := N) (x := x)).1 hx)

public theorem theorem_10_7_typeP_outer_complements_conj_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U V W1 W2 W1' W2' : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hP' : Section8.typePDefinitionData M MF V W1' W2') :
    ∃ d : M, W1' = W1.conjBy (d : G) := by
  classical
  have hP0 : Section8.typePDefinitionData M MF U W1 W2 := hP
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hcompW1, _hUleD,
      _hUnil, _hW1norm, _hCompU, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2le, _hW2cyc, _hW2ne, _hCentralizer,
      _hNormalizer⟩
  rcases hP' with
    ⟨_hMF', _hW1cyc', _hW1ne', _hW1Hall', hcompW1', _hVleD,
      _hVnil, _hW1norm', _hCompV, _hMFnotcyc', _hSecond', _hFit',
      _hFitDer', _hW2le', _hW2cyc', _hW2ne', _hCentralizer',
      _hNormalizer'⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  let _ : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hcomp1 :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement'
        (W1.subgroupOf M) :=
    Section9.section12ComplementIn_left_isComplement'_subgroupOf_sec9 hcompW1
  have hcomp2 :
      ((ambientDerivedSubgroup M).subgroupOf M).IsComplement'
        (W1'.subgroupOf M) :=
    Section9.section12ComplementIn_left_isComplement'_subgroupOf_sec9 hcompW1'
  have hDleM : D ≤ M := by
    simpa [D] using hcompW1.1
  have hDsub_solv :
      Group.IsSolvable ((ambientDerivedSubgroup M).subgroupOf M) := by
    have hDsolv : Group.IsSolvable D := by
      simpa [D] using typePDefinitionData_ambientDerived_solvable hP0
    let e : ((ambientDerivedSubgroup M).subgroupOf M) ≃* D :=
      (Subgroup.subgroupOfEquivOfLe (H := D) (K := M) hDleM)
    have _ : Group.IsSolvable D := hDsolv
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hW1sub_cyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hcompW1.2.1).isCyclic.mpr
      _hW1cyc
  have hW1sub_solv : Group.IsSolvable (W1.subgroupOf M) := by
    let _ : IsCyclic (W1.subgroupOf M) := hW1sub_cyclic
    infer_instance
  have hquot_solv :
      Group.IsSolvable (M ⧸ ((ambientDerivedSubgroup M).subgroupOf M)) := by
    have _ : Group.IsSolvable (W1.subgroupOf M) := hW1sub_solv
    exact Group.isSolvable_of_isSolvable_injective
      (f := hcomp1.symm.QuotientMulEquiv.toMonoidHom)
      hcomp1.symm.QuotientMulEquiv.injective
  have hMsolv : Group.IsSolvable M := by
    exact theorem_10_7_solvable_of_normal_and_quotient_source_data
      ((ambientDerivedSubgroup M).subgroupOf M) hDsub_solv hquot_solv
  rcases _hW1Hall with ⟨_hW1leM, hHall1⟩
  have hW1sub_card_eq :
      Nat.card (W1'.subgroupOf M) = Nat.card (W1.subgroupOf M) :=
    (hcomp2.symm.index_eq_card).symm.trans hcomp1.symm.index_eq_card
  have hW1sub_index_eq :
      (W1'.subgroupOf M).index = (W1.subgroupOf M).index :=
    hcomp2.index_eq_card.trans hcomp1.index_eq_card.symm
  have hHall2 : IsHallSubgroup (subgroupPrimeSet W1) (W1'.subgroupOf M) := by
    refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet W1)
      (H := W1'.subgroupOf M) ?_ ?_
    · intro p hp
      exact hHall1.p_in_pi_of_p_dvd_card p <| by
        rw [← hW1sub_card_eq]
        exact hp
    · intro p hp hpidx
      exact (hHall1.p_in_pi_of_p_dvd_index p (by
        rw [← hW1sub_index_eq]
        exact hpidx)) hp
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := M) hMsolv hHall1 hHall2 with
    ⟨d, hconj⟩
  have hEq :
      W1' = W1.conjBy (d : G) :=
    theorem_10_7_eq_conjBy_of_subgroupOf_map_conj
      (D := M) hcompW1.2.1 hcompW1'.2.1 hconj
  exact ⟨d, hEq⟩


public def theorem_10_7_typeP_partner_selected_column_preimage_data
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax Ms W1S W2S : Subgroup G}
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (ν : Section1.ClassFunction Smax) : Prop :=
  letI : Fintype d52.I := d52.instFintypeI
  letI : Fintype d52.J := d52.instFintypeJ
  ∃ k j : d52.J,
    k ≠ d52.j0 ∧
      Section4Scratch.piColumn d52.piChar k = ν ∧
        Section1.conjugateCharacter
            (Section4Scratch.piColumn d52.piChar k) =
          Section4Scratch.piColumn d52.piChar j

public theorem theorem_10_7_deltaSign_int_witness_of_hypothesis52FullData
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
      d52.deltaSign = (fun j => (δSign j : ℂ)) ∧
        ∀ j, δSign j = 1 ∨ δSign j = -1 := by
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
  refine ⟨δSign, ?_, ?_⟩
  · funext j
    by_cases hδ : d52.deltaSign j = 1
    · simp [δSign, hδ]
    · have hsign : Section1.IsSign (d52.deltaSign j) := h43b.2.1 j
      rw [Section1.IsSign] at hsign
      rcases hsign with hδone | hδneg
      · exact False.elim (hδ hδone)
      · simp [δSign, hδneg]
  · intro j
    by_cases hδ : d52.deltaSign j = 1 <;> simp [δSign, hδ]

public theorem theorem_10_7_inducedFromNonkernelFamily_of_section8InducedNonkernelFamily
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

public theorem theorem_10_7_section8InducedNonkernelFamily_mono
    {G : Type u}
    [Group G]
    [Finite G]
    {M Ms : Subgroup G}
    {S4 S9 : Finset (Section1.ClassFunction M)}
    (hsub : S4 ⊆ S9)
    (hne : S4.Nonempty)
    (hclosed :
      ∀ χ : Section1.ClassFunction M, χ ∈ S4 →
        Section1.conjugateCharacter χ ∈ S4)
    (hS9 : Section8.section8InducedNonkernelFamily M Ms S9) :
    Section8.section8InducedNonkernelFamily M Ms S4 := by
  refine ⟨hne, hclosed, ?_⟩
  intro χ hχ
  exact hS9.2.2 χ (hsub hχ)

public theorem theorem_10_7_typeP_partner_selected_column_preimage_of_fullData
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax W1S W2S Ms : Subgroup G}
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    {S : Finset (Section1.ClassFunction Smax)}
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (hInd : Section5.inducedFromNonkernelFamily_statement
      (derivedSubgroup Smax) (Ms.subgroupOf Smax) S)
    (ν : Section1.ClassFunction Smax)
    (hνS : ν ∈ S)
    (hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν) :
    theorem_10_7_typeP_partner_selected_column_preimage_data d52 ν := by
  classical
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  rcases d52.fullHypothesis with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      htail⟩
  rcases htail with
    ⟨hω, h43b, _h43c, _h43d, h45a, h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hBaseColumn⟩
  let X : S := ⟨ν, hνS⟩
  have hXnotirr :
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (X : Section1.ClassFunction Smax) := by
    simpa [X] using hν_reducible
  rcases Section5.theorem_5_3_b_nonbase_piColumn_pf53
      (K := derivedSubgroup Smax)
      (W1 := W1S.subgroupOf Smax)
      (W2 := W2S.subgroupOf Smax)
      (W := d52.W)
      (H := Ms.subgroupOf Smax)
      (i0 := d52.i0)
      (j0 := d52.j0)
      (ω := d52.omega)
      (σL := d52.sigmaM)
      (piChar := d52.piChar)
      (xChar := d52.xChar)
      (deltaSign := d52.deltaSign)
      hω h43b h45a h45b hInd X hXnotirr with
    ⟨k, hk0, hXk⟩
  let Xbar : S :=
    ⟨Section1.conjugateCharacter ν, by
      simpa [X] using (h52a X).1⟩
  have hXbarnotirr :
      ¬ Section1.IsIrreducibleCharacterOnGroup
        (Xbar : Section1.ClassFunction Smax) := by
    intro hXbarirr
    have hνconjconjIrr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.conjugateCharacter (Section1.conjugateCharacter ν)) := by
      simpa [Xbar] using
        (Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hXbarirr)
    exact hν_reducible
      ((theorem_10_7_conjugateCharacter_involutive ν) ▸ hνconjconjIrr)
  rcases Section5.theorem_5_3_b_nonbase_piColumn_pf53
      (K := derivedSubgroup Smax)
      (W1 := W1S.subgroupOf Smax)
      (W2 := W2S.subgroupOf Smax)
      (W := d52.W)
      (H := Ms.subgroupOf Smax)
      (i0 := d52.i0)
      (j0 := d52.j0)
      (ω := d52.omega)
      (σL := d52.sigmaM)
      (piChar := d52.piChar)
      (xChar := d52.xChar)
      (deltaSign := d52.deltaSign)
      hω h43b h45a h45b hInd Xbar hXbarnotirr with
    ⟨j, _hj0, hXbarj⟩
  have hνk :
      ν = Section4Scratch.piColumn d52.piChar k := by
    simpa [X] using hXk
  have hconjνj :
      Section1.conjugateCharacter ν =
        Section4Scratch.piColumn d52.piChar j := by
    simpa [Xbar] using hXbarj
  refine ⟨k, j, hk0, hνk.symm, ?_⟩
  simpa [hνk] using hconjνj

public theorem theorem_10_7_typeP_partner_selected_column_preimage_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 C Cprime Ms : Subgroup G}
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {S4 : Finset (Section1.ClassFunction Smax)}
    (_h52S4 : Section5.hypothesis_5_2_statement S4 T)
    (ν : Section1.ClassFunction Smax)
    (_hS4sub : S4 ⊆ S9)
    (_hνS4 : ν ∈ S4)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν) :
    theorem_10_7_typeP_partner_selected_column_preimage_data d52 ν := by
  classical
  rcases _h52 with ⟨hsetup9, _R9, _h52a9, _h52b9, _h52c9, _h52d9, _h52e9⟩
  have hS9ne : S9.Nonempty := hsetup9.1
  have hS8S9 : Section8.section8InducedNonkernelFamily Smax Ms S9 :=
    Section9.section8InducedNonkernelFamily_of_kernelInducedFamily_msChoice_nonempty_sec9
      Smax SF U W1S W2S Ms H0 S9 _h95.hypothesis92 _hMs
      _h95.kernelInduced hS9ne
  have hS8S4 : Section8.section8InducedNonkernelFamily Smax Ms S4 := by
    rcases _h52S4 with
      ⟨hsetup4, _R4, h52a4, _h52b4, _h52c4, _h52d4, _h52e4⟩
    exact theorem_10_7_section8InducedNonkernelFamily_mono
      _hS4sub hsetup4.1
      (fun ψ hψ => (h52a4 ⟨ψ, hψ⟩).1) hS8S9
  have hInd4 :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup Smax) (Ms.subgroupOf Smax) S4 :=
    theorem_10_7_inducedFromNonkernelFamily_of_section8InducedNonkernelFamily hS8S4
  rcases _h52S4 with
    ⟨_hsetup4, _R4, h52a4, _h52b4, _h52c4, _h52d4, _h52e4⟩
  exact theorem_10_7_typeP_partner_selected_column_preimage_of_fullData
    d52 h52a4 hInd4 ν _hνS4 _hν_reducible

public theorem theorem_10_7_typeP_partner_selected_column_image_classification_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 C Cprime Ms : Subgroup G}
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (_hT4Iso : Section5.isCFLinearIsometryOnSpan S4 T4)
    (_hT4Virt : Section5.mapsIntegerSpanToVirtualCharacters S4 T4)
    (_hT4Agree : Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet T T4)
    (_h52S4 : Section5.hypothesis_5_2_statement S4 T)
    (χ ν : Section1.ClassFunction Smax)
    (_hχS4 : χ ∈ S4)
    (_hχbarS4 : Section1.conjugateCharacter χ ∈ S4)
    (_hS4sub : S4 ⊆ S9)
    (_hνS4 : ν ∈ S4)
    (_hν_mem : ν ∈ S9)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν)
    (_hν_degree : Section1.degree ν = Section1.degree χ)
    (_hχ_family : χ ∈ S9)
    (_hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ) :
    theorem_10_7_typeP_partner_selected_column_image_classification_data
      d52 S4 T4 ν := by
  classical
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  rcases theorem_10_7_typeP_partner_selected_column_preimage_source_data
      T S9 d52 _h95 _h52 _hMs _hT_eq _h52S4 ν
      _hS4sub _hνS4 _hν_reducible with
    ⟨k, j, hk0, hνeq, hconj⟩
  rcases _h52 with ⟨hsetup9, _R9, _h52a9, _h52b9, _h52c9, _h52d9, _h52e9⟩
  have hS9ne : S9.Nonempty := hsetup9.1
  have hS8S9 : Section8.section8InducedNonkernelFamily Smax Ms S9 :=
    Section9.section8InducedNonkernelFamily_of_kernelInducedFamily_msChoice_nonempty_sec9
      Smax SF U W1S W2S Ms H0 S9 _h95.hypothesis92 _hMs
      _h95.kernelInduced hS9ne
  have hS8S4 : Section8.section8InducedNonkernelFamily Smax Ms S4 := by
    rcases _h52S4 with
      ⟨hsetup4, _R4, h52a4, _h52b4, _h52c4, _h52d4, _h52e4⟩
    exact theorem_10_7_section8InducedNonkernelFamily_mono
      _hS4sub hsetup4.1
      (fun ψ hψ => (h52a4 ⟨ψ, hψ⟩).1) hS8S9
  have hInd4 :
      Section5.inducedFromNonkernelFamily_statement
        (derivedSubgroup Smax) (Ms.subgroupOf Smax) S4 :=
    theorem_10_7_inducedFromNonkernelFamily_of_section8InducedNonkernelFamily hS8S4
  rcases _h52S4 with
    ⟨_hsetup4, _R4, h52a4, _h52b4, _h52c4, _h52d4, _h52e4⟩
  have hCtx :=
    Section5.theorem_5_3_b_core_context_of_supported_pf53
      (L := Smax)
      (K := derivedSubgroup Smax)
      (W1 := W1S.subgroupOf Smax)
      (W2 := W2S.subgroupOf Smax)
      (W := d52.W)
      (H := Ms.subgroupOf Smax)
      (A := Section8.section8SubgroupSetPreimage Smax
        (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
      (i0 := d52.i0)
      (j0 := d52.j0)
      (ω := d52.omega)
      (σL := d52.sigmaM)
      (σ := d52.sigma)
      (piChar := d52.piChar)
      (xChar := d52.xChar)
      (deltaSign := d52.deltaSign)
      (τ := d52.tau)
      (H_A := d52.H_A)
      d52.fullHypothesis
  have hIrrMem :
      ∃ X : S4,
        Section1.IsIrreducibleCharacterOnGroup
          (X : Section1.ClassFunction Smax) :=
    ⟨⟨χ, _hχS4⟩, _hχ_irreducible⟩
  have hkS4 : Section4Scratch.piColumn d52.piChar k ∈ S4 := by
    rw [hνeq]
    exact _hνS4
  have hT4Agree' :
      Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet d52.tau T4 := by
    simpa [← _hT_eq] using _hT4Agree
  have hAlt :=
    Section5.theorem_5_8_core
      (K := derivedSubgroup Smax)
      (W1 := W1S.subgroupOf Smax)
      (W2 := W2S.subgroupOf Smax)
      (W := d52.W)
      (H := Ms.subgroupOf Smax)
      (A := Section8.section8SubgroupSetPreimage Smax
        (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
      (i0 := d52.i0)
      (j0 := d52.j0)
      (ω := d52.omega)
      (σL := d52.sigmaM)
      (σ := d52.sigma)
      (piChar := d52.piChar)
      (xChar := d52.xChar)
      (deltaSign := d52.deltaSign)
      (τ := d52.tau)
      (S := S4)
      hCtx h52a4 hIrrMem hInd4 k hk0 hkS4 j hconj T4
      _hT4Iso _hT4Virt hT4Agree'
  rcases theorem_10_7_deltaSign_int_witness_of_hypothesis52FullData d52 with
    ⟨δSignZ, hδSignZ, hδSignZ_sign⟩
  refine ⟨k, j, δSignZ, hδSignZ, hδSignZ_sign, hk0, hνeq, hconj, ?_⟩
  rcases hAlt with hpos | hneg
  · left
    rw [← hνeq, hpos, hδSignZ]
    simp [Section4Scratch.omegaColumnSigma]
  · right
    refine ⟨?_, ?_⟩
    · rw [← hνeq, hneg.1, hδSignZ]
      simp [Section4Scratch.omegaColumnSigma]
    · exact hneg.2


public theorem theorem_10_7_pairDiff_integerSpanOn_punctured
    {L : Type u}
    [Group L]
    [Finite L]
    {S : Finset (Section1.ClassFunction L)}
    (hsetup : Section5.hypothesis_5_2_setup_statement S)
    (h52a : Section5.hypothesis_5_2_a_statement S)
    (X : S) :
    Section5.integerSpanOn S Section5.puncturedSet
      ((X : Section1.ClassFunction L) -
        Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
  classical
  refine ⟨?_, ?_⟩
  · exact Section5.integerSpan_sub
      (Section5.integerSpan_of_mem S X.2)
      (Section5.integerSpan_of_mem S (h52a X).1)
  · apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    have hXchar : Section1.IsCharacter (X : Section1.ClassFunction L) :=
      hsetup.2 X
    rw [Section1.degree]
    have hdeg_apply :
        (X : Section1.ClassFunction L) 1 =
          Section1.conjugateCharacter (X : Section1.ClassFunction L) 1 := by
      simpa [Section1.degree] using
        (Section5.degree_conjugateCharacter_eq_of_isCharacter hXchar).symm
    simp [Pi.sub_apply, hdeg_apply]


public theorem theorem_10_7_orthogonalFinsets_mono_right
    {G : Type u}
    [Group G]
    [Finite G]
    {R Ω Ω' : Finset (Section1.ClassFunction G)}
    (horth : Section5.orthogonalFinsets R Ω')
    (hsub : Ω ⊆ Ω') :
    Section5.orthogonalFinsets R Ω := by
  intro φ ψ hφ hψ
  exact horth hφ (hsub hψ)

public theorem theorem_10_7_theorem_5_3_b_extra_transport_of_table_subset
    {L : Type u}
    [Group L]
    [Finite L]
    {G : Type u}
    [Group G]
    [Finite G]
    {S : Finset (Section1.ClassFunction L)}
    {R : S → Finset (Section1.ClassFunction G)}
    {Ω Ω' : Finset (Section1.ClassFunction G)}
    (hExtra : Section5.theorem_5_3_b_extra_statement S R Ω')
    (hsub : Ω ⊆ Ω') :
    Section5.theorem_5_3_b_extra_statement S R Ω := by
  intro φ hφirr
  exact theorem_10_7_orthogonalFinsets_mono_right (hExtra φ hφirr) hsub

public theorem theorem_10_7_typeP_partner_pairDiff_CFon_ASet
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 C Cprime : Subgroup G}
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (h52 : Section5.hypothesis_5_2_statement S9 T)
    (X : S9) :
    Section2.CFOn Smax (section16ASet Smax U)
      ((X : Section1.ClassFunction Smax) -
        Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) := by
  rcases h52 with ⟨hsetup, _R, h52a, _h52b, _h52c, _h52d, _h52e⟩
  have hdiff :
      Section5.integerSpanOn S9 Section5.puncturedSet
        ((X : Section1.ClassFunction Smax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) :=
    theorem_10_7_pairDiff_integerSpanOn_punctured hsetup h52a X
  exact theorem_10_7_CFon_of_integerSpanOn_kernelInducedFamily_ASet
    h95.hypothesis92 h95.kernelInduced hdiff

public theorem theorem_10_7_typeP_partner_cyclicTI_R_pairDiff_transform_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U W1S W2S H0 C Cprime Ms : Subgroup G}
    {A52 : Set G}
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S A52)
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hT_eq : T = d52.tau)
    (X : S9) :
    T ((X : Section1.ClassFunction Smax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) =
      d52.tau ((X : Section1.ClassFunction Smax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) := by
  have _hDiffCFOn :
      Section2.CFOn Smax (section16ASet Smax U)
        ((X : Section1.ClassFunction Smax) -
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) :=
    theorem_10_7_typeP_partner_pairDiff_CFon_ASet T S9 _h95 _h52 X
  -- Source PF `(10.7)`: the selected PF `(9.5)` Dade map `T` and the
  -- selected Section 8 full-data map `d52.tau` give the same transform on the
  -- conjugate-pair difference used by PF `(5.2.d)`, after the checked helper
  -- above verifies that this difference lies on the common Dade domain.
  rw [hT_eq]

@[expose] public def theorem_10_7_typeP_partner_cyclicTI_table_alignment_data
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type*}
    {M Smax Ms W1S W2S : Subgroup G}
    {W : Subgroup M}
    (ω : I → J → Section1.ClassFunction W)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms)) :
    Prop :=
  ∀ i : I, ∀ j : J, ∃ i' : d52.I, ∃ j' : d52.J,
    σ (ω i j) = d52.sigma (d52.omega i' j')


public theorem theorem_10_8_exists_hypothesis_10_4_a_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
      ∃ W : Subgroup M, ∃ A A0 : Set M, ∃ i0 : I, ∃ j0 : J,
      ∃ μ : I → J → Section1.ClassFunction M,
      ∃ δSign : J → ℤ,
      ∃ ω : I → J → Section1.ClassFunction W,
      ∃ σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G,
      ∃ ξ : Section1.ClassFunction M, ∃ d n : ℕ, ∃ δ : ℤ,
        @hypothesis_10_4_a_supported_data G _ _ I J instI instJ decI decJ
          M MF W1 W2 V W A A0 S τ ξ i0 j0 μ δSign ω σ d n δ := by
  rcases theorem_10_2_supported M MF W1 W2 V S τ h10 with
    ⟨ξ, hξS, hξIrr, hξDegree⟩
  rcases exists_section10FourSixNotationSupportedData_of_hypothesis_10_1_supported_data
      h10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign, ω, σ,
      hNotation⟩
  rcases @theorem_10_3_supported G _ _ _ I J instI instJ decI decJ
      M MF W1 W2 V W A A0 S τ i0 j0 μ δSign ω σ h10 hNotation with
    ⟨d, n, δ, hUniform⟩
  exact ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign, ω, σ,
    ξ, d, n, δ, ⟨h10, hNotation, hξS, hξIrr, hξDegree, hUniform⟩⟩

public theorem theorem_10_8_dadeSupport_subset_tildeA_of_notation_8_14_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R) :
    Section2.dadeSupport A R ⊆ tildeA := by
  intro g hg
  rcases h14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hUnique, _hReq, htildeA, _htildeA0,
      _htildeA1⟩
  rcases hg with ⟨a, ha, r, hr, hconj⟩
  rcases hconj with ⟨y, hy⟩
  rw [htildeA]
  refine ⟨a, ha, ?_⟩
  refine ⟨a * r, ?_, y⁻¹, by simp, ?_⟩
  · exact ⟨r, hr, rfl⟩
  · calc
      g = y⁻¹ * (y * g * y⁻¹) * y := by group
      _ = y⁻¹ * (a * r) * y := by
        rw [show y * g * y⁻¹ = a * r by simpa [Section2.conjBy] using hy]
      _ = y⁻¹ * (a * r) * (y⁻¹)⁻¹ := by simp

public theorem theorem_10_8_dadeTransform_eq_zero_of_supportedOn_of_not_mem_dadeSupport
    {G : Type u}
    [Group G]
    {L : Subgroup G}
    {A A0 : Set G}
    {H : G → Subgroup G}
    (hA0L : ∀ a ∈ A0, a ∈ L)
    {α : Section1.ClassFunction L}
    (hα : Section1.supportedOn α (Section8.section8SubgroupSetPreimage L A))
    {g : G}
    (hg : g ∉ Section2.dadeSupport A H) :
    Section2.dadeTransform H hA0L α g = 0 := by
  classical
  by_cases hmem : ∃ a ∈ A0, ∃ h ∈ H a, Section2.conjugateIn g (a * h)
  · let a : G := Classical.choose hmem
    have ha0 : a ∈ A0 := (Classical.choose_spec hmem).1
    let h : G := Classical.choose (Classical.choose_spec hmem).2
    have hh : h ∈ H a := (Classical.choose_spec (Classical.choose_spec hmem).2).1
    have hconj : Section2.conjugateIn g (a * h) :=
      (Classical.choose_spec (Classical.choose_spec hmem).2).2
    have ha_not : a ∉ A := by
      intro ha
      exact hg ⟨a, ha, h, hh, hconj⟩
    have hαzero : α ⟨a, hA0L a ha0⟩ = 0 := by
      rw [Section1.supportedOn_iff] at hα
      exact hα ⟨a, hA0L a ha0⟩ (by
        simpa [Section8.section8SubgroupSetPreimage] using ha_not)
    simpa [Section2.dadeTransform, hmem, a] using hαzero
  · simp [Section2.dadeTransform, hmem]


public theorem theorem_10_8_derived_nonidentity_subset_A_of_hypothesis_10_4_a_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    ((derivedSubgroup M : Subgroup M) : Set M) \ {1} ⊆ A := by
  rcases h104a with
    ⟨h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  have h46 :=
    hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hNotation
  rcases h46 with
    ⟨_h42, _hNormal, _hW2H, _hHK, hUnionSub, _hASub⟩
  intro x hx
  let hxH : derivedSubgroup M := ⟨x, hx.1⟩
  let hidx : {h : derivedSubgroup M // (h : M) ≠ 1} := ⟨hxH, hx.2⟩
  have hxCentral :
      x ∈ (((Section2.centralizerIn (derivedSubgroup M)
        ((hidx : derivedSubgroup M) : M)) : Set M) \ {1}) := by
    constructor
    · rw [Section2.centralizerIn, Section2.elementCentralizer]
      exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x)⟩
    · simpa using hx.2
  exact hUnionSub (Set.mem_iUnion.mpr ⟨hidx, hxCentral⟩)

public theorem theorem_10_8_baseColumnMinusXi_CFOn_A0book_of_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I : Type v}
    {J : Type w}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ)
    {MFsrc Ms : Subgroup G}
    {Abook A0book A1book : Set G}
    (hSource :
      A = Section8.section8SubgroupSetPreimage M Abook ∧
        Section8.section8SubgroupSetPreimage M A0book ⊆ A0 ∧
        Section8.notation_8_10_source_data M MFsrc Ms Abook A0book A1book ∧
        ∃ H_A0 : G → Subgroup G,
          ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
            ∀ α : Section1.ClassFunction M,
              Section2.CFOn M A0book α →
                τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) :
    Section2.CFOn M A0book (muColumn μ j0 - ξ) := by
  classical
  rcases h104a with
    ⟨h10, hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  rcases h10 with
    ⟨_hM, hType, hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hSource with ⟨_hApre, _hA0sub, hNotationSrc, _hDadeSrc⟩
  rcases hNotation with
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
    theorem_10_7_late_source_type_of_typeIIIIVVData hType
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

public theorem theorem_10_8_baseColumnMinusXi_supportedOn_A_of_hypothesis_10_4_a_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    Section1.supportedOn (muColumn μ j0 - ξ) A := by
  classical
  have hAll := h104a
  rcases h104a with ⟨h10, hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  rcases h10 with
    ⟨_hM, _hType, hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hNotation with
    ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, h45, _h48,
      _hTauA0, hFull⟩
  rcases h45 with ⟨xChar, h45a, _h45b⟩
  have hDerivedSub :
      ((derivedSubgroup M : Subgroup M) : Set M) \ {1} ⊆ A :=
    theorem_10_8_derived_nonidentity_subset_A_of_hypothesis_10_4_a_supported_data
      hAll
  have hμ0Derived :
      Section1.supportedOn (muColumn μ j0) ((derivedSubgroup M : Subgroup M) : Set M) := by
    have hμ0_eq :
        muColumn μ j0 =
          Section1.inducedCF (derivedSubgroup M) (xChar j0) := by
      simpa [muColumn, Section4Scratch.piColumn] using (h45a.2.2 j0).symm
    rw [hμ0_eq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) (xChar j0)
  have hξDerived :
      Section1.supportedOn ξ ((derivedSubgroup M : Subgroup M) : Set M) := by
    rcases (hS ξ).mp hξS with ⟨θ, _hθirr, _hθne, hξeq⟩
    rw [hξeq]
    exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ
  have hμ0_one : muColumn μ j0 1 = (Nat.card W1 : ℂ) := by
    have hbase : ∀ i, Section1.degree (μ i j0) = 1 := by
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
    have hI : Nat.card I = Nat.card W1 := by
      calc
        Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
        _ = Nat.card (W1.subgroupOf M) := hω.card_left
        _ = Nat.card W1 :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1M).toEquiv
    have hIcard : (Fintype.card I : ℂ) = (Nat.card W1 : ℂ) := by
      exact_mod_cast (by
        simpa [Nat.card_eq_fintype_card] using hI :
          Fintype.card I = Nat.card W1)
    calc
      muColumn μ j0 1 = ∑ i : I, μ i j0 1 := by simp [muColumn]
      _ = ∑ _i : I, (1 : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simpa [Section1.degree] using hbase i
      _ = (Nat.card W1 : ℂ) := by simp [hIcard]
  have hξ_one : ξ 1 = (Nat.card W1 : ℂ) := by
    simpa [Section1.degree] using hξDegree
  rw [Section1.supportedOn_iff]
  intro x hxA
  by_cases hx1 : x = 1
  · subst x
    simp [Pi.sub_apply, hμ0_one, hξ_one]
  · have hxNotDerived : x ∉ ((derivedSubgroup M : Subgroup M) : Set M) := by
      intro hxDerived
      exact hxA (hDerivedSub ⟨hxDerived, by simpa using hx1⟩)
    have hμ0_zero : muColumn μ j0 x = 0 :=
      (Section1.supportedOn_iff.mp hμ0Derived) x hxNotDerived
    have hξ_zero : ξ x = 0 :=
      (Section1.supportedOn_iff.mp hξDerived) x hxNotDerived
    simp [Pi.sub_apply, hμ0_zero, hξ_zero]

public theorem theorem_10_8_late_source_type_of_typeIIIIVVData
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    (hType : typeIIIIVVData M MF W1 W2 V) :
    Section8.typeIIIDefinitionData M MF ∨
      Section8.typeIVDefinitionData M MF ∨
        Section8.typeVDefinitionData M MF := by
  rcases hType with ⟨_hVeq, U, hP, hCases⟩
  rcases hCases with hIII | hIV | hV
  · exact Or.inl
      ⟨U, W1, W2, hP, hIII.1, hIII.2.1, hIII.2.2⟩
  · exact Or.inr (Or.inl
      ⟨U, W1, W2, hP, hIV.1, hIV.2.1, hIV.2.2⟩)
  · exact Or.inr (Or.inr
      ⟨U, W1, W2, hP, hV.1, hV.2⟩)


public theorem theorem_10_8_A_eq_late_of_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    A = Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
      (ambientDerivedSubgroup M) := by
  have hMs_eq :
      Ms = ambientDerivedSubgroup M :=
    Section8.msChoiceSource_eq_ambientDerived_of_late hNotation.2.2.1 hTail
  have hNot :=
    section10_source_not_typeI_typeII_of_msChoice_tail hNotation.2.2.1 hTail
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hBranch⟩
  rcases hBranch with hI | hP
  · exact False.elim (hNot.1 hI.1)
  · rcases hP with ⟨_U, _W1, _W2, _hP, _hType, hA, _hA0, _hLateImp⟩
    simpa [hMs_eq] using hA


public theorem theorem_10_8_dadeSupport_subset_tildeA_of_notation_8_14_and_H_le
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {Abook A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {H R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R)
    (hAbookA : Abook ⊆ A)
    (hHle : ∀ a : G, a ∈ Abook → H a ≤ R a) :
    Section2.dadeSupport Abook H ⊆ tildeA := by
  intro g hg
  rcases hg with ⟨a, ha, h, hh, hconj⟩
  exact theorem_10_8_dadeSupport_subset_tildeA_of_notation_8_14_source_data h14
    ⟨a, hAbookA ha, h, hHle a ha hh, hconj⟩

public theorem theorem_10_8_A_subset_A0_of_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1) :
    A ⊆ A0 := by
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hBranch⟩
  rcases hBranch with hI | hP
  · rcases hI with ⟨_hTypeI, _hA, hA0⟩
    intro x hx
    simpa [hA0] using hx
  · rcases hP with ⟨_U, _W1, _W2, _hP, _hType, _hA, hA0, _hLateImp⟩
    intro x hx
    rw [hA0]
    exact Or.inl hx

public theorem theorem_10_8_A1_subset_A_of_late_notation_8_10_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF) :
    A1 ⊆ A := by
  have hNot :=
    section10_source_not_typeI_typeII_of_msChoice_tail hNotation.2.2.1 hTail
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hBranch⟩
  rcases hBranch with hI | hP
  · exact False.elim (hNot.1 hI.1)
  · rcases hP with ⟨_U, _W1, _W2, _hP, _hType, _hA, _hA0, hLate⟩
    have hAeq : A = A1 := (hLate hTail).2
    intro x hx
    simpa [hAeq] using hx


public theorem theorem_10_8_hypothesis2_complement_le_bot_of_centralizer_le
    {G : Type u}
    [Group G]
    [Finite G]
    {A : Set G}
    {M : Subgroup G}
    {H : G → Subgroup G}
    (hA0M : Section2.Hypothesis2 A M H)
    {a : G}
    (ha : a ∈ A)
    (hCentM : Subgroup.centralizer ({a} : Set G) ≤ M) :
    H a ≤ ⊥ := by
  intro h hh
  have hprod := hA0M.centralizer_eq_product ha
  have hhCent : h ∈ Section2.elementCentralizer a := hprod.left_le hh
  have hhM : h ∈ M := hCentM (by
    simpa [Section2.elementCentralizer] using hhCent)
  have hhCentIn : h ∈ Section2.centralizerIn M a := by
    exact ⟨hhM, hhCent⟩
  have hInf : h ∈ H a ⊓ Section2.centralizerIn M a := ⟨hh, hhCentIn⟩
  simpa [hprod.inf_eq_bot] using hInf


public theorem theorem_10_8_section12ComplementIn_isComplement'_subgroupOf_right
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    (L.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hKM, hLM, hsup, hdisj⟩
  have hsup_local : L.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    calc
      L.subgroupOf M ⊔ K.subgroupOf M = (L ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := M) hLM hKM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf M) (K.subgroupOf M)).symm

public theorem theorem_10_8_section12ComplementIn_left_relIndex_eq_card_right
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    K.relIndex M = Nat.card L := by
  have hcompLocal : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    theorem_10_8_section12ComplementIn_isComplement'_subgroupOf_right hcomp
  calc
    K.relIndex M = (K.subgroupOf M).index := rfl
    _ = Nat.card (L.subgroupOf M) := hcompLocal.index_eq_card
    _ = Nat.card L :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := L) (K := M) hcomp.2.1).toEquiv

public theorem theorem_10_8_section12ComplementIn_left_isHall_of_coprime
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card L)) :
    IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf M) := by
  classical
  have hcompLocal : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    theorem_10_8_section12ComplementIn_isComplement'_subgroupOf_right hcomp
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet K)
    (H := K.subgroupOf M) ?_ ?_
  · intro p hpK
    have hcardK : Nat.card (K.subgroupOf M) = Nat.card K :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hcomp.1).toEquiv
    rw [hcardK] at hpK
    exact hpK
  · intro p hpK hpidxK
    have hpLcardSub : p.val ∣ Nat.card (L.subgroupOf M) := by
      simpa [hcompLocal.index_eq_card] using hpidxK
    have hpLcard : p.val ∣ Nat.card L := by
      have hcardL : Fintype.card (L.subgroupOf M) = Fintype.card L := by
        simpa [Nat.card_eq_fintype_card] using
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := L) (K := M) hcomp.2.1).toEquiv
      simpa [Nat.card_eq_fintype_card, hcardL] using hpLcardSub
    exact (p.property.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hpK) hpLcard


public theorem theorem_10_8_internalSemidirectProduct_left_isHall_of_coprime
    {G : Type u}
    [Group G]
    [Finite G]
    {C H K : Subgroup G}
    (hprod : Section2.IsInternalSemidirectProduct C H K)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf C) := by
  classical
  refine isHallSubgroup_of (G := C) (π := subgroupPrimeSet H)
    (H := H.subgroupOf C) ?_ ?_
  · intro p hpH
    have hcardH : Nat.card (H.subgroupOf C) = Nat.card H :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := H) (K := C) hprod.left_le).toEquiv
    rw [hcardH] at hpH
    exact hpH
  · intro p hpH hpidxH
    have hidx : (H.subgroupOf C).index = Nat.card K := by
      simpa [Subgroup.relIndex] using
        Section2.internalSemidirectProduct_left_relIndex_eq_card_right hprod
    have hpK : p.val ∣ Nat.card K := by
      simpa [hidx] using hpidxH
    exact (p.property.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hpH) hpK

public theorem theorem_10_8_left_le_left_of_common_coprime_complement
    {G : Type u}
    [Group G]
    [Finite G]
    {C H F K : Subgroup G}
    (hHprod : Section2.IsInternalSemidirectProduct C H K)
    (hFsemi : Section8.section8SemidirectProductIn C F K)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K)) :
    H ≤ F := by
  classical
  rcases hFsemi with ⟨hFcomp, _hFleC, hFnormal⟩
  have hHrel : H.relIndex C = Nat.card K :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hHprod
  let _ : (F.subgroupOf C).Normal := hFnormal
  have hFrel : F.relIndex C = Nat.card K :=
    theorem_10_8_section12ComplementIn_left_relIndex_eq_card_right hFcomp
  have hHmul :
      Nat.card K * Nat.card H = Nat.card C := by
    have hlag :=
      relIndex_mul_card_eq_card_of_le (H := C) (H' := H) hHprod.left_le
    simpa [hHrel] using hlag
  have hFmul :
      Nat.card K * Nat.card F = Nat.card C := by
    have hlag :=
      relIndex_mul_card_eq_card_of_le (H := C) (H' := F) hFcomp.1
    simpa [hFrel] using hlag
  have hcardHF : Nat.card H = Nat.card F :=
    Nat.mul_left_cancel (Nat.card_pos (α := K)) (hHmul.trans hFmul.symm)
  have hcardHFF : Fintype.card H = Fintype.card F := by
    simpa [Nat.card_eq_fintype_card] using hcardHF
  have hcopF : Nat.Coprime (Nat.card F) (Nat.card K) := by
    simpa [Nat.card_eq_fintype_card, ← hcardHFF] using hcop
  have hHallH :
      IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf C) :=
    theorem_10_8_internalSemidirectProduct_left_isHall_of_coprime hHprod hcop
  have hPrimeSet : subgroupPrimeSet H = subgroupPrimeSet F := by
    ext p
    simp [subgroupPrimeSet, hcardHFF]
  have hHallH' :
      IsHallSubgroup (subgroupPrimeSet F) (H.subgroupOf C) := by
    simpa [hPrimeSet] using hHallH
  have hHallF :
      IsHallSubgroup (subgroupPrimeSet F) (F.subgroupOf C) :=
    theorem_10_8_section12ComplementIn_left_isHall_of_coprime hFcomp hcopF
  have hHleFSub : H.subgroupOf C ≤ F.subgroupOf C :=
    IsHallSubgroup.le_of_normal hHallF hHallH'
  intro x hx
  have hxSub : (⟨x, hHprod.left_le hx⟩ : C) ∈ H.subgroupOf C := hx
  exact hHleFSub hxSub


public theorem theorem_10_8_A_subset_A_of_late_notation_8_10_source_data_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 MsBook MsTilde : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {Abook A0book A1book Atilde A0tilde A1tilde : Set G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hBook :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book A1book)
    (hTilde :
      Section8.notation_8_10_source_data M MF MsTilde Atilde A0tilde A1tilde) :
    Abook ⊆ Atilde := by
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  have hTail := theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hBookEq :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data hBook hTail
  have hTildeEq :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data hTilde hTail
  intro x hx
  simpa [hTildeEq] using (by simpa [hBookEq] using hx)

public theorem theorem_10_8_selectedDadeSupport_subset_tildeA_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 MsBook : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    {tildeA Abook A0book A1book : Set G}
    (hBook :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book A1book)
    (hTilde : section10TildeAData M MF tildeA)
    {H_A0 : G → Subgroup G}
    (hA0M : Section2.Hypothesis2 A0book M H_A0) :
    Section2.dadeSupport Abook H_A0 ⊆ tildeA := by
  rcases hTilde with
    ⟨MsTilde, Atilde, A0tilde, A1tilde, D, tildeA0, tildeA1, R,
      hTildeNotation, h14⟩
  have hAbookA0book : Abook ⊆ A0book :=
    theorem_10_8_A_subset_A0_of_notation_8_10_source_data hBook
  have hAbookAtilde : Abook ⊆ Atilde :=
    theorem_10_8_A_subset_A_of_late_notation_8_10_source_data_supported
      h10 hBook hTildeNotation
  have h14Data := h14
  rcases h14 with
    ⟨_hA1A, hAtildeA0tilde, hD, hRbot, _hUnique, hReq, _htildeA,
      _htildeA0, _htildeA1⟩
  have hHle : ∀ a : G, a ∈ Abook → H_A0 a ≤ R a := by
    intro a ha h hh
    have haA0tilde : a ∈ A0tilde := hAtildeA0tilde (hAbookAtilde ha)
    by_cases hCentM : Subgroup.centralizer ({a} : Set G) ≤ M
    · have hHbot : H_A0 a ≤ ⊥ :=
        theorem_10_8_hypothesis2_complement_le_bot_of_centralizer_le
          hA0M (hAbookA0book ha) hCentM
      have haNotD : a ∉ D := by
        intro haD
        have haD' : a ∈ Section8.section8DSet M A0tilde := by
          simpa [hD] using haD
        exact haD'.2 hCentM
      have hR : R a = ⊥ := hRbot a ⟨haA0tilde, haNotD⟩
      rw [hR]
      exact hHbot hh
    · have haD : a ∈ D :=
        by
          rw [hD]
          exact ⟨hAtildeA0tilde (hAbookAtilde ha), hCentM⟩
      rcases Section8.theorem_8_15_support_of_mem_D
          (G := G) (M := M) (MF := MF) (Ms := MsTilde)
          (A := Atilde) (A0 := A0tilde) (A1 := A1tilde)
          (D := D) (tildeA := tildeA) (tildeA0 := tildeA0)
          (tildeA1 := tildeA1) (R := R)
          (hG := inferInstance) hTildeNotation h14Data haD with
        ⟨L, LF, hSupp, _hReq⟩
      rcases hSupp with
        ⟨_hLmax, hLF, hSet, _hSemiL, hSemiC, _hCoprime, _hType⟩
      have hHprod :
          Section2.IsInternalSemidirectProduct (Section2.elementCentralizer a)
            (H_A0 a) (Section2.centralizerIn M a) :=
        hA0M.centralizer_eq_product (hAbookA0book ha)
      have hSemiC' :
          Section8.section8SemidirectProductIn (Section2.elementCentralizer a)
            (elementCentralizerIn LF a) (Section2.centralizerIn M a) := by
        simpa [Section2.elementCentralizer, Section2.centralizerIn,
          elementCentralizerIn] using hSemiC
      have hHleCentLF : H_A0 a ≤ elementCentralizerIn LF a :=
        theorem_10_8_left_le_left_of_common_coprime_complement hHprod hSemiC'
          (hA0M.coprime_orders (hAbookA0book ha) (hAbookA0book ha))
      have hR : R a = elementCentralizerIn LF a :=
        hReq a haD L LF hSet hLF
      rw [hR]
      exact hHleCentLF hh
  exact theorem_10_8_dadeSupport_subset_tildeA_of_notation_8_14_and_H_le
    h14Data hAbookAtilde hHle

public theorem theorem_10_8_selectedDadeComplement_le_tildeR_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 MsBook MsTilde : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    {Abook A0book A1book Atilde A0tilde A1tilde D tildeA tildeA0 tildeA1 : Set G}
    (hBook :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book A1book)
    (hTilde :
      Section8.notation_8_10_source_data M MF MsTilde Atilde A0tilde A1tilde)
    {H_A0 R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M Atilde A0tilde A1tilde
        D tildeA tildeA0 tildeA1 R)
    (hA0M : Section2.Hypothesis2 A0book M H_A0) :
    ∀ a : G, a ∈ Abook → H_A0 a ≤ R a := by
  have hAbookA0book : Abook ⊆ A0book :=
    theorem_10_8_A_subset_A0_of_notation_8_10_source_data hBook
  have hAbookAtilde : Abook ⊆ Atilde :=
    theorem_10_8_A_subset_A_of_late_notation_8_10_source_data_supported
      h10 hBook hTilde
  have h14Data := h14
  rcases h14 with
    ⟨_hA1A, hAtildeA0tilde, hD, hRbot, _hUnique, hReq, _htildeA,
      _htildeA0, _htildeA1⟩
  intro a ha h hh
  have haA0tilde : a ∈ A0tilde := hAtildeA0tilde (hAbookAtilde ha)
  by_cases hCentM : Subgroup.centralizer ({a} : Set G) ≤ M
  · have hHbot : H_A0 a ≤ ⊥ :=
      theorem_10_8_hypothesis2_complement_le_bot_of_centralizer_le
        hA0M (hAbookA0book ha) hCentM
    have haNotD : a ∉ D := by
      intro haD
      have haD' : a ∈ Section8.section8DSet M A0tilde := by
        simpa [hD] using haD
      exact haD'.2 hCentM
    have hR : R a = ⊥ := hRbot a ⟨haA0tilde, haNotD⟩
    rw [hR]
    exact hHbot hh
  · have haD : a ∈ D := by
      rw [hD]
      exact ⟨hAtildeA0tilde (hAbookAtilde ha), hCentM⟩
    rcases Section8.theorem_8_15_support_of_mem_D
        (G := G) (M := M) (MF := MF) (Ms := MsTilde)
        (A := Atilde) (A0 := A0tilde) (A1 := A1tilde)
        (D := D) (tildeA := tildeA) (tildeA0 := tildeA0)
        (tildeA1 := tildeA1) (R := R)
        (hG := inferInstance) hTilde h14Data haD with
      ⟨L, LF, hSupp, _hReq⟩
    rcases hSupp with
      ⟨_hLmax, hLF, hSet, _hSemiL, hSemiC, _hCoprime, _hType⟩
    have hHprod :
        Section2.IsInternalSemidirectProduct (Section2.elementCentralizer a)
          (H_A0 a) (Section2.centralizerIn M a) :=
      hA0M.centralizer_eq_product (hAbookA0book ha)
    have hSemiC' :
        Section8.section8SemidirectProductIn (Section2.elementCentralizer a)
          (elementCentralizerIn LF a) (Section2.centralizerIn M a) := by
      simpa [Section2.elementCentralizer, Section2.centralizerIn,
        elementCentralizerIn] using hSemiC
    have hHleCentLF : H_A0 a ≤ elementCentralizerIn LF a :=
      theorem_10_8_left_le_left_of_common_coprime_complement hHprod hSemiC'
        (hA0M.coprime_orders (hAbookA0book ha) (hAbookA0book ha))
    have hR : R a = elementCentralizerIn LF a :=
      hReq a haD L LF hSet hLF
    rw [hR]
    exact hHleCentLF hh


public theorem theorem_10_8_baseColumnMinusXi_dadeSupportControl_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ)
    {tildeA : Set G}
    (hTilde : section10TildeAData M MF tildeA) :
    ∃ Abook A0book : Set G,
      ∃ H_A0 : G → Subgroup G,
        ∃ hA0M : Section2.Hypothesis2 A0book M H_A0,
          (∀ α : Section1.ClassFunction M,
            Section2.CFOn M A0book α →
              τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) ∧
            Section2.CFOn M A0book (muColumn μ j0 - ξ) ∧
              Section1.supportedOn (muColumn μ j0 - ξ)
                (Section8.section8SubgroupSetPreimage M Abook) ∧
                Section2.dadeSupport Abook H_A0 ⊆ tildeA := by
  have hAll := h104a
  rcases h104a with
    ⟨h10, hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  rcases hNotation with
    ⟨_MFsrc, _Ms, Abook, A0book, _A1book, hSource,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
        _hTauA0, _hFull⟩
  rcases hSource with ⟨hApre, _hA0pre, h810, H_A0, hA0M, hτ⟩
  refine ⟨Abook, A0book, H_A0, hA0M, hτ, ?_, ?_, ?_⟩
  · exact theorem_10_8_baseColumnMinusXi_CFOn_A0book_of_supported
      hAll ⟨hApre, _hA0pre, h810, H_A0, hA0M, hτ⟩
  · have hsuppA :
        Section1.supportedOn (muColumn μ j0 - ξ) A :=
      theorem_10_8_baseColumnMinusXi_supportedOn_A_of_hypothesis_10_4_a_supported_data
        hAll
    simpa [hApre] using hsuppA
  · have hMFsrc_eq : _MFsrc = MF := by
      rcases h10 with
        ⟨_hM, hType, _hS, _hW1, _hW2, _hW12, _hDade, _h46base,
          _hNotation10, _h52⟩
      rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
      exact section16MFSubgroup_unique h810.2.1 hP.1
    have h810_outer :
        Section8.notation_8_10_source_data M MF _Ms Abook A0book _A1book := by
      simpa [hMFsrc_eq] using h810
    exact theorem_10_8_selectedDadeSupport_subset_tildeA_supported_source
      h10 h810_outer hTilde hA0M

public theorem theorem_10_8_tildeA_vanishing_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    section10TildeAVanishingData M MF τ ξ j0 μ := by
  intro tildeA hTilde g hg
  rcases theorem_10_8_baseColumnMinusXi_dadeSupportControl_supported_source
      h104a hTilde with
    ⟨Abook, A0book, H_A0, hA0M, hτ, hCFOn, hsupp, hsupport_tilde⟩
  have hgSupport : g ∉ Section2.dadeSupport Abook H_A0 := by
    intro hgSupport
    exact hg (hsupport_tilde hgSupport)
  calc
    τ (muColumn μ j0 - ξ) g =
        Section2.dadeTransform H_A0 hA0M.subset_L (muColumn μ j0 - ξ) g := by
          simpa using congrFun (hτ (muColumn μ j0 - ξ) hCFOn) g
    _ = 0 :=
        theorem_10_8_dadeTransform_eq_zero_of_supportedOn_of_not_mem_dadeSupport
          hA0M.subset_L hsupp hgSupport


public theorem theorem_10_8_baseColumn_principal_of_hypothesis_10_4_a_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    σ (ω i0 j0) = Section1.principalCharacter G := by
  rcases h104a with
    ⟨_h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  rcases hNotation with
    ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46, hω, _hIso, _hVirt, hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  simpa [hω.principal] using hPrin

public theorem exists_exactCharacterValueOrder_dvd_of_characterValueOrder
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} {b : ℕ}
    (hb : Section3.characterValueOrder χ b) :
    ∃ a : ℕ, a ∣ b ∧ Section3.exactCharacterValueOrder χ a := by
  classical
  let := Fintype.ofFinite G
  let a : ℕ := (Finset.univ : Finset G).lcm (fun g => orderOf (χ g))
  have hadvd_b : a ∣ b := by
    dsimp [a]
    refine Finset.lcm_dvd ?_
    intro g _hg
    exact orderOf_dvd_of_pow_eq_one (hb.2 g)
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd_b hb.1
  refine ⟨a, hadvd_b, ?_⟩
  constructor
  · constructor
    · exact hapos
    · intro g
      have hdiv : orderOf (χ g) ∣ a := by
        dsimp [a]
        exact Finset.dvd_lcm (Finset.mem_univ g)
      exact (orderOf_dvd_iff_pow_eq_one).1 hdiv
  · intro c hc
    dsimp [a]
    refine Finset.lcm_dvd ?_
    intro g _hg
    exact orderOf_dvd_of_pow_eq_one (hc.2 g)

public theorem internalDirectProduct_left_subgroupOf_normal
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    (H.subgroupOf C).Normal := by
  refine ⟨?_⟩
  intro y hyH x
  rcases h.mul_surjective (x : G) x.2 with ⟨h0, hh0, k0, hk0, hx⟩
  have hcomm : k0 * (y : G) = (y : G) * k0 := by
    exact (h.commute (y : G) hyH k0 hk0).symm
  change ((x : G) * (y : G) * (x : G)⁻¹) ∈ H
  rw [hx]
  have hmid : k0 * (y : G) * k0⁻¹ = (y : G) := by
    calc
      k0 * (y : G) * k0⁻¹ = (y : G) * k0 * k0⁻¹ := by
        rw [hcomm]
      _ = (y : G) := by simp [mul_assoc]
  have hcalc : h0 * k0 * (y : G) * (h0 * k0)⁻¹ =
      h0 * (y : G) * h0⁻¹ := by
    calc
      h0 * k0 * (y : G) * (h0 * k0)⁻¹ =
          h0 * (k0 * (y : G) * k0⁻¹) * h0⁻¹ := by
            simp [mul_assoc]
      _ = h0 * (y : G) * h0⁻¹ := by rw [hmid]
  rw [hcalc]
  exact H.mul_mem (H.mul_mem hh0 hyH) (H.inv_mem hh0)

public theorem internalDirectProduct_right_subgroupOf_normal
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    (K.subgroupOf C).Normal :=
  internalDirectProduct_left_subgroupOf_normal (Section3.internalDirectProduct_swap h)

public theorem internalDirectProduct_left_relIndex_eq_card_right
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    H.relIndex C = Nat.card K := by
  let hsemi : Section2.IsInternalSemidirectProduct C H K :=
    { left_le := h.left_le
      right_le := h.right_le
      right_normalizes_left := by
        intro k hk h0 hh0
        change k * h0 * k⁻¹ ∈ H
        have hcomm : k * h0 = h0 * k := (h.commute h0 hh0 k hk).symm
        rw [hcomm]
        simpa [mul_assoc] using hh0
      inf_eq_bot := h.inf_eq_bot
      mul_surjective := h.mul_surjective }
  exact Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi

public theorem quotientCharacterInflation_pow_natCard
    {G : Type u} [Group G] [Finite G]
    (H T : Subgroup G) [(H.subgroupOf T).Normal]
    (χ : T ⧸ H.subgroupOf T →* ℂˣ) (t : T) :
    (Section1.quotientCharacterInflation H T χ t) ^
      Nat.card (T ⧸ H.subgroupOf T) = 1 := by
  let q : T ⧸ H.subgroupOf T := t
  have hqpow : q ^ Nat.card (T ⧸ H.subgroupOf T) = 1 := by
    exact pow_card_eq_one' (x := q)
  have hpow : χ q ^ Nat.card (T ⧸ H.subgroupOf T) = 1 := by
    calc
      χ q ^ Nat.card (T ⧸ H.subgroupOf T) =
          χ (q ^ Nat.card (T ⧸ H.subgroupOf T)) := by
            rw [MonoidHom.map_pow]
      _ = 1 := by rw [hqpow, map_one]
  change ((χ q : ℂˣ) : ℂ) ^ Nat.card (T ⧸ H.subgroupOf T) = 1
  simpa using congrArg (fun z : ℂˣ => (z : ℂ)) hpow

public theorem characterValueOrder_of_leftKernel_internalDirectProduct
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (hIP : Section2.IsInternalDirectProduct W W1 W2)
    {θ : Section1.ClassFunction W}
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθker : Section1.subgroupInKernel' θ (W2.subgroupOf W))
    (hθdeg : Section1.degree θ = 1) :
    Section3.characterValueOrder θ (Nat.card W1) := by
  classical
  have _ : (W2.subgroupOf W).Normal :=
    internalDirectProduct_right_subgroupOf_normal hIP
  rcases Section1.exists_quotientLinearCharacter_of_irreducible_degree_one_kernel
      W2 W hθirr hθker hθdeg with ⟨χ, hθ⟩
  have hidx : (W2.subgroupOf W).index = Nat.card W1 := by
    have hrel := internalDirectProduct_left_relIndex_eq_card_right
      (Section3.internalDirectProduct_swap hIP)
    simpa [Subgroup.relIndex] using hrel
  have hcardQ : Nat.card (W ⧸ W2.subgroupOf W) = Nat.card W1 := by
    simpa [Subgroup.index_eq_card] using hidx
  have hcardQF : Fintype.card (W ⧸ W2.subgroupOf W) = Fintype.card W1 := by
    simpa [Nat.card_eq_fintype_card] using hcardQ
  constructor
  · exact Nat.card_pos (α := W1)
  · intro w
    rw [hθ]
    simpa [Nat.card_eq_fintype_card, hcardQF] using
      quotientCharacterInflation_pow_natCard W2 W χ w


public theorem theorem_10_8_baseColumnValueOrder_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∀ i : I, i ≠ i0 →
      Section3.characterValueOrder (ω i j0) (Nat.card W1) := by
  rcases h104a with
    ⟨h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  rcases h10 with
    ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases hNotation with
    ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  rcases h46 with
    ⟨h42, _hHnormal, _hW2leH, _hHleK, _hCent, _hA⟩
  rcases h42 with
    ⟨_hsemi, _hHall, _hW1cyc, _hW1nontriv, _hW2cyc, _hW2nontriv,
      _hcentralizer, _hW1leW, _hW2leW, hIP, _hWodd⟩
  have hcardW1Sub :
      Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1M).toEquiv
  have hcardW1SubF :
      Fintype.card (W1.subgroupOf M) = Fintype.card W1 := by
    simpa [Nat.card_eq_fintype_card] using hcardW1Sub
  intro i _hi
  have horderSub :
      Section3.characterValueOrder (ω i j0) (Nat.card (W1.subgroupOf M)) :=
    characterValueOrder_of_leftKernel_internalDirectProduct
      (W1 := W1.subgroupOf M)
      (W2 := W2.subgroupOf M)
      (W := W)
      hIP
      (hω.irreducible i j0)
      (hω.left_kernel i)
      (hω.degree_one i j0)
  constructor
  · simpa [Nat.card_eq_fintype_card, ← hcardW1SubF] using horderSub.1
  · intro w
    simpa [Nat.card_eq_fintype_card, hcardW1SubF] using horderSub.2 w


public theorem theorem_10_8_baseColumnExactValueOrder_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∀ i : I, i ≠ i0 →
      ∃ a : ℕ, a ∣ Nat.card W1 ∧
        Section3.exactCharacterValueOrder (ω i j0) a := by
  intro i hi
  exact exists_exactCharacterValueOrder_dvd_of_characterValueOrder
    (theorem_10_8_baseColumnValueOrder_supported_source h104a i hi)


public theorem theorem_10_8_ambientRelativePF39_baseColumnBridge_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    (∀ i : I, i ≠ i0 →
      ∀ {a : ℕ},
        Section3.exactCharacterValueOrder (ω i j0) a →
          ∀ g : G, (orderOf g).Coprime a →
            ∃ z : ℤ, σ (ω i j0) g = (z : ℂ)) ∧
    (∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
      ∀ c : I → I,
        (∀ i : I, Section1.conjugateCharacter (ω i j0) = ω (c i) j0) →
          ∀ i : I, i ≠ i0 →
            σ (ω (c i) j0) g = σ (ω i j0) g) := by
  rcases h104a with
    ⟨h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  have hLocal :
      ambientRelativePF39BaseColumnData
        (Nat.card (W1.subgroupOf M)) W i0 j0 ω σ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData
        hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
        hRest⟩
    rcases hRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hTauIso, _hTauPunct, _hTauVirt, hAmbientPF39,
        _hAmbientPF39BaseRow⟩
    simpa [ambientRelativePF39BaseColumnData,
      Section4Scratch.ambientRelativePF39BaseColumnData] using hAmbientPF39
  constructor
  · exact hLocal.1
  · intro g hcop c hconj i hi
    rcases h10 with
      ⟨_hM, _hType, _hS, hW1M, _hW2M, _hW12M, _hDade, _h46base,
        _hNotation10, _h52⟩
    have hcardW1 :
        Nat.card (W1.subgroupOf M) = Nat.card W1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
    have hcardW1F :
        Fintype.card (W1.subgroupOf M) = Fintype.card W1 := by
      simpa [Nat.card_eq_fintype_card] using hcardW1
    exact hLocal.2 g
      (by simpa [Nat.card_eq_fintype_card, hcardW1F] using hcop) c hconj i hi


public theorem theorem_10_8_baseColumnIntegralValues_of_pf39_c
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {W : Subgroup M}
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (horder :
      ∀ i : I, i ≠ i0 →
        ∃ a : ℕ, a ∣ Nat.card W1 ∧
          Section3.exactCharacterValueOrder (ω i j0) a)
    (h39c :
      ∀ i : I, i ≠ i0 →
        ∀ {a : ℕ},
          Section3.exactCharacterValueOrder (ω i j0) a →
            ∀ g : G, (orderOf g).Coprime a →
              ∃ z : ℤ, σ (ω i j0) g = (z : ℂ)) :
    ∀ i : I, i ≠ i0 →
      ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∃ z : ℤ, σ (ω i j0) g = (z : ℂ) := by
  intro i hi g hcop
  rcases horder i hi with ⟨a, hadvd, ha⟩
  exact h39c i hi ha g (hcop.coprime_dvd_right hadvd)


public theorem int_sum_even_of_fixedPointFree_involution
    {I : Type*} [DecidableEq I]
    (s : Finset I) (zVal : I → ℤ) (c : I → I)
    (hmem : ∀ i, i ∈ s → c i ∈ s)
    (hinv : ∀ i, i ∈ s → c (c i) = i)
    (hneq : ∀ i, i ∈ s → c i ≠ i)
    (hz : ∀ i, i ∈ s → zVal (c i) = zVal i) :
    ∃ z : ℤ, s.sum zVal = 2 * z := by
  classical
  have hsumMod : ((s.sum zVal : ℤ) : ZMod 2) = 0 := by
    have hcast : ((s.sum zVal : ℤ) : ZMod 2) =
        ∑ x ∈ s, ((zVal x : ℤ) : ZMod 2) := by
      simp
    rw [hcast]
    rw [← Finset.sum_attach]
    have hzero :
        (∑ x : {x // x ∈ s}, ((zVal x : ℤ) : ZMod 2)) = 0 := by
      refine Finset.sum_involution
        (s := Finset.univ)
        (f := fun x : {x // x ∈ s} => ((zVal x : ℤ) : ZMod 2))
        (g := fun x _ => ⟨c x, hmem x x.2⟩) ?_ ?_ ?_ ?_
      · intro x _
        change ((zVal (x : I) : ℤ) : ZMod 2) +
            ((zVal (c (x : I)) : ℤ) : ZMod 2) = 0
        rw [hz x x.2]
        exact CharTwo.add_self_eq_zero _
      · intro x _ _ hfix
        exact hneq x x.2 (congrArg Subtype.val hfix)
      · intro x _
        simp
      · intro x _
        ext
        exact hinv x x.2
    simpa using hzero
  have hEven : Even (s.sum zVal : ℤ) :=
    (ZMod.intCast_eq_zero_iff_even).1 hsumMod
  rcases hEven with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  omega

public theorem theorem_10_8_baseColumnIntegerPairingEven_of_conjugate_pairing
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {W : Subgroup M}
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hpair :
      ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∃ c : I → I,
          (∀ i : I, i ≠ i0 → c i ≠ i0) ∧
          (∀ i : I, i ≠ i0 → c (c i) = i) ∧
          (∀ i : I, i ≠ i0 → c i ≠ i) ∧
          (∀ i : I, i ≠ i0 → σ (ω (c i) j0) g = σ (ω i j0) g)) :
    ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
      ∀ zVal : I → ℤ,
        (∀ i : I, i ≠ i0 → σ (ω i j0) g = (zVal i : ℂ)) →
          ∃ z : ℤ, (Finset.univ.erase i0 : Finset I).sum zVal = 2 * z := by
  intro g hcop zVal hvalues
  rcases hpair g hcop with ⟨c, hnonbase, hinv, hneq, hsame⟩
  refine int_sum_even_of_fixedPointFree_involution
    (Finset.univ.erase i0) zVal c ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_erase.mpr
      ⟨hnonbase i (Finset.mem_erase.mp hi).1, Finset.mem_univ _⟩
  · intro i hi
    exact hinv i (Finset.mem_erase.mp hi).1
  · intro i hi
    exact hneq i (Finset.mem_erase.mp hi).1
  · intro i hi
    have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
    have hci0 : c i ≠ i0 := hnonbase i hi0
    have hleft := hvalues (c i) hci0
    have hright := hvalues i hi0
    have hσ := hsame i hi0
    have hcast : (zVal (c i) : ℂ) = (zVal i : ℂ) := by
      rw [← hleft, hσ, hright]
    exact_mod_cast hcast

public theorem theorem_10_8_conjugate_omega_baseColumn_eq
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (i : I) :
    ∃ i', Section1.conjugateCharacter (ω i j0) = ω i' j0 := by
  have hbarIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.conjugateCharacter (ω i j0)) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter (hω.irreducible i j0)
  have hbarKer :
      Section1.subgroupInKernel' (Section1.conjugateCharacter (ω i j0))
        (W2.subgroupOf W) := by
    intro x
    have hx := hω.left_kernel i x
    have hx' := congrArg star hx
    simpa [Section1.conjugateCharacter, Section1.degree] using hx'
  exact (hω.left_kernel_exact _ hbarIrr).mp hbarKer

public theorem theorem_10_8_conjugate_omega_baseColumn_not_fixed
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    (h31 : Section3.hypothesis_3_1_statement W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    {i : I} (hi0 : i ≠ i0) :
    Section1.conjugateCharacter (ω i j0) ≠ ω i j0 := by
  intro hfix
  have hne_principal : ω i j0 ≠ Section1.principalCharacter W := by
    intro hEq
    exact hi0 ((hω.pairwise_eq (i := i) (i' := i0) (j := j0) (j' := j0)
      (by simpa [hω.principal] using hEq)).1)
  rcases h31 with ⟨_hW1, _hW2, _hDirect, _hcycW, hoddW, _hcard1, _hcard2, _hTI⟩
  rcases hω.irreducible i j0 with ⟨n, ρ, hρirr, hρchar⟩
  have hneChar : ρ.character ≠ Section1.principalCharacter W := by
    simpa [hρchar] using hne_principal
  exact Section1.proposition_1_1 hoddW ρ hρirr hneChar
    (by simpa [hρchar] using hfix.symm)


public theorem theorem_10_8_baseColumnConjugateIndex_of_hypothesis_10_4_a_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∃ c : I → I,
      (∀ i : I, Section1.conjugateCharacter (ω i j0) = ω (c i) j0) ∧
      (∀ i : I, i ≠ i0 → c i ≠ i0) ∧
      (∀ i : I, i ≠ i0 → c (c i) = i) ∧
      (∀ i : I, i ≠ i0 → c i ≠ i) := by
  classical
  rcases h104a with
    ⟨_h10, hNotation, _hξS, _hξIrr, _hξDegree, _hUniform⟩
  rcases hNotation with
    ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
        _hFull⟩
  rcases h46 with
    ⟨h42, _hHnormal, _hW2leH, _hHleK, _hCent, _hA⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h42).2
  let c : I → I := fun i =>
    Classical.choose (theorem_10_8_conjugate_omega_baseColumn_eq hω i)
  have hc :
      ∀ i : I, Section1.conjugateCharacter (ω i j0) = ω (c i) j0 := by
    intro i
    exact Classical.choose_spec (theorem_10_8_conjugate_omega_baseColumn_eq hω i)
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · intro i hi hci0
    have hprincipalBar :
        Section1.conjugateCharacter (ω i j0) = Section1.principalCharacter W := by
      simpa [hci0, hω.principal] using hc i
    have hprincipal :
        ω i j0 = Section1.principalCharacter W := by
      have hconj := congrArg Section1.conjugateCharacter hprincipalBar
      have hprincipalConj :
          Section1.conjugateCharacter (Section1.principalCharacter W) =
            Section1.principalCharacter W := by
        ext x
        simp [Section1.conjugateCharacter, Section1.principalCharacter]
      simpa [theorem_10_7_conjugateCharacter_involutive, hprincipalConj] using hconj
    exact hi ((hω.pairwise_eq (i := i) (i' := i0) (j := j0) (j' := j0)
      (by simpa [hω.principal] using hprincipal)).1)
  · intro i _hi
    have hcc :
        ω i j0 = ω (c (c i)) j0 := by
      calc
        ω i j0 =
            Section1.conjugateCharacter (Section1.conjugateCharacter (ω i j0)) := by
              rw [theorem_10_7_conjugateCharacter_involutive]
        _ = Section1.conjugateCharacter (ω (c i) j0) := by rw [hc i]
        _ = ω (c (c i)) j0 := hc (c i)
    exact (hω.pairwise_eq (i := i) (i' := c (c i)) (j := j0) (j' := j0) hcc).1.symm
  · intro i hi hci
    exact theorem_10_8_conjugate_omega_baseColumn_not_fixed h31 hω hi
      (by simpa [hci] using hc i)


public theorem theorem_10_8_baseColumnConjugatePairing_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
      ∃ c : I → I,
        (∀ i : I, i ≠ i0 → c i ≠ i0) ∧
        (∀ i : I, i ≠ i0 → c (c i) = i) ∧
        (∀ i : I, i ≠ i0 → c i ≠ i) ∧
        (∀ i : I, i ≠ i0 → σ (ω (c i) j0) g = σ (ω i j0) g) := by
  intro g hcop
  rcases theorem_10_8_baseColumnConjugateIndex_of_hypothesis_10_4_a_supported_data
      h104a with
    ⟨c, hconj, hnonbase, hinv, hneq⟩
  refine ⟨c, hnonbase, hinv, hneq, ?_⟩
  exact (theorem_10_8_ambientRelativePF39_baseColumnBridge_supported h104a).2 g hcop c hconj

public theorem theorem_10_8_baseColumnNonprincipalEven_of_integral_pairing
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    {W1 : Subgroup G}
    {M : Subgroup G}
    {W : Subgroup M}
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hintegral :
      ∀ i : I, i ≠ i0 →
        ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
          ∃ z : ℤ, σ (ω i j0) g = (z : ℂ))
    (hpair :
      ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∀ zVal : I → ℤ,
          (∀ i : I, i ≠ i0 → σ (ω i j0) g = (zVal i : ℂ)) →
            ∃ z : ℤ, (Finset.univ.erase i0 : Finset I).sum zVal = 2 * z) :
    ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
      ∃ z : ℤ,
        (Finset.univ.erase i0 : Finset I).sum (fun i => σ (ω i j0) g) =
          ((2 * z : ℤ) : ℂ) := by
  classical
  intro g hcop
  let witness : (i : I) → i ≠ i0 → ℤ :=
    fun i hi => Classical.choose (hintegral i hi g hcop)
  have witness_spec :
      ∀ (i : I) (hi : i ≠ i0), σ (ω i j0) g = (witness i hi : ℂ) := by
    intro i hi
    exact Classical.choose_spec (hintegral i hi g hcop)
  let zVal : I → ℤ := fun i =>
    if hi : i = i0 then 0 else witness i hi
  have hzVal :
      ∀ i : I, i ≠ i0 → σ (ω i j0) g = (zVal i : ℂ) := by
    intro i hi
    dsimp [zVal]
    rw [dif_neg hi]
    exact witness_spec i hi
  rcases hpair g hcop zVal hzVal with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  calc
    (Finset.univ.erase i0 : Finset I).sum (fun i => σ (ω i j0) g) =
        (Finset.univ.erase i0 : Finset I).sum (fun i => (zVal i : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
          exact hzVal i hne
    _ = (((Finset.univ.erase i0 : Finset I).sum zVal : ℤ) : ℂ) := by
          simp
    _ = ((2 * z : ℤ) : ℂ) := by
          rw [hz]


public theorem theorem_10_8_baseColumnParity_of_nonprincipal_even
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    {M : Subgroup G}
    {W1 : Subgroup G}
    {W : Subgroup M}
    {i0 : I}
    {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hprincipal : σ (ω i0 j0) = Section1.principalCharacter G)
    (heven :
      ∀ g : G, Nat.Coprime (orderOf g) (Nat.card W1) →
        ∃ z : ℤ,
          (Finset.univ.erase i0 : Finset I).sum (fun i => σ (ω i j0) g) =
            ((2 * z : ℤ) : ℂ)) :
    section10BaseColumnParityData W1 W i0 j0 ω σ := by
  intro g hcop
  rcases heven g hcop with ⟨z, hz⟩
  refine ⟨2 * z + 1, ?_, ?_⟩
  · have hsplit := Finset.sum_erase_add (Finset.univ : Finset I)
      (fun i => σ (ω i j0) g) (Finset.mem_univ i0)
    calc
      (∑ i : I, σ (ω i j0) g) =
          (Finset.univ.erase i0 : Finset I).sum (fun i => σ (ω i j0) g) +
            σ (ω i0 j0) g := by
            exact hsplit.symm
      _ = ((2 * z : ℤ) : ℂ) + 1 := by
            simp [hz, hprincipal, Section1.principalCharacter]
      _ = ((2 * z + 1 : ℤ) : ℂ) := by
            norm_num
  · exact ⟨z, by ring⟩


public theorem theorem_10_8_hypothesis_10_4_supported_of_coherence
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
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
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104a :
      hypothesis_10_4_a_supported_data M MF W1 W2 V W A A0 S τ ξ i0 j0
        μ δSign ω σ d n δ)
    (hcoh : Section6.coherentFamily S τ) :
    ∃ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G,
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ := by
  rcases exists_typeVCoherentSubfamilyData_of_coherentFamily (M := M) hcoh with
    ⟨τ₁, _hcoh', hExt⟩
  have htail :
      section10TildeAVanishingData M MF τ ξ j0 μ ∧
        section10BaseColumnParityData W1 W i0 j0 ω σ :=
    ⟨theorem_10_8_tildeA_vanishing_supported_source h104a,
      theorem_10_8_baseColumnParity_of_nonprincipal_even
        (theorem_10_8_baseColumn_principal_of_hypothesis_10_4_a_supported_data h104a)
        (theorem_10_8_baseColumnNonprincipalEven_of_integral_pairing
          (theorem_10_8_baseColumnIntegralValues_of_pf39_c
            (theorem_10_8_baseColumnExactValueOrder_supported_source h104a)
            ((theorem_10_8_ambientRelativePF39_baseColumnBridge_supported h104a).1))
          (theorem_10_8_baseColumnIntegerPairingEven_of_conjugate_pairing
            (theorem_10_8_baseColumnConjugatePairing_supported_source h104a)))⟩
  rcases htail with ⟨hvanish, hparity⟩
  have hOddM : Odd (Nat.card M) :=
    Odd.of_dvd_nat IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  exact ⟨τ₁, h104a, hcoh, hExt, hOddM, hvanish, hparity⟩


public theorem theorem_10_8_counting_cardinality_contradiction
    {w1 w2 m q r : ℕ}
    (hw2 : 0 < w2)
    (hm : m = q * r)
    (hq : 2 * w1 + 1 ≤ q)
    (hr : w2 ≤ r)
    (hlt : m < 2 * w1 * w2) :
    False := by
  have hstrict : 2 * w1 * w2 < (2 * w1 + 1) * w2 := by
    simpa [Nat.succ_eq_add_one, mul_assoc] using
      Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self (2 * w1)) hw2
  have hprod_le : (2 * w1 + 1) * w2 ≤ q * r :=
    Nat.mul_le_mul hq hr
  have hm_gt : 2 * w1 * w2 < m := by
    rw [hm]
    exact lt_of_lt_of_le hstrict hprod_le
  exact (not_lt_of_ge (le_of_lt hm_gt)) hlt

public theorem theorem_10_8_secondDerived_le_ambientDerived
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M := by
  simpa [section16SecondDerivedSubgroup] using
    (section12_ambientDerivedSubgroup_le (G := G) (E := ambientDerivedSubgroup M))

public theorem theorem_10_8_ambientDerived_card_eq_secondDerived_relIndex_mul_card
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    Nat.card (ambientDerivedSubgroup M) =
      (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) *
        Nat.card (section16SecondDerivedSubgroup M) := by
  have hle : section16SecondDerivedSubgroup M ≤ ambientDerivedSubgroup M :=
    theorem_10_8_secondDerived_le_ambientDerived M
  exact (relIndex_mul_card_eq_card_of_le
    (H := ambientDerivedSubgroup M) (H' := section16SecondDerivedSubgroup M) hle).symm


public theorem theorem_10_8_counting_secondDerivedQuotient_card_eq_relIndex
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G) :
    Nat.card (derivedSubgroup M ⧸
      ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)) =
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) := by
  have hrelM :
      ((section16SecondDerivedSubgroup M).subgroupOf M).relIndex (derivedSubgroup M) =
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) := by
    have hamb :
        ((section16SecondDerivedSubgroup M).subgroupOf M).relIndex
            ((ambientDerivedSubgroup M).subgroupOf M) =
          (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) := by
      exact Subgroup.relIndex_subgroupOf
        (H := section16SecondDerivedSubgroup M) (K := ambientDerivedSubgroup M) (L := M)
        (section12_ambientDerivedSubgroup_le (E := M))
    rw [section12_ambientDerivedSubgroup_subgroupOf_eq] at hamb
    exact hamb
  rw [← hrelM]
  simpa [Subgroup.relIndex] using
    (Subgroup.index_eq_card
      (H := ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
        (derivedSubgroup M))).symm


public theorem theorem_10_8_counting_quotient_lower_bound_of_factor
    {w k q : ℕ}
    (hw : 0 < w)
    (hk : w * k = q - 1)
    (h2 : 2 ≤ k) :
    2 * w + 1 ≤ q := by
  have hle : 2 * w ≤ q - 1 := by
    have hmul := Nat.mul_le_mul_left w h2
    rw [Nat.mul_comm w 2, hk] at hmul
    exact hmul
  omega


public theorem theorem_10_8_counting_secondDerived_card_lower_bound_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    Nat.card W2 ≤ Nat.card (section16SecondDerivedSubgroup M) := by
  rcases hypothesis_10_1_of_hypothesis_10_4_supported_data h104 with
    ⟨_hM, hType, _hFamily, _hW1M, hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
  have hW2SecondSub :
      W2.subgroupOf M ≤ (section16SecondDerivedSubgroup M).subgroupOf M :=
    typePDefinitionData_W2_subgroupOf_le_secondDerived_subgroupOf hP
  have hcardSub :
      Nat.card (W2.subgroupOf M) ≤
        Nat.card ((section16SecondDerivedSubgroup M).subgroupOf M) :=
    Subgroup.card_le_of_le hW2SecondSub
  have hSecondM : section16SecondDerivedSubgroup M ≤ M :=
    (theorem_10_8_secondDerived_le_ambientDerived M).trans
      (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hW2card : Nat.card (W2.subgroupOf M) = Nat.card W2 :=
    natCard_subgroupOf_eq W2 M hW2M
  have hSecondCard :
      Nat.card ((section16SecondDerivedSubgroup M).subgroupOf M) =
        Nat.card (section16SecondDerivedSubgroup M) :=
    natCard_subgroupOf_eq (section16SecondDerivedSubgroup M) M hSecondM
  calc
    Nat.card W2 = Nat.card (W2.subgroupOf M) := hW2card.symm
    _ ≤ Nat.card ((section16SecondDerivedSubgroup M).subgroupOf M) := hcardSub
    _ = Nat.card (section16SecondDerivedSubgroup M) := hSecondCard

public theorem theorem_10_8_counting_quotient_sub_one_factor_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∃ k : ℕ,
      Nat.card W1 * k =
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) - 1 := by
  classical
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h104
  have h10copy := h10
  rcases h10 with
    ⟨_hM, hType, _hFamily, hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, U, hP, _hCases⟩
  let N : Subgroup (derivedSubgroup M) :=
    ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  let _ : N.Normal := hNnormal
  have hNchar : N.Characteristic := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Characteristic
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  have _ : N.Characteristic := hNchar
  have hNinvW1 : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := by
    exact isInvariant_of_characteristic (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N
  let _ : IsInvariant (W1.subgroupOf M) (derivedSubgroup M) N := hNinvW1
  let : MulDistribMulAction (W1.subgroupOf M) (derivedSubgroup M ⧸ N) :=
    quotientMulDistribMulAction (A := W1.subgroupOf M)
      (G := derivedSubgroup M) N hNinvW1
  have hfree :
      ∀ a : W1.subgroupOf M, a ≠ 1 →
        ∀ q : derivedSubgroup M ⧸ N, a • q = q → q = 1 := by
    intro a ha q hfix
    dsimp [N]
    exact typePDefinitionData_secondDerivedQuotient_fixed_eq_one_of_W1_ne_one_supported
      hP h10copy a ha q hfix
  let k : ℕ := Nat.card (nonidentityOrbitQuotient (W1.subgroupOf M) (derivedSubgroup M ⧸ N))
  refine ⟨k, ?_⟩
  have horbit := nonidentityOrbitQuotient_card_mul_eq_sub_one
    (A := W1.subgroupOf M) (G := derivedSubgroup M ⧸ N) hfree
  have hcardW1Sub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hquotcard :
      Nat.card (derivedSubgroup M ⧸ N) =
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) := by
    dsimp [N]
    exact theorem_10_8_counting_secondDerivedQuotient_card_eq_relIndex M
  have hquotcard' :
      Nat.card ((commutator M) ⧸ N) =
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) := by
    simpa [derivedSubgroup] using hquotcard
  dsimp [k] at horbit ⊢
  rw [hcardW1Sub] at horbit
  calc
    Nat.card W1 * Nat.card (nonidentityOrbitQuotient (W1.subgroupOf M) (commutator M ⧸ N)) =
        Nat.card (commutator M ⧸ N) - 1 := horbit
    _ = (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) - 1 := by
      rw [hquotcard']

public theorem theorem_10_8_counting_quotient_factor_ge_two_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {k : ℕ}
    (_hk :
      Nat.card W1 * k =
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) - 1) :
    2 ≤ k := by
  classical
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
  let N : Subgroup (derivedSubgroup M) :=
    ((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf (derivedSubgroup M)
  have hNnormal : N.Normal := by
    dsimp [N]
    change (((section16SecondDerivedSubgroup M).subgroupOf M).subgroupOf
      (derivedSubgroup M)).Normal
    rw [secondDerivedSubgroup_subgroupOf_derived_eq M]
    infer_instance
  let _ : N.Normal := hNnormal
  let q : ℕ := (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M)
  have hW1odd : Odd (Nat.card W1) :=
    odd_card_W1_of_hypothesis_10_4_supported_data _h104
  have hH2lt : (section16SecondDerivedSubgroup M).subgroupOf M < derivedSubgroup M :=
    typePDefinitionData_secondDerived_lt_derivedSubgroup hP
  have hquotNontrivial : Nontrivial (derivedSubgroup M ⧸ N) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    change N = ⊤ at htop
    have hle : derivedSubgroup M ≤ (section16SecondDerivedSubgroup M).subgroupOf M :=
      (Subgroup.subgroupOf_eq_top).1 htop
    exact hH2lt.not_ge hle
  have hq_gt_one : 1 < q := by
    have _ : Nontrivial (derivedSubgroup M ⧸ N) := hquotNontrivial
    have hcard_gt : 1 < Nat.card (derivedSubgroup M ⧸ N) := Finite.one_lt_card
    have hqcard : Nat.card (derivedSubgroup M ⧸ N) = q := by
      dsimp [N, q]
      exact theorem_10_8_counting_secondDerivedQuotient_card_eq_relIndex M
    rwa [hqcard] at hcard_gt
  have hqodd : Odd q := by
    have hModd : Odd (Nat.card M) := odd_card_M_of_hypothesis_10_4_supported_data _h104
    have hq_dvd_amb : q ∣ Nat.card (ambientDerivedSubgroup M) := by
      dsimp [q]
      exact Subgroup.relIndex_dvd_card
        (H := section16SecondDerivedSubgroup M)
        (K := ambientDerivedSubgroup M)
    have hambSub_dvd_M :
        Nat.card ((ambientDerivedSubgroup M).subgroupOf M) ∣ Nat.card M :=
      Subgroup.card_subgroup_dvd_card ((ambientDerivedSubgroup M).subgroupOf M)
    have hamb_card :
        Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
          Nat.card (ambientDerivedSubgroup M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (H := ambientDerivedSubgroup M) (K := M)
        (section12_ambientDerivedSubgroup_le (E := M))).toEquiv
    have hamb_dvd_M : Nat.card (ambientDerivedSubgroup M) ∣ Nat.card M := by
      rw [← hamb_card]
      exact hambSub_dvd_M
    exact Odd.of_dvd_nat hModd (Nat.dvd_trans hq_dvd_amb hamb_dvd_M)
  have hkq : Nat.card W1 * k = q - 1 := by
    simpa [q] using _hk
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hq_sub_one_zero : q - 1 = 0 := by
      simpa [hk0] using hkq.symm
    have hq_le_one : q ≤ 1 := Nat.sub_eq_zero_iff_le.mp hq_sub_one_zero
    exact (not_lt_of_ge hq_le_one) hq_gt_one
  have hkeven : Even k := by
    rw [← Nat.not_odd_iff_even]
    intro hkodd
    have hprodOdd : Odd (Nat.card W1 * k) := hW1odd.mul hkodd
    have hqminusOdd : Odd (q - 1) := by
      rw [← hkq]
      exact hprodOdd
    have hqEven : Even q := by
      have h := hqminusOdd.add_one
      have hq_ge_one : 1 ≤ q := Nat.le_of_lt hq_gt_one
      have hsucc : q - 1 + 1 = q := Nat.sub_add_cancel hq_ge_one
      simpa [hsucc] using h
    exact (Nat.not_odd_iff_even.mpr hqEven) hqodd
  rcases hkeven with ⟨t, ht⟩
  subst k
  omega

public theorem theorem_10_8_counting_quotient_lower_bound_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    2 * Nat.card W1 + 1 ≤
      (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) := by
  rcases theorem_10_8_counting_quotient_sub_one_factor_supported h104 with ⟨k, hk⟩
  exact theorem_10_8_counting_quotient_lower_bound_of_factor
    (w := Nat.card W1)
    (q := (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M))
    (Nat.card_pos (α := W1)) hk
    (theorem_10_8_counting_quotient_factor_ge_two_supported_source h104 hk)

public theorem theorem_10_8_counting_strict_upper_of_ratio_half
    {m w1 w2 : ℕ}
    (hm : 0 < m)
    (h : (1 / 2 : ℚ) < ((w1 * w2 : ℕ) : ℚ) / (m : ℚ)) :
    m < 2 * w1 * w2 := by
  have hmQ : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast hm
  have hmul : (m : ℚ) / 2 < ((w1 * w2 : ℕ) : ℚ) := by
    have h' := (lt_div_iff₀ hmQ).mp h
    nlinarith
  have hcast : (m : ℚ) < (2 * (w1 * w2 : ℕ) : ℚ) := by
    nlinarith
  have hnat : m < 2 * (w1 * w2) := by
    exact_mod_cast hcast
  simpa [Nat.mul_assoc] using hnat

public theorem theorem_10_8_counting_ratio_half_of_bound
    {m w1 w2 u : ℕ}
    (hm : 0 < m)
    (hw1 : 3 ≤ w1)
    (hw2 : 0 < w2)
    (hu : 7 ≤ u)
    (hbound :
      ((w1 : ℚ) / (m : ℚ)) >
        (1 / (w2 : ℚ)) - (1 / ((w1 * w2 : ℕ) : ℚ)) -
          (1 / ((w2 * u : ℕ) : ℚ))) :
    (1 / 2 : ℚ) < ((w1 * w2 : ℕ) : ℚ) / (m : ℚ) := by
  have hmQ : (0 : ℚ) < (m : ℚ) := by
    exact_mod_cast hm
  have hw1Q : (0 : ℚ) < (w1 : ℚ) := by
    exact_mod_cast (by omega : 0 < w1)
  have hw2Q : (0 : ℚ) < (w2 : ℚ) := by
    exact_mod_cast hw2
  have huQ : (0 : ℚ) < (u : ℚ) := by
    exact_mod_cast (by omega : 0 < u)
  have hmul := mul_lt_mul_of_pos_right hbound hw2Q
  norm_num [Nat.cast_mul] at hmul
  have hmul' :
      (1 : ℚ) - 1 / (w1 : ℚ) - 1 / (u : ℚ) <
        ((w1 * w2 : ℕ) : ℚ) / (m : ℚ) := by
    norm_num [Nat.cast_mul]
    field_simp [hmQ.ne', hw1Q.ne', hw2Q.ne', huQ.ne'] at hmul ⊢
    ring_nf at hmul ⊢
    nlinarith [hmQ, hw1Q, hw2Q, huQ]
  have hw1inv : (1 / (w1 : ℚ)) ≤ (1 / 3 : ℚ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hw1)
  have huinv : (1 / (u : ℚ)) ≤ (1 / 7 : ℚ) := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hu)
  have hlower : (1 / 2 : ℚ) < (1 : ℚ) - 1 / (w1 : ℚ) - 1 / (u : ℚ) := by
    nlinarith
  exact lt_trans hlower hmul'

public theorem section12ComplementIn_isComplement'_subgroupOf_right_pf108
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    (L.subgroupOf M).IsComplement' (K.subgroupOf M) := by
  rcases hcomp with ⟨hKM, hLM, hsup, hdisj⟩
  have hsup_local : L.subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
    calc
      L.subgroupOf M ⊔ K.subgroupOf M = (L ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := L) (A' := K) (B := M) hLM hKM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxL hxK
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxK,
      by simpa [Subgroup.mem_subgroupOf] using hxL⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (L.subgroupOf M) (K.subgroupOf M)).symm

public theorem section12ComplementIn_left_relIndex_eq_card_right_pf108
    {G : Type u}
    [Group G]
    [Finite G]
    {M K L : Subgroup G}
    (hcomp : section12ComplementIn M K L)
    [hKNormal : (K.subgroupOf M).Normal] :
    K.relIndex M = Nat.card L := by
  have hcompLocal : (L.subgroupOf M).IsComplement' (K.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_right_pf108 hcomp
  calc
    K.relIndex M = (K.subgroupOf M).index := rfl
    _ = Nat.card (L.subgroupOf M) := hcompLocal.index_eq_card
    _ = Nat.card L := natCard_subgroupOf_eq L M hcomp.2.1

public theorem theorem_10_8_counting_selected_Smax_card_eq
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax SF U W2 Wcentral : Subgroup G}
    (hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hP : Section8.typePDefinitionData Smax SF U W2 Wcentral) :
    Nat.card Smax = Nat.card SF * Nat.card U * Nat.card W2 := by
  rcases hP with
    ⟨_hSF, _hW2cyc, _hW2ne, _hW2hall, hScomp, _hUleD,
      _hUnil, _hW2norm, _hDercomp, _hRest⟩
  have hDcard :
      Nat.card (ambientDerivedSubgroup Smax) = Nat.card SF * Nat.card U := by
    have hlag :=
      relIndex_mul_card_eq_card_of_le
        (H := ambientDerivedSubgroup Smax) (H' := SF) hsemi.left_le
    rw [Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi] at hlag
    simpa [Nat.mul_comm] using hlag.symm
  have hrel :
      (ambientDerivedSubgroup Smax).relIndex Smax = Nat.card W2 :=
    by
      let _ : ((ambientDerivedSubgroup Smax).subgroupOf Smax).Normal := by
        simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
      exact section12ComplementIn_left_relIndex_eq_card_right_pf108 hScomp
  have hlagS :=
    relIndex_mul_card_eq_card_of_le
      (H := Smax) (H' := ambientDerivedSubgroup Smax) hScomp.1
  rw [hrel] at hlagS
  calc
    Nat.card Smax = Nat.card W2 * Nat.card (ambientDerivedSubgroup Smax) :=
      hlagS.symm
    _ = Nat.card W2 * (Nat.card SF * Nat.card U) := by rw [hDcard]
    _ = Nat.card SF * Nat.card U * Nat.card W2 := by ring

public theorem theorem_10_8_counting_ratio_bound_of_support_estimate
    {m w1 w2 u sf s : ℕ}
    (hw1 : 0 < w1)
    (hw2 : 0 < w2)
    (hu : 0 < u)
    (hsf : 0 < sf)
    (hs : s = sf * u * w2)
    (hpre :
      ((w1 : ℚ) / (m : ℚ)) >
        1 - ((sf : ℚ) / (s : ℚ) +
          (1 - 1 / (w2 : ℚ) - 1 / (w1 : ℚ) +
            1 / ((w1 * w2 : ℕ) : ℚ))) -
          1 / (w1 : ℚ)) :
    ((w1 : ℚ) / (m : ℚ)) >
      (1 / (w2 : ℚ)) -
        (1 / ((w1 * w2 : ℕ) : ℚ)) -
          (1 / ((w2 * u : ℕ) : ℚ)) := by
  have hw1Q : (0 : ℚ) < (w1 : ℚ) := by exact_mod_cast hw1
  have hw2Q : (0 : ℚ) < (w2 : ℚ) := by exact_mod_cast hw2
  have huQ : (0 : ℚ) < (u : ℚ) := by exact_mod_cast hu
  have hsfQ : (0 : ℚ) < (sf : ℚ) := by exact_mod_cast hsf
  have hsQ : (s : ℚ) = (sf : ℚ) * (u : ℚ) * (w2 : ℚ) := by
    exact_mod_cast hs
  have hSF :
      (sf : ℚ) / (s : ℚ) = 1 / ((w2 * u : ℕ) : ℚ) := by
    rw [hsQ]
    have hwu : ((w2 * u : ℕ) : ℚ) = (u : ℚ) * (w2 : ℚ) := by
      norm_num [Nat.cast_mul, Nat.mul_comm]
      ring
    rw [hwu]
    field_simp [hsfQ.ne', huQ.ne', hw2Q.ne']
  have halg :
      1 - (1 / ((w2 * u : ℕ) : ℚ) +
          (1 - 1 / (w2 : ℚ) - 1 / (w1 : ℚ) +
            1 / ((w1 * w2 : ℕ) : ℚ))) -
          1 / (w1 : ℚ) =
        (1 / (w2 : ℚ)) -
          (1 / ((w1 * w2 : ℕ) : ℚ)) -
            (1 / ((w2 * u : ℕ) : ℚ)) := by
    norm_num [Nat.cast_mul]
    field_simp [hw1Q.ne', hw2Q.ne', huQ.ne']
    ring
  rw [hSF] at hpre
  rw [halg] at hpre
  exact hpre

public theorem theorem_10_8_counting_ratio_support_estimate_of_g1_bounds
    {m w1 w2 sf s g1 g : ℕ}
    (hgap :
      (1 : ℚ) - ((g1 : ℚ) / (g : ℚ)) - 1 / (w1 : ℚ) <
        (w1 : ℚ) / (m : ℚ))
    (hg1 :
      ((g1 : ℚ) / (g : ℚ)) ≤
        ((sf : ℚ) / (s : ℚ) +
          (1 - 1 / (w2 : ℚ) - 1 / (w1 : ℚ) +
            1 / ((w1 * w2 : ℕ) : ℚ)))) :
    ((w1 : ℚ) / (m : ℚ)) >
      1 - ((sf : ℚ) / (s : ℚ) +
        (1 - 1 / (w2 : ℚ) - 1 / (w1 : ℚ) +
          1 / ((w1 * w2 : ℕ) : ℚ))) -
        1 / (w1 : ℚ) := by
  have hle :
      1 - ((sf : ℚ) / (s : ℚ) +
        (1 - 1 / (w2 : ℚ) - 1 / (w1 : ℚ) +
          1 / ((w1 * w2 : ℕ) : ℚ))) -
        1 / (w1 : ℚ) ≤
      (1 : ℚ) - ((g1 : ℚ) / (g : ℚ)) - 1 / (w1 : ℚ) := by
    linarith
  exact lt_of_le_of_lt hle hgap

@[expose] public def theorem_10_8_countingG1Set
    {G : Type u}
    [Group G]
    (tildeA : Set G)
    (W1 : Subgroup G) : Set G :=
  {g : G | g ∉ tildeA ∧ ¬ Nat.Coprime (orderOf g) (Nat.card W1)}

@[expose] public def theorem_10_8_countingHVSupportSet
    {G : Type u}
    [Group G]
    (H : Subgroup G)
    (V : Set G) : Set G :=
  section16ConjugatesOfSetBySet (Section7.puncturedSubgroupSet H) Set.univ ∪
    section16ConjugatesOfSetBySet V Set.univ

public theorem typePDefinitionData_secondComplement_prime_mem_mf
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {p : ℕ}
    (hpPrime : p.Prime)
    (hpW2 : p ∣ Nat.card W2) :
    (⟨p, hpPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet MF := by
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
      _hW1normU, _hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD,
      hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  have hW2MF : W2 ≤ MF := fun x hx => (hW2le hx).1
  have hcard_dvd : Nat.card W2 ∣ Nat.card MF :=
    Subgroup.card_dvd_of_le hW2MF
  change p ∣ Nat.card MF
  exact hpW2.trans hcard_dvd

public theorem theorem_10_8_typeII_mf_isHallSubgroup
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF) :
    IsHallSubgroup (subgroupPrimeSet SF) SF := by
  have hMs : Section8.msChoice Smax SF SF :=
    Or.inl ⟨Or.inr (Or.inl hTypeII), rfl⟩
  exact (Section8.theorem_8_11_of_msChoice (G := G) hSmax hSF hMs).2.1

public theorem theorem_10_8_exists_conjugate_mem_of_isHallSubgroup_prime_order
    {G : Type u}
    [Group G]
    [Finite G]
    {π : Set Nat.Primes}
    {H : Subgroup G}
    (hHall : IsHallSubgroup π H)
    {p : ℕ}
    (hpPrime : p.Prime)
    (hpπ : (⟨p, hpPrime⟩ : Nat.Primes) ∈ π)
    {a : G}
    (haOrder : orderOf a = p) :
    ∃ y : G, y * a * y⁻¹ ∈ H := by
  classical
  have _ : Fact p.Prime := ⟨hpPrime⟩
  let PH : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
  let Psub : Subgroup G := (PH : Subgroup H).map H.subtype
  have hPsub_p : IsPGroup p Psub := by
    simpa [Psub] using
      (IsPGroup.map (p := p) (H := (PH : Subgroup H)) PH.isPGroup' H.subtype)
  have hp_not_dvd_Hindex : ¬ p ∣ H.index := by
    intro hp_dvd
    exact (hHall.p_in_pi_of_p_dvd_index ⟨p, hpPrime⟩ hp_dvd) hpπ
  have hp_not_dvd_PHindex : ¬ p ∣ (PH : Subgroup H).index :=
    PH.not_dvd_index
  have hp_not_dvd_Psubindex : ¬ p ∣ Psub.index := by
    have hidx : Psub.index = (PH : Subgroup H).index * H.index := by
      simpa [Psub] using (Subgroup.index_map_subtype (K := (PH : Subgroup H)))
    rw [hidx]
    exact Nat.Prime.not_dvd_mul hpPrime hp_not_dvd_PHindex hp_not_dvd_Hindex
  let S : Sylow p G := IsPGroup.toSylow (p := p) hPsub_p hp_not_dvd_Psubindex
  have hS_le_H : (S : Subgroup G) ≤ H := by
    intro x hx
    change x ∈ Psub at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  let A : Subgroup G := Subgroup.zpowers a
  have hAp : IsPGroup p A := by
    exact IsPGroup.of_card (((Nat.card_zpowers a).trans haOrder).trans (pow_one p).symm)
  obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hAp
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨y, ?_⟩
  have haQ : a ∈ (Q : Subgroup G) := hAQ (Subgroup.mem_zpowers a)
  have hayS : y * a * y⁻¹ ∈ (S : Subgroup G) := by
    have hmem : (MulAut.conj y) a ∈ ((y • Q : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj y) (Q : Subgroup G) haQ
    simpa [MulAut.conj_apply, hy] using hmem
  exact hS_le_H hayS

public theorem theorem_10_8_conj_mem_elementCentralizerIn_top
    {G : Type u}
    [Group G]
    {x a y : G}
    (hxCent : x ∈ elementCentralizerIn (⊤ : Subgroup G) a) :
    y * x * y⁻¹ ∈ elementCentralizerIn (⊤ : Subgroup G) (y * a * y⁻¹) := by
  refine ⟨by simp, ?_⟩
  change y * x * y⁻¹ ∈ Subgroup.centralizer ({y * a * y⁻¹} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxCent.2
  calc
    (y * x * y⁻¹) * (y * a * y⁻¹) = y * (x * a) * y⁻¹ := by group
    _ = y * (a * x) * y⁻¹ := by rw [hcomm]
    _ = (y * a * y⁻¹) * (y * x * y⁻¹) := by group

public theorem theorem_10_8_countingHVSupportSet_conj_inv
    {G : Type u}
    [Group G]
    {H : Subgroup G}
    {V : Set G}
    {x y : G}
    (hxy : y * x * y⁻¹ ∈ theorem_10_8_countingHVSupportSet H V) :
    x ∈ theorem_10_8_countingHVSupportSet H V := by
  rcases hxy with hH | hV
  · left
    rcases hH with ⟨z, hz, t, _ht, hzt⟩
    refine ⟨z, hz, y⁻¹ * t, Set.mem_univ _, ?_⟩
    calc
      x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = y⁻¹ * (t * z * t⁻¹) * y := by rw [hzt]
      _ = (y⁻¹ * t) * z * (y⁻¹ * t)⁻¹ := by group
  · right
    rcases hV with ⟨z, hz, t, _ht, hzt⟩
    refine ⟨z, hz, y⁻¹ * t, Set.mem_univ _, ?_⟩
    calc
      x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = y⁻¹ * (t * z * t⁻¹) * y := by rw [hzt]
      _ = (y⁻¹ * t) * z * (y⁻¹ * t)⁻¹ := by group

public theorem theorem_10_8_counting_ratio_le_of_subset_ratio_le
    {G : Type u}
    [Group G]
    [Finite G]
    {X Y : Set G}
    {q : ℚ}
    (hXY : X ⊆ Y)
    (hY :
      ((Y.ncard : ℚ) / (Nat.card G : ℚ)) ≤ q) :
    ((X.ncard : ℚ) / (Nat.card G : ℚ)) ≤ q := by
  have hcard : X.ncard ≤ Y.ncard := Set.ncard_le_ncard hXY
  have hcardQ : (X.ncard : ℚ) ≤ (Y.ncard : ℚ) := by
    exact_mod_cast hcard
  have hden_nonneg : (0 : ℚ) ≤ (Nat.card G : ℚ) := by positivity
  exact (div_le_div_of_nonneg_right hcardQ hden_nonneg).trans hY

public theorem theorem_10_8_counting_union_ratio_bound
    {G : Type u}
    [Finite G]
    {X Y : Set G}
    {a b : ℚ}
    (hX : ((X.ncard : ℚ) / (Nat.card G : ℚ)) ≤ a)
    (hY : ((Y.ncard : ℚ) / (Nat.card G : ℚ)) ≤ b) :
    (((X ∪ Y).ncard : ℚ) / (Nat.card G : ℚ)) ≤ a + b := by
  have hcard : (X ∪ Y).ncard ≤ X.ncard + Y.ncard :=
    Set.ncard_union_le X Y
  have hcardQ :
      (((X ∪ Y).ncard : ℚ)) ≤ (X.ncard : ℚ) + (Y.ncard : ℚ) := by
    exact_mod_cast hcard
  have hden_nonneg : (0 : ℚ) ≤ (Nat.card G : ℚ) := by positivity
  have hdiv :
      (((X ∪ Y).ncard : ℚ) / (Nat.card G : ℚ)) ≤
        (((X.ncard : ℚ) + (Y.ncard : ℚ)) / (Nat.card G : ℚ)) :=
    div_le_div_of_nonneg_right hcardQ hden_nonneg
  have hsplit :
      (((X.ncard : ℚ) + (Y.ncard : ℚ)) / (Nat.card G : ℚ)) =
        (X.ncard : ℚ) / (Nat.card G : ℚ) +
          (Y.ncard : ℚ) / (Nat.card G : ℚ) := by
    ring
  rw [hsplit] at hdiv
  linarith


public theorem theorem_10_8_counting_rho_gap_of_real_source_bounds
    {g1 g w1 m : ℕ}
    {rho aRatio : ℝ}
    (hlower : (1 : ℝ) - (w1 : ℝ) / (m : ℝ) ≤ rho)
    (hupper : rho ≤ (g1 : ℝ) / (g : ℝ) + aRatio)
    (hA : aRatio < 1 / (w1 : ℝ)) :
    (1 : ℚ) - ((g1 : ℚ) / (g : ℚ)) - 1 / (w1 : ℚ) <
      ((w1 : ℚ) / (m : ℚ)) := by
  have hreal :
      (1 : ℝ) - ((g1 : ℝ) / (g : ℝ)) - 1 / (w1 : ℝ) <
        ((w1 : ℝ) / (m : ℝ)) := by
    linarith
  apply (Rat.cast_lt (K := ℝ)).mp
  norm_num [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one]
  simpa [div_eq_mul_inv] using hreal

public theorem theorem_10_8_counting_rho_upper_bound_of_cover_excess
    {rho g1Ratio aRatio coverExcess : ℝ}
    (hcover : -g1Ratio ≤ coverExcess)
    (hSuzuki : coverExcess + rho - aRatio ≤ 0) :
    rho ≤ g1Ratio + aRatio := by
  linarith

public noncomputable def theorem_10_8_countingRhoCoverExcess
    {G : Type u}
    [Group G]
    [Finite G]
    (tildeA : Set G)
    (χ : Section1.ClassFunction G) : ℝ :=
  by
    classical
    exact
      (∑ g : G, if g ∉ tildeA then Complex.normSq (χ g) - 1 else 0) /
        (Nat.card G : ℝ)

public theorem theorem_10_8_countingRhoCoverExcess_eq_normalizedSupportEnergy_sub
    {G : Type u}
    [Group G]
    [Finite G]
    {tildeA : Set G}
    (χ : Section1.ClassFunction G) :
    theorem_10_8_countingRhoCoverExcess tildeA χ =
      Section7.normalizedSupportEnergy (Set.univ \ tildeA) χ -
        Section7.normalizedSupportEnergy (Set.univ \ tildeA)
          (Section1.principalCharacter G) := by
  classical
  have hsum :
      (∑ g : G, if g ∉ tildeA then Complex.normSq (χ g) - 1 else 0) =
        (∑ g : G,
          ((if g ∈ (Set.univ \ tildeA : Set G) then Complex.normSq (χ g) else 0) -
            (if g ∈ (Set.univ \ tildeA : Set G) then (1 : ℝ) else 0))) := by
    refine Finset.sum_congr rfl ?_
    intro g _
    by_cases hg : g ∈ tildeA <;> simp [hg]
  rw [theorem_10_8_countingRhoCoverExcess, hsum, Finset.sum_sub_distrib]
  simp [Section7.normalizedSupportEnergy, Section7.supportEnergy,
    Section1.principalCharacter_apply]
  ring

public theorem theorem_10_8_counting_rho_coverExcess_lower_bound
    {G : Type u}
    [Group G]
    [Finite G]
    {tildeA : Set G}
    {W1 : Subgroup G}
    {χ : Section1.ClassFunction G}
    (hpoint :
      ∀ g : G, g ∉ tildeA → Nat.Coprime (orderOf g) (Nat.card W1) →
        1 ≤ Complex.normSq (χ g)) :
    -(((theorem_10_8_countingG1Set tildeA W1).ncard : ℝ) /
        (Nat.card G : ℝ)) ≤
      theorem_10_8_countingRhoCoverExcess tildeA χ := by
  classical
  have hsum_indicator :
      (∑ g : G,
          if g ∈ theorem_10_8_countingG1Set tildeA W1 then (-1 : ℝ) else 0) =
        -((theorem_10_8_countingG1Set tildeA W1).ncard : ℝ) := by
    have hcard :
        (Finset.univ.filter
            (fun g : G => g ∈ theorem_10_8_countingG1Set tildeA W1)).card =
          (theorem_10_8_countingG1Set tildeA W1).ncard := by
      rw [← Nat.card_coe_set_eq (theorem_10_8_countingG1Set tildeA W1)]
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← Finset.sum_filter]
    simp [hcard]
  have hpointwise :
      ∀ g : G,
        (if g ∈ theorem_10_8_countingG1Set tildeA W1 then (-1 : ℝ) else 0) ≤
          (if g ∉ tildeA then Complex.normSq (χ g) - 1 else 0) := by
    intro g
    by_cases hg1 : g ∈ theorem_10_8_countingG1Set tildeA W1
    · have hgA : g ∉ tildeA := hg1.1
      have hnorm_nonneg : (0 : ℝ) ≤ Complex.normSq (χ g) :=
        Complex.normSq_nonneg _
      simp [hg1, hgA]
      linarith
    · by_cases hgA : g ∉ tildeA
      · have hcop : Nat.Coprime (orderOf g) (Nat.card W1) := by
          by_contra hnot
          exact hg1 ⟨hgA, hnot⟩
        have hnorm_ge : (1 : ℝ) ≤ Complex.normSq (χ g) :=
          hpoint g hgA hcop
        simp [hg1, hgA]
        linarith
      · simp [hg1, hgA]
  have hsum :
      -((theorem_10_8_countingG1Set tildeA W1).ncard : ℝ) ≤
        ∑ g : G, if g ∉ tildeA then Complex.normSq (χ g) - 1 else 0 := by
    rw [← hsum_indicator]
    exact Finset.sum_le_sum (by intro g _; exact hpointwise g)
  have hden_nonneg : (0 : ℝ) ≤ (Nat.card G : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hsum hden_nonneg
  simpa [theorem_10_8_countingRhoCoverExcess, neg_div] using hdiv

public theorem theorem_10_8_ncard_lt_card_subgroup_of_subset_punctured
    {G : Type u}
    [Group G]
    [Finite G]
    {K : Subgroup G}
    {A : Set G}
    (hA : A ⊆ ((K : Set G) \ {1})) :
    A.ncard < Nat.card K := by
  classical
  have hproper : A ⊂ (K : Set G) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hA hx).1
    · intro hsub
      have h1A : (1 : G) ∈ A := hsub K.one_mem
      exact (hA h1A).2 (by simp)
  have hlt : Nat.card A < Nat.card (K : Set G) := by
    simpa using
      (Set.Finite.card_lt_card (Set.toFinite (K : Set G)) hproper)
  rw [← Nat.card_coe_set_eq A]
  simpa [Nat.card_eq_fintype_card] using hlt

public theorem theorem_10_8_ratio_lt_recip_of_ncard_lt_subgroup_card
    {G : Type u}
    [Group G]
    [Finite G]
    {K : Subgroup G}
    {A : Set G}
    {w : ℕ}
    (hAcard : A.ncard < Nat.card K)
    (hidx : K.index = w) :
    ((A.ncard : ℚ) / (Nat.card G : ℚ)) < 1 / (w : ℚ) := by
  classical
  have hcardG_nat : w * Nat.card K = Nat.card G := by
    simpa [hidx] using (Subgroup.index_mul_card (H := K))
  have hcardG : (Nat.card G : ℚ) = (w : ℚ) * (Nat.card K : ℚ) := by
    exact_mod_cast hcardG_nat.symm
  have hA_ltK : (A.ncard : ℚ) < (Nat.card K : ℚ) := by
    exact_mod_cast hAcard
  have hwposNat : 0 < w := by
    by_contra hw
    have hw0 : w = 0 := Nat.eq_zero_of_not_pos hw
    have hG0 : Nat.card G = 0 := by
      simpa [hw0] using hcardG_nat.symm
    exact (Nat.card_pos (α := G)).ne' hG0
  have hwpos : (0 : ℚ) < (w : ℚ) := by
    exact_mod_cast hwposNat
  have hKpos : (0 : ℚ) < (Nat.card K : ℚ) := by
    exact_mod_cast (Nat.card_pos (α := K))
  rw [hcardG]
  field_simp [hwpos.ne', hKpos.ne']
  nlinarith [hA_ltK, hwpos]

public theorem theorem_10_8_normalizedSupportEnergy_neg
    {G : Type u}
    [Group G]
    [Finite G]
    (X : Set G)
    (χ : Section1.ClassFunction G) :
    Section7.normalizedSupportEnergy X (-χ) =
      Section7.normalizedSupportEnergy X χ := by
  simp [Section7.normalizedSupportEnergy, Section7.supportEnergy]

public theorem theorem_10_8_dadeProjectionOn_neg
    {G : Type u}
    [Group G]
    [Finite G]
    (A : Set G)
    (L : Subgroup G)
    (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) :
    Section7.dadeProjectionOn A L H (-χ) =
      -Section7.dadeProjectionOn A L H χ := by
  ext x
  by_cases hx : (x : G) ∈ A <;>
    simp [Section7.dadeProjectionOn, Section7.dadeProjection,
      Section2.dadeAveragingFunction, hx, Finset.sum_neg_distrib]

public theorem theorem_10_8_weightedProjectionEnergy_neg
    {G : Type u}
    [Group G]
    [Finite G]
    (A : Set G)
    (L : Subgroup G)
    (H : G → Subgroup G)
    (χ : Section1.ClassFunction G) :
    Section7.weightedProjectionEnergy A L H (-χ) =
      Section7.weightedProjectionEnergy A L H χ := by
  unfold Section7.weightedProjectionEnergy
  rw [theorem_10_8_dadeProjectionOn_neg]
  simpa using
    (Section5.cfNormSq_smul (-1 : ℂ) (Section7.dadeProjectionOn A L H χ))

public theorem theorem_10_8_section7_theorem_7_5_signed
    {G : Type u}
    [Group G]
    [Finite G]
    {I : Type*}
    [Fintype I]
    (A : I → Set G)
    (L : I → Subgroup G)
    (H : I → G → Subgroup G)
    (G0 : Set G)
    (h74 : Section7.hypothesis_7_4_statement A L H G0)
    (χ : Section1.ClassFunction G)
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section7.normalizedSupportEnergy G0 χ +
        ∑ i, Section7.weightedProjectionEnergy (A i) (L i) (H i) χ ≤
      Section7.normalizedSupportEnergy G0 (Section1.principalCharacter G) +
        ∑ i, ((A i).ncard : ℝ) / (Nat.card (L i) : ℝ) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using Section7.theorem_7_5 A L H G0 h74 μ hμ
  · have hμneg : ((-1 : ℂ) • μ : Section1.ClassFunction G) = -μ := by
      ext g
      simp
    have h := Section7.theorem_7_5 A L H G0 h74 μ hμ
    simpa [hμneg, theorem_10_8_normalizedSupportEnergy_neg,
      theorem_10_8_weightedProjectionEnergy_neg] using h

public theorem theorem_10_8_dadeProjectionSupport_eq_tildeA
    {G : Type u}
    [Group G]
    [Finite G]
    {M : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0
        tildeA1 R) :
    Section7.dadeProjectionSupport A R = tildeA := by
  ext y
  rcases h14 with
    ⟨_hA1A, _hAA0, _hD, _hRbot, _hUnique, _hReq, htildeA,
      _htildeA0, _htildeA1⟩
  rw [htildeA]
  constructor
  · intro hy
    rcases hy with ⟨a, ha, r, hr, hconj⟩
    rcases hconj with ⟨x, hx⟩
    refine ⟨a, ha, ?_⟩
    refine ⟨a * r, ?_, x⁻¹, by simp, ?_⟩
    · exact ⟨r, hr, rfl⟩
    · calc
        y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x⁻¹ * (a * r) * x := by
          rw [show x * y * x⁻¹ = a * r by
            simpa [Section2.conjBy] using hx]
        _ = x⁻¹ * (a * r) * (x⁻¹)⁻¹ := by simp
  · intro hy
    rcases hy with ⟨a, ha, z, hz, x, _hxuniv, hy_eq⟩
    rcases hz with ⟨r, hr, hz_eq⟩
    refine ⟨a, ha, r, hr, ?_⟩
    refine ⟨x⁻¹, ?_⟩
    calc
      x⁻¹ * y * (x⁻¹)⁻¹ =
          x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ := by rw [hy_eq]
      _ = z := by group
      _ = a * r := hz_eq

public theorem theorem_10_8_notation_8_10_A_subset_M
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF Ms : Subgroup G}
    {A A0 A1 : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1) :
    A ⊆ (M : Set G) := by
  intro x hxA
  rcases hNotation with ⟨_hM, _hMF, _hMs, _hA1, hCases⟩
  rcases hCases with hTypeI | hTypeP
  · rcases hTypeI with ⟨_hTypeI, hA, _hA0⟩
    rw [hA, Section8.section8CentralizerUnion] at hxA
    rcases hxA with ⟨_z, _hz, hxCent⟩
    exact hxCent.1.1
  · rcases hTypeP with
      ⟨_U, _W1, _W2, _hP, _hSourceType, hA, _hA0, _hLate⟩
    rw [hA, Section8.section8CentralizerUnion] at hxA
    rcases hxA with ⟨_z, _hz, hxCent⟩
    exact (section12_ambientDerivedSubgroup_le (G := G) (E := M))
      hxCent.1.1

public theorem theorem_10_8_section8SubgroupSetPreimage_ncard_eq
    {G : Type u}
    [Group G]
    (M : Subgroup G)
    (A : Set G)
    (hA : A ⊆ (M : Set G)) :
    (Section8.section8SubgroupSetPreimage M A).ncard = A.ncard := by
  let e : {m : M // m ∈ Section8.section8SubgroupSetPreimage M A} ≃ A :=
    { toFun := fun m => ⟨(m.1 : G), m.2⟩
      invFun := fun a => ⟨⟨a.1, hA a.2⟩, a.2⟩
      left_inv := by
        intro m
        ext
        rfl
      right_inv := by
        intro a
        ext
        rfl }
  calc
    (Section8.section8SubgroupSetPreimage M A).ncard =
        Nat.card {m : M // m ∈ Section8.section8SubgroupSetPreimage M A} := by
      exact (Nat.card_coe_set_eq (Section8.section8SubgroupSetPreimage M A)).symm
    _ = Nat.card A := Nat.card_congr e
    _ = A.ncard := Nat.card_coe_set_eq A

public theorem theorem_10_8_section7_singleton_cover_inequality
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF Ms : Subgroup G}
    {A A0 A1 D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    {χ : Section1.ClassFunction G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms A A0 A1)
    (h14 :
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0
        tildeA1 R)
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section7.normalizedSupportEnergy (Set.univ \ tildeA) χ +
        Section7.weightedProjectionEnergy A M R χ ≤
      Section7.normalizedSupportEnergy (Set.univ \ tildeA)
          (Section1.principalCharacter G) +
        ((A.ncard : ℝ) / (Nat.card M : ℝ)) := by
  have h815 :=
    Section8.theorem_8_15 M MF Ms A A0 A1 D tildeA tildeA0 tildeA1 A R
      (∅ : Finset (Section1.ClassFunction M)) inferInstance
      ⟨hNotation, h14, Or.inr (Or.inl rfl)⟩
  have h22 : Section2.hypothesis_2_2_statement A M R := h815.2.1
  have hSupportEq : Section7.dadeProjectionSupport A R = tildeA :=
    theorem_10_8_dadeProjectionSupport_eq_tildeA h14
  have h74 : Section7.hypothesis_7_4_statement
      (fun _ : Unit => A) (fun _ : Unit => M) (fun _ : Unit => R)
      (Set.univ \ tildeA) := by
    constructor
    · constructor
      · intro _
        exact h22
      · intro i j hij
        cases i
        cases j
        exact False.elim (hij rfl)
    · ext y
      simp [hSupportEq]
  have h75 := theorem_10_8_section7_theorem_7_5_signed
    (fun _ : Unit => A) (fun _ : Unit => M) (fun _ : Unit => R)
    (Set.univ \ tildeA) h74 χ hχ
  simpa using h75


public theorem theorem_10_8_section8CentralizerUnion_self_eq_punctured
    {G : Type u}
    [Group G]
    (H : Subgroup G) :
    Section8.section8CentralizerUnion H H =
      Section7.puncturedSubgroupSet H := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    simp [Section7.puncturedSubgroupSet, section16NonidentityElements,
      elementCentralizerIn] at hx hy ⊢
    exact ⟨hy.1.1, hy.2⟩
  · intro hy
    refine ⟨y, ?_, ?_⟩
    · simpa [Section7.puncturedSubgroupSet, section16NonidentityElements] using hy
    · simp [Section7.puncturedSubgroupSet, section16NonidentityElements,
        elementCentralizerIn] at hy ⊢
      exact ⟨⟨hy.1, by simp [Subgroup.mem_centralizer_iff]⟩, hy.2⟩

public noncomputable def theorem_10_8_section7FullFamily
    {G : Type u}
    [Group G]
    [Finite G]
    (M : Subgroup G)
    (S : Finset (Section1.ClassFunction M)) :
    Finset (Section1.ClassFunction M) :=
  letI : DecidableEq (Section1.ClassFunction M) := Classical.decEq _
  insert (Section7.principalInducedCharacter M (ambientDerivedSubgroup M)) S


public theorem theorem_10_8_puncturedInducedFamily_ambientDerived_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section7.puncturedInducedFamily
      ((ambientDerivedSubgroup M).subgroupOf M) S := by
  rcases h10 with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46,
      _hNotation10, _h52⟩
  change ∀ χ : Section1.ClassFunction M,
    χ ∈ S ↔
      ∃ θ : Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M),
        Section1.IsIrreducibleCharacterOnGroup θ ∧
          θ ≠ Section1.principalCharacter ((ambientDerivedSubgroup M).subgroupOf M) ∧
            χ = Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ
  rw [section12_ambientDerivedSubgroup_subgroupOf_eq]
  exact hS

public theorem theorem_10_8_section7_theorem_7_8_hypothesis_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    Section7.theorem_7_8_hypothesis M (ambientDerivedSubgroup M)
      (theorem_10_8_section7FullFamily M S) S τ τ₁ ξ := by
  classical
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h104
  have hPunct :
      Section7.puncturedInducedFamily
        ((ambientDerivedSubgroup M).subgroupOf M) S :=
    theorem_10_8_puncturedInducedFamily_ambientDerived_supported h10
  have hHL : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hHnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  rcases h104 with ⟨h104a, hCoherent, hExt, _hOddM, _hTilde, _hParity⟩
  rcases h104a with
    ⟨_h10, _hNotation, hξS, hξIrr, hξDegree, _hUniform⟩
  have hrel : (ambientDerivedSubgroup M).relIndex M = Nat.card W1 := by
    simpa [Subgroup.relIndex, section12_ambientDerivedSubgroup_subgroupOf_eq]
      using (derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10)
  have hξDegreeRel :
      Section1.degree ξ = ((ambientDerivedSubgroup M).relIndex M : ℂ) := by
    rw [hrel]
    exact hξDegree
  refine ⟨hHL, ?_, hPunct, hCoherent, hExt, hξS, hξIrr, hξDegreeRel⟩
  intro χ
  constructor
  · intro hχS
    refine ⟨?_, ?_⟩
    · simpa [theorem_10_8_section7FullFamily, Finset.mem_insert] using Or.inr hχS
    · intro hχprincipal
      have hzero :
          Section1.scalarProduct M
              (Section7.principalInducedCharacter M (ambientDerivedSubgroup M))
              χ = 0 :=
        Section7.theorem_7_8_principalInduced_punctured_member_scalar
          hHnormal hPunct hχS
      have hself :
          Section1.scalarProduct M
              (Section7.principalInducedCharacter M (ambientDerivedSubgroup M))
              (Section7.principalInducedCharacter M (ambientDerivedSubgroup M)) =
            ((ambientDerivedSubgroup M).relIndex M : ℂ) :=
        Section7.theorem_7_8_principalInduced_self_scalar hHnormal
      have hrel_ne : ((ambientDerivedSubgroup M).relIndex M : ℂ) ≠ 0 := by
        have _ : ((ambientDerivedSubgroup M).subgroupOf M).FiniteIndex :=
          inferInstance
        have hrel0 : (ambientDerivedSubgroup M).relIndex M ≠ 0 := by
          simpa [Subgroup.relIndex] using
            (Subgroup.FiniteIndex.index_ne_zero
              (H := (ambientDerivedSubgroup M).subgroupOf M))
        exact_mod_cast hrel0
      apply hrel_ne
      calc
        ((ambientDerivedSubgroup M).relIndex M : ℂ) =
            Section1.scalarProduct M
              (Section7.principalInducedCharacter M (ambientDerivedSubgroup M))
              (Section7.principalInducedCharacter M (ambientDerivedSubgroup M)) :=
          hself.symm
        _ = Section1.scalarProduct M
              (Section7.principalInducedCharacter M (ambientDerivedSubgroup M))
              χ := by
            rw [hχprincipal]
        _ = 0 := hzero
  · intro hχ
    rcases hχ with ⟨hχT, hχne⟩
    have hχT' :
        χ = Section7.principalInducedCharacter M (ambientDerivedSubgroup M) ∨
          χ ∈ S := by
      simpa [theorem_10_8_section7FullFamily, Finset.mem_insert] using hχT
    rcases hχT' with hχprincipal | hχS
    · exact False.elim (hχne hχprincipal)
    · exact hχS

public theorem theorem_10_8_section7_hypothesis_7_6_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {Ms : Subgroup G}
    {Abook A0book A1book D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (h14 :
      Section8.notation_8_14_source_data M Abook A0book A1book D
        tildeA tildeA0 tildeA1 R) :
    Section7.hypothesis_7_6_statement Abook M (ambientDerivedSubgroup M) R
      (theorem_10_8_section7FullFamily M S) := by
  classical
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h104
  have hPunct :
      Section7.puncturedInducedFamily
        ((ambientDerivedSubgroup M).subgroupOf M) S :=
    theorem_10_8_puncturedInducedFamily_ambientDerived_supported h10
  have hT :
      Section7.inducedFamilyNotation ((ambientDerivedSubgroup M).subgroupOf M)
        (theorem_10_8_section7FullFamily M S) := by
    intro χ
    constructor
    · intro hχT
      have hχT' :
          χ = Section7.principalInducedCharacter M (ambientDerivedSubgroup M) ∨
            χ ∈ S := by
        simpa [theorem_10_8_section7FullFamily, Finset.mem_insert] using hχT
      rcases hχT' with hχprincipal | hχS
      · refine ⟨Section1.principalCharacter
            ((ambientDerivedSubgroup M).subgroupOf M), ?_, ?_⟩
        · exact Section3.principalCharacter_isIrreducibleCharacterOnGroup
        · simpa [Section7.principalInducedCharacter] using hχprincipal
      · rcases (hPunct χ).mp hχS with ⟨θ, hθirr, _hθne, hχeq⟩
        exact ⟨θ, hθirr, hχeq⟩
    · intro hχ
      rcases hχ with ⟨θ, hθirr, hχeq⟩
      by_cases hθ : θ =
          Section1.principalCharacter ((ambientDerivedSubgroup M).subgroupOf M)
      · have hχprincipal :
            χ = Section7.principalInducedCharacter M (ambientDerivedSubgroup M) := by
          simpa [Section7.principalInducedCharacter, hθ] using hχeq
        simpa [theorem_10_8_section7FullFamily, Finset.mem_insert] using
          Or.inl hχprincipal
      · have hχS : χ ∈ S :=
          (hPunct χ).mpr ⟨θ, hθirr, hθ, hχeq⟩
        simpa [theorem_10_8_section7FullFamily, Finset.mem_insert] using
          Or.inr hχS
  have h815 :=
    Section8.theorem_8_15 M MF Ms Abook A0book A1book D tildeA tildeA0
      tildeA1 Abook R (∅ : Finset (Section1.ClassFunction M))
      inferInstance ⟨hNotation, h14, Or.inr (Or.inl rfl)⟩
  have h22 : Section2.hypothesis_2_2_statement Abook M R := h815.2.1
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  have hTail := theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hAeqCentralizer :
      Abook =
        Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
          (ambientDerivedSubgroup M) :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data hNotation hTail
  have hAeqPunctured :
      Abook = Section7.puncturedSubgroupSet (ambientDerivedSubgroup M) :=
    hAeqCentralizer.trans
      (theorem_10_8_section8CentralizerUnion_self_eq_punctured
        (ambientDerivedSubgroup M))
  refine ⟨section12_ambientDerivedSubgroup_le (G := G) (E := M), ?_,
    h22, hAeqPunctured, hT⟩
  exact (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2

public theorem theorem_10_8_section7_relIndex_bound_of_hypothesis_10_4_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    (ambientDerivedSubgroup M).relIndex M ≤
      (Nat.card (ambientDerivedSubgroup M) - 1) / 2 := by
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h104
  have hrel : (ambientDerivedSubgroup M).relIndex M = Nat.card W1 := by
    simpa [Subgroup.relIndex, section12_ambientDerivedSubgroup_subgroupOf_eq]
      using (derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10)
  have hcard_mul :
      (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) *
          Nat.card (section16SecondDerivedSubgroup M) =
        Nat.card (ambientDerivedSubgroup M) :=
    relIndex_mul_card_eq_card_of_le (H := ambientDerivedSubgroup M)
      (H' := section16SecondDerivedSubgroup M)
      (theorem_10_8_secondDerived_le_ambientDerived M)
  have hsecond_pos : 0 < Nat.card (section16SecondDerivedSubgroup M) :=
    Nat.card_pos
  have hquot :
      2 * Nat.card W1 + 1 ≤
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) :=
    theorem_10_8_counting_quotient_lower_bound_supported_source h104
  have hcard_lower :
      2 * Nat.card W1 + 1 ≤ Nat.card (ambientDerivedSubgroup M) := by
    rw [← hcard_mul]
    nlinarith [hquot, hsecond_pos]
  rw [hrel]
  omega

public theorem theorem_10_8_dadeTransform_eq_of_eq_on_carrier
    {G : Type u}
    [Group G]
    [Finite G]
    {A : Set G}
    {L : Subgroup G}
    {H R : G → Subgroup G}
    (hH : Section2.Hypothesis2 A L H)
    (hR : Section2.Hypothesis2 A L R)
    (hHR : ∀ a : G, a ∈ A → H a = R a)
    (hHL : ∀ a ∈ A, a ∈ L)
    (hRL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L)
    (hα : Section2.CFOn L A α) :
    Section2.dadeTransform H hHL α = Section2.dadeTransform R hRL α := by
  ext g
  have hdefH := Section2.definition_2_5 A L H hH hHL α hα
  have hdefR := Section2.definition_2_5 A L R hR hRL α hα
  by_cases hgH : g ∈ Section2.dadeSupport A H
  · rcases hgH with ⟨a, ha, h, hh, hconj⟩
    have hhR : h ∈ R a := by
      simpa [hHR a ha] using hh
    have hleft :
        Section2.dadeTransform H hHL α g = α ⟨a, hHL a ha⟩ :=
      hdefH.1 ha hh hconj
    have hright :
        Section2.dadeTransform R hRL α g = α ⟨a, hRL a ha⟩ :=
      hdefR.1 ha hhR hconj
    have hsub : (⟨a, hHL a ha⟩ : L) = ⟨a, hRL a ha⟩ := by
      ext
      rfl
    simp [hleft, hright, hsub]
  · have hgR : g ∉ Section2.dadeSupport A R := by
      intro hgR
      rcases hgR with ⟨a, ha, h, hh, hconj⟩
      have hhH : h ∈ H a := by
        simpa [hHR a ha] using hh
      exact hgH ⟨a, ha, h, hhH, hconj⟩
    have hleft : Section2.dadeTransform H hHL α g = 0 :=
      Section2.dadeTransform_eq_zero_of_not_mem_support H hHL α hgH
    have hright : Section2.dadeTransform R hRL α g = 0 :=
      Section2.dadeTransform_eq_zero_of_not_mem_support R hRL α hgR
    simp [hleft, hright]

public theorem theorem_10_8_eq_of_le_of_same_semidirect_complement
    {G : Type u}
    [Group G]
    [Finite G]
    {C H R K : Subgroup G}
    (hHR : H ≤ R)
    (hH : Section2.IsInternalSemidirectProduct C H K)
    (hR : Section2.IsInternalSemidirectProduct C R K) :
    H = R := by
  refine Subgroup.eq_of_le_of_card_ge hHR ?_
  have hHrel : H.relIndex C = Nat.card K :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hH
  have hRrel : R.relIndex C = Nat.card K :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hR
  have hHmul :
      Nat.card K * Nat.card H = Nat.card C := by
    simpa [hHrel] using
      relIndex_mul_card_eq_card_of_le (H := C) (H' := H) hH.left_le
  have hRmul :
      Nat.card K * Nat.card R = Nat.card C := by
    simpa [hRrel] using
      relIndex_mul_card_eq_card_of_le (H := C) (H' := R) hR.left_le
  have hcard : Nat.card R = Nat.card H :=
    Nat.mul_left_cancel (Nat.card_pos (α := K)) (hRmul.trans hHmul.symm)
  exact Nat.le_of_eq hcard


public theorem theorem_10_8_counting_section7_selected_dade_data_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {Ms : Subgroup G}
    {Abook A0book A1book D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (_hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (_h14 :
      Section8.notation_8_14_source_data M Abook A0book A1book D
        tildeA tildeA0 tildeA1 R) :
    ∃ MsSelected : Subgroup G,
    ∃ A0selected A1selected : Set G,
      ∃ H_A0 : G → Subgroup G,
        Section8.notation_8_10_source_data M MF MsSelected Abook
            A0selected A1selected ∧
          ∃ hA0M : Section2.Hypothesis2 A0selected M H_A0,
            Abook ⊆ A0selected ∧
              ∀ α : Section1.ClassFunction M,
                Section2.CFOn M A0selected α →
                  τ α = Section2.dadeTransform H_A0 hA0M.subset_L α := by
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h104 with
    ⟨MFsrc, MsBook, Abook10, A0book10, A1book10, hSource10,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, _hFull⟩
  rcases hSource10 with
    ⟨_hApre, _hA0sub, hNotation10, H_A0, hA0M, hτ⟩
  have hMFsrc_eq : MFsrc = MF := by
    rcases h10 with
      ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
        _h46base, _hNotation10, _h52⟩
    rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
    exact section16MFSubgroup_unique hNotation10.2.1 hP.1
  have hNotation10_outer :
      Section8.notation_8_10_source_data M MF MsBook Abook10 A0book10
        A1book10 := by
    simpa [hMFsrc_eq] using hNotation10
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46base, _hNotation10, _h52⟩
  have hTail := theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hAbook10_eq :
      Abook10 =
        Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
          (ambientDerivedSubgroup M) :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data
      hNotation10_outer hTail
  have hAbook_eq :
      Abook =
        Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
          (ambientDerivedSubgroup M) :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data _hNotation hTail
  have hAbook_eq_Abook10 : Abook = Abook10 :=
    hAbook_eq.trans hAbook10_eq.symm
  have hAbook10_A0 : Abook10 ⊆ A0book10 :=
    theorem_10_8_A_subset_A0_of_notation_8_10_source_data
      hNotation10_outer
  have hAbook_A0 : Abook ⊆ A0book10 := by
    intro a ha
    exact hAbook10_A0 (by
      simpa [hAbook_eq_Abook10] using ha)
  have hNotationSelected :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book10
        A1book10 := by
    simpa [hAbook_eq_Abook10] using hNotation10_outer
  exact ⟨MsBook, A0book10, A1book10, H_A0, hNotationSelected,
    hA0M, hAbook_A0, hτ⟩


public theorem theorem_10_8_counting_section7_dade_complement_eq_tildeR_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {Ms : Subgroup G}
    {Abook A0book A1book D tildeA tildeA0 tildeA1 A0selected : Set G}
    {R H_A0 : G → Subgroup G}
    (_hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (_h14 :
      Section8.notation_8_14_source_data M Abook A0book A1book D
        tildeA tildeA0 tildeA1 R)
    {MsSelected : Subgroup G}
    {A1selected : Set G}
    (hSelectedNotation :
      Section8.notation_8_10_source_data M MF MsSelected Abook
        A0selected A1selected)
    (hA0M : Section2.Hypothesis2 A0selected M H_A0) :
    ∀ a : G, a ∈ Abook → H_A0 a = R a := by
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  have hAbookA0selected : Abook ⊆ A0selected :=
    theorem_10_8_A_subset_A0_of_notation_8_10_source_data hSelectedNotation
  have hR2 : Section2.Hypothesis2 Abook M R := by
    have h815 :=
      Section8.theorem_8_15 M MF Ms Abook A0book A1book D tildeA
        tildeA0 tildeA1 Abook R
        (∅ : Finset (Section1.ClassFunction M)) inferInstance
        ⟨_hNotation, _h14, Or.inr (Or.inl rfl)⟩
    exact h815.2.1
  have hHleR :
      ∀ a : G, a ∈ Abook → H_A0 a ≤ R a :=
    theorem_10_8_selectedDadeComplement_le_tildeR_supported_source
      h10 hSelectedNotation _hNotation _h14 hA0M
  intro a ha
  exact theorem_10_8_eq_of_le_of_same_semidirect_complement
    (hHleR a ha)
    (hA0M.centralizer_eq_product (hAbookA0selected ha))
    (hR2.centralizer_eq_product ha)

public theorem theorem_10_8_counting_section7_dade_transform_eq_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {Ms : Subgroup G}
    {Abook A0book A1book D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (_hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (_h14 :
      Section8.notation_8_14_source_data M Abook A0book A1book D
        tildeA tildeA0 tildeA1 R)
    (χ : Section1.ClassFunction M)
    (_hχ : Section2.CFOn M Abook χ) :
    τ χ =
      Section2.dadeTransform R
        (theorem_10_8_notation_8_10_A_subset_M _hNotation) χ := by
  let hAbookM : ∀ a : G, a ∈ Abook → a ∈ M :=
    theorem_10_8_notation_8_10_A_subset_M _hNotation
  rcases theorem_10_8_counting_section7_selected_dade_data_supported
      _h104 _hNotation _h14 with
    ⟨MsSelected, A0selected, A1selected, H_A0, hSelectedNotation,
      hA0M, hAbookA0, hτ⟩
  have hHR : ∀ a : G, a ∈ Abook → H_A0 a = R a :=
    theorem_10_8_counting_section7_dade_complement_eq_tildeR_supported_source
      _h104 _hNotation _h14 hSelectedNotation hA0M
  have hR2 : Section2.Hypothesis2 Abook M R := by
    have h815 :=
      Section8.theorem_8_15 M MF Ms Abook A0book A1book D tildeA
        tildeA0 tildeA1 Abook R
        (∅ : Finset (Section1.ClassFunction M)) inferInstance
        ⟨_hNotation, _h14, Or.inr (Or.inl rfl)⟩
    exact h815.2.1
  have h211 := Section2.proposition_2_11 A0selected Abook M H_A0
  have hH2 : Section2.Hypothesis2 Abook M H_A0 :=
    (h211 hAbookA0 hR2.L_le_normalizer hA0M).1
  have hχA0 : Section2.CFOn M A0selected χ :=
    Section2.CFOn_mono hAbookA0 _hχ
  have hRestrict :
      Section2.dadeTransform H_A0 hA0M.subset_L χ =
        Section2.dadeTransform H_A0 hAbookM χ :=
    (h211 hAbookA0 hR2.L_le_normalizer hA0M).2
      hA0M.subset_L hAbookM χ _hχ
  calc
    τ χ = Section2.dadeTransform H_A0 hA0M.subset_L χ := hτ χ hχA0
    _ = Section2.dadeTransform H_A0 hAbookM χ := hRestrict
    _ = Section2.dadeTransform R hAbookM χ :=
      theorem_10_8_dadeTransform_eq_of_eq_on_carrier
        hH2 hR2 hHR hAbookM hAbookM χ _hχ


public theorem theorem_10_8_counting_section7_dade_agreement_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {Ms : Subgroup G}
    {Abook A0book A1book D tildeA tildeA0 tildeA1 : Set G}
    {R : G → Subgroup G}
    (_hNotation :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (_h14 :
      Section8.notation_8_14_source_data M Abook A0book A1book D
        tildeA tildeA0 tildeA1 R) :
    Section7.agreesWithDadeTransform Abook M R τ := by
  refine ⟨theorem_10_8_notation_8_10_A_subset_M _hNotation, ?_⟩
  intro χ hχ
  exact theorem_10_8_counting_section7_dade_transform_eq_supported_source
    _h104 _hNotation _h14 χ hχ

public def theorem_10_8_countingSection7RhoData
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF : Subgroup G}
    {tildeA : Set G}
    (_hTilde : section10TildeAData M MF tildeA)
    (χ : Section1.ClassFunction G)
    (rho : ℝ) : Prop :=
  ∃ Ms : Subgroup G,
  ∃ A A0 A1 D tildeA0 tildeA1 : Set G,
  ∃ R : G → Subgroup G,
    Section8.notation_8_10_source_data M MF Ms A A0 A1 ∧
      Section8.notation_8_14_source_data M A A0 A1 D tildeA tildeA0 tildeA1 R ∧
        rho = Section7.weightedProjectionEnergy A M R χ


public theorem theorem_10_8_counting_rho_section7_projection_lower_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {tildeA : Set G}
    (_hTilde : section10TildeAData M MF tildeA) :
    ∃ rho : ℝ,
      theorem_10_8_countingSection7RhoData _hTilde (τ₁ ξ) rho ∧
      (1 : ℝ) -
          ((Nat.card W1 : ℝ) / (Nat.card (ambientDerivedSubgroup M) : ℝ)) ≤
        rho := by
  classical
  rcases _hTilde with
    ⟨Ms, Abook, A0book, A1book, D, tildeA0, tildeA1, R,
      hNotation, h14⟩
  let T : Finset (Section1.ClassFunction M) :=
    theorem_10_8_section7FullFamily M S
  let rho : ℝ := Section7.weightedProjectionEnergy Abook M R (τ₁ ξ)
  refine ⟨rho, ?_, ?_⟩
  · exact ⟨Ms, Abook, A0book, A1book, D, tildeA0, tildeA1, R,
      hNotation, h14, rfl⟩
  have h76 :
      Section7.hypothesis_7_6_statement Abook M (ambientDerivedSubgroup M) R
        T := by
    simpa [T] using
      theorem_10_8_section7_hypothesis_7_6_supported _h104 hNotation h14
  have hAgree :
      Section7.agreesWithDadeTransform Abook M R τ :=
    theorem_10_8_counting_section7_dade_agreement_supported_source
      _h104 hNotation h14
  have h78 :
      Section7.theorem_7_8_hypothesis M (ambientDerivedSubgroup M)
        T S τ τ₁ ξ := by
    simpa [T] using
      theorem_10_8_section7_theorem_7_8_hypothesis_supported _h104
  have hProj :
      ∀ a : ℤ, ∀ r : Section1.ClassFunction G,
        Section7.theorem_7_8_decompositionData M (ambientDerivedSubgroup M)
            S τ τ₁ ξ ((ambientDerivedSubgroup M).relIndex M) a r →
          Section7.theorem_7_8_b_projectionData Abook M
            (ambientDerivedSubgroup M) T τ τ₁ ξ a := by
    intro a r hdecomp
    simpa [T] using
      Section7.theorem_7_8_b_projectionData_source_bridge
        (A := Abook) (L := M) (H := ambientDerivedSubgroup M) (K := R)
        (T := T) (S := S) (τ := τ) (ν := τ₁) (ζ := ξ)
        h76 hAgree h78 hdecomp
  have hbound :
      (ambientDerivedSubgroup M).relIndex M ≤
        (Nat.card (ambientDerivedSubgroup M) - 1) / 2 :=
    theorem_10_8_section7_relIndex_bound_of_hypothesis_10_4_supported_data
      _h104
  have h78b :=
    Section7.theorem_7_8_b Abook M (ambientDerivedSubgroup M) R T S τ τ₁ ξ
      h76 hAgree h78 hProj hbound
  have hlower :
      (1 : ℝ) -
          ((Nat.card W1 : ℝ) /
            (Nat.card (ambientDerivedSubgroup M) : ℝ)) ≤
        rho := by
    have hrel :
        (ambientDerivedSubgroup M).relIndex M = Nat.card W1 := by
      have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
        hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
      simpa [Subgroup.relIndex, section12_ambientDerivedSubgroup_subgroupOf_eq]
        using (derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10)
    simpa [rho, Section7.weightedProjectionEnergy, hrel] using h78b.1
  exact hlower


public theorem theorem_10_8_counting_rho_section7_suzuki_cover_inequality_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (_h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {tildeA : Set G}
    (_hTilde : section10TildeAData M MF tildeA) :
    ∀ {rho : ℝ},
      theorem_10_8_countingSection7RhoData _hTilde (τ₁ ξ) rho →
        Section7.normalizedSupportEnergy (Set.univ \ tildeA) (τ₁ ξ) + rho ≤
          Section7.normalizedSupportEnergy (Set.univ \ tildeA)
              (Section1.principalCharacter G) +
            ((A.ncard : ℝ) / (Nat.card M : ℝ)) := by
  intro rho hRho
  rcases hRho with
    ⟨Ms, Abook, A0book, A1book, D, tildeA0, tildeA1, R,
      hNotationRho, h14, hrho⟩
  have hSigned : Section3.IsSignedIrreducibleCharacter (τ₁ ξ) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59
      (tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_supported_data _h104)
      (tauOne_xi_scalarProduct_self_of_hypothesis_10_4_supported_data _h104)
  have hCover :
      Section7.normalizedSupportEnergy (Set.univ \ tildeA) (τ₁ ξ) +
          Section7.weightedProjectionEnergy Abook M R (τ₁ ξ) ≤
        Section7.normalizedSupportEnergy (Set.univ \ tildeA)
            (Section1.principalCharacter G) +
          ((Abook.ncard : ℝ) / (Nat.card M : ℝ)) :=
    theorem_10_8_section7_singleton_cover_inequality hNotationRho h14 hSigned
  have hNotation10 := section10FourSixNotation_of_hypothesis_10_4_supported_data
    _h104
  rcases hNotation10 with
    ⟨MFsrc, MsBook, Abook10, A0book10, A1book10, hSource10,
      _hW, _hA0, _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, _hFull⟩
  rcases hSource10 with
    ⟨hApre, _hA0sub, hNotation10, _H_A0, _hA0M, _hτ⟩
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  have hMFsrc_eq : MFsrc = MF := by
    rcases h10 with
      ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
        _h46base, _hNotation10, _h52⟩
    rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
    exact section16MFSubgroup_unique hNotation10.2.1 hP.1
  have hNotation10_outer :
      Section8.notation_8_10_source_data M MF MsBook Abook10 A0book10
        A1book10 := by
    simpa [hMFsrc_eq] using hNotation10
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46base, _hNotation10, _h52⟩
  have hTail := theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hAbook10_eq :
      Abook10 =
        Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
          (ambientDerivedSubgroup M) :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data
      hNotation10_outer hTail
  have hAbook_eq :
      Abook =
        Section8.section8CentralizerUnion (ambientDerivedSubgroup M)
          (ambientDerivedSubgroup M) :=
    theorem_10_8_A_eq_late_of_notation_8_10_source_data
      hNotationRho hTail
  have hAbook10_eq_Abook : Abook10 = Abook := by
    exact hAbook10_eq.trans hAbook_eq.symm
  have hAeq : A = Section8.section8SubgroupSetPreimage M Abook := by
    simpa [hAbook10_eq_Abook] using hApre
  have hAbookM : Abook ⊆ (M : Set G) :=
    theorem_10_8_notation_8_10_A_subset_M hNotationRho
  have hAcard :
      A.ncard = Abook.ncard := by
    rw [hAeq]
    exact theorem_10_8_section8SubgroupSetPreimage_ncard_eq M Abook hAbookM
  simpa [hrho, hAcard] using hCover

public theorem theorem_10_8_counting_rho_section7_suzuki_cover_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {tildeA : Set G}
    (hTilde : section10TildeAData M MF tildeA) :
    ∀ {rho : ℝ},
      theorem_10_8_countingSection7RhoData hTilde (τ₁ ξ) rho →
        theorem_10_8_countingRhoCoverExcess tildeA (τ₁ ξ) + rho -
            ((A.ncard : ℝ) / (Nat.card M : ℝ)) ≤ 0 := by
  intro rho hrho
  have hcover :=
    theorem_10_8_counting_rho_section7_suzuki_cover_inequality_supported_source
      h104 hTilde hrho
  rw [theorem_10_8_countingRhoCoverExcess_eq_normalizedSupportEnergy_sub]
  linarith


public theorem theorem_10_8_counting_rho_section7_cover_supported_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I}
    {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ}
    {δ : ℤ}
    (h104 :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ)
    {tildeA : Set G}
    (hTilde : section10TildeAData M MF tildeA) :
    ∃ rho : ℝ,
      (1 : ℝ) -
          ((Nat.card W1 : ℝ) / (Nat.card (ambientDerivedSubgroup M) : ℝ)) ≤
        rho ∧
        theorem_10_8_countingRhoCoverExcess tildeA (τ₁ ξ) + rho -
            ((A.ncard : ℝ) / (Nat.card M : ℝ)) ≤ 0 := by
  rcases theorem_10_8_counting_rho_section7_projection_lower_supported_source
      h104 hTilde with
    ⟨rho, hrho, hlower⟩
  exact ⟨rho, hlower,
    theorem_10_8_counting_rho_section7_suzuki_cover_supported_source
      h104 hTilde hrho⟩


public theorem theorem_10_8_mem_normalizer_of_ti_subset_centralizes_mem
    {G : Type u}
    [Group G]
    {X : Set G}
    {N : Subgroup G}
    {x a : G}
    (hTI : section16TISubsetWithNormalizer X N)
    (haX : a ∈ X)
    (haNe : a ≠ 1)
    (hxa : x ∈ elementCentralizerIn (⊤ : Subgroup G) a) :
    x ∈ N := by
  have hnotSmall : ¬ X ∩ section16ConjugateSet X x ⊆ ({1} : Set G) := by
    intro hsmall
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxa.2
    have haConj : a ∈ section16ConjugateSet X x := by
      refine ⟨a, haX, ?_⟩
      have hxa_eq : x * a * x⁻¹ = a := by
        calc
          x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [hcomm]
          _ = a := by group
      exact hxa_eq.symm
    exact haNe (by simpa using hsmall ⟨haX, haConj⟩)
  rcases hTI.1 x with hconj | hsmall
  · have hxNorm : x ∈ Subgroup.normalizer X := by
      change ∀ y : G, y ∈ X ↔ x * y * x⁻¹ ∈ X
      intro y
      constructor
      · intro hy
        have hyConj : x * y * x⁻¹ ∈ section16ConjugateSet X x :=
          ⟨y, hy, rfl⟩
        simpa [hconj] using hyConj
      · intro hy
        have hyConj : x * y * x⁻¹ ∈ section16ConjugateSet X x := by
          simpa [hconj] using hy
        rcases hyConj with ⟨z, hz, hyz⟩
        have hy_eq : y = z := by
          calc
            y = x⁻¹ * (x * y * x⁻¹) * x := by group
            _ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hyz]
            _ = z := by group
        simpa [hy_eq] using hz
    simpa [hTI.2] using hxNorm
  · exact False.elim (hnotSmall hsmall)

public theorem theorem_10_8_ne_one_of_prime_dvd_order
    {G : Type u}
    [Group G]
    {x : G}
    {p : ℕ}
    (hpPrime : p.Prime)
    (hpx : p ∣ orderOf x) :
    x ≠ 1 := by
  intro hx
  have hpOne : p ∣ 1 := by
    simpa [hx] using hpx
  exact hpPrime.ne_one (Nat.dvd_one.mp hpOne)

public theorem theorem_10_8_frobeniusJoin_mem_kernel_of_mem_join_centralizes_ne
    {G : Type u}
    [Group G]
    [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R)
    {x a : G}
    (hxJoin : x ∈ K ⊔ R)
    (haK : a ∈ K)
    (haNe : a ≠ 1)
    (hxa : x ∈ elementCentralizerIn (⊤ : Subgroup G) a) :
    x ∈ K := by
  classical
  by_contra hxnotK
  let L : Subgroup G := K ⊔ R
  let Ksub : Subgroup L := K.subgroupOf L
  let Rsub : Subgroup L := R.subgroupOf L
  have hfrobL : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [section12FrobeniusJoinWithKernel, L, Ksub, Rsub] using hfrob
  have hKnormal : (K.subgroupOf L).Normal := by
    simpa [Ksub] using IsFrobeniusGroupWithKernelComplement.normal hfrobL
  have hcent : ∀ r : Rsub, r ≠ 1 →
      Section2.centralizerIn Ksub (r : L) = ⊥ := by
    intro r hrne
    have hcentElem : elementCentralizerIn Ksub (r : L) = ⊥ :=
      (lemma_3_1 Ksub Rsub
        (IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobL)
        (IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobL)
        (IsFrobeniusGroupWithKernelComplement.normal hfrobL)
        (IsFrobeniusGroupWithKernelComplement.isComplement' hfrobL)).1
        hfrobL r hrne
    simpa [Section2.centralizerIn, Section2.elementCentralizer, elementCentralizerIn]
      using hcentElem
  have hfrob6 : Section6.frobeniusWithKernel L K := by
    refine ⟨le_sup_left, hKnormal, Rsub, ?_, ?_, ?_, ?_⟩
    · exact IsFrobeniusGroupWithKernelComplement.isComplement' hfrobL
    · exact IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobL
    · exact IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobL
    · exact hcent
  have hcentBot : Section2.centralizerIn K x = ⊥ :=
    Section6.theorem_6_8_frobeniusWithKernel_centralizerIn_eq_bot_of_not_mem
      (L0 := L) (H := K) hfrob6 x hxJoin hxnotK
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hxa.2
  have haCentX : a ∈ Section2.elementCentralizer x := by
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = x := by simpa using hz
    subst z
    exact hcomm
  have haCent : a ∈ Section2.centralizerIn K x :=
    ⟨haK, haCentX⟩
  have haBot : a ∈ (⊥ : Subgroup G) := by
    simpa [hcentBot] using haCent
  exact haNe (by simpa using haBot)

public theorem theorem_10_8_section16HatW_swap
    {G : Type u}
    [Group G]
    (W1 W2 : Subgroup G) :
    section16HatW W2 W1 = section16HatW W1 W2 := by
  ext x
  simp [section16HatW, sup_comm, Set.union_comm]

public theorem section16ASet_subset_ambientDerived_of_nontrivial_KUData
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M K Uc : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section16KUData M K Uc)
    (hKne : K ≠ ⊥) :
    section16ASet M Uc ⊆ ambientDerivedSubgroup M := by
  intro x hx
  have hD_eq : ambientDerivedSubgroup M = Uc ⊔ section10Msigma M :=
    (lemma_15_1_b (G := G) hM (by simpa [section16KUData] using hKU) hKne).1
  rcases hx with ⟨_hxHat, hxProd, _hxne⟩
  rcases hxProd with ⟨u, hu, s, hs, hxs⟩
  rw [← hxs]
  simpa [hD_eq] using
    ((Uc ⊔ section10Msigma M : Subgroup G).mul_mem
      (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hs))

public theorem theorem_10_8_not_mem_ASet_of_typeP_not_mem_source_join
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 Uc : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hKU : section16KUData M W1 Uc)
    {x : G}
    (hxNotHU : x ∉ MF ⊔ U) :
    x ∉ section16ASet M Uc := by
  intro hxA
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, hDercomp, _hRest⟩
  have hxD : x ∈ ambientDerivedSubgroup M :=
    section16ASet_subset_ambientDerived_of_nontrivial_KUData
      (G := G) hM hKU hW1ne hxA
  have hD_eq : ambientDerivedSubgroup M = MF ⊔ U := hDercomp.2.2.1
  exact hxNotHU (by simpa [hD_eq] using hxD)

public theorem theorem_10_8_exists_prime_order_zpower_centralized
    {G : Type u}
    [Group G]
    [Finite G]
    {x : G}
    {p : ℕ}
    (hp : p.Prime)
    (hpx : p ∣ orderOf x) :
    ∃ a : G,
      a ∈ Subgroup.zpowers x ∧
        a ≠ 1 ∧ orderOf a = p ∧ x ∈ elementCentralizerIn (⊤ : Subgroup G) a := by
  classical
  have _ : Fact p.Prime := ⟨hp⟩
  have hpdvd_zpowers : p ∣ Nat.card (Subgroup.zpowers x) := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_zpowers] using hpx
  rcases exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) p hpdvd_zpowers with
    ⟨a0, ha0order⟩
  let a : G := a0
  have haZ : a ∈ Subgroup.zpowers x := a0.property
  have haOrder : orderOf a = p := by
    simpa [a, Subgroup.orderOf_coe] using ha0order
  have hane : a ≠ 1 := by
    intro ha1
    have horder_one : orderOf a = 1 := orderOf_eq_one_iff.mpr ha1
    exact hp.ne_one (haOrder.symm.trans horder_one)
  have hcomm : Commute a x := by
    rcases Subgroup.mem_zpowers_iff.mp haZ with ⟨n, hn⟩
    simp [← hn]
  have hxCent : x ∈ elementCentralizerIn (⊤ : Subgroup G) a :=
    ⟨by simp, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  exact ⟨a, haZ, hane, haOrder, hxCent⟩

public theorem theorem_10_8_typeP_not_conj_nonidentity_W1_of_prime_support
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {x : G}
    {p : ℕ}
    (hpPrime : p.Prime)
    (hpMF : (⟨p, hpPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet MF)
    (hxOrder : p ∣ orderOf x) :
    x ∉ section16ConjugatesOfSetBySet
      (section16NonidentityElements (W1 : Set G)) (M : Set G) := by
  intro hconj
  have hPFull : Section8.typePDefinitionData M MF U W1 W2 := hP
  rcases hconj with ⟨w, hw, m, _hmM, hx_eq⟩
  have hconj_order : orderOf (m * w * m⁻¹) = orderOf w := by
    simpa [MulAut.conj_apply] using (MulAut.conj m).orderOf_eq w
  have hpW1card : p ∣ Nat.card W1 := by
    have hpw : p ∣ orderOf w := by
      rw [hx_eq] at hxOrder
      simpa [hconj_order] using hxOrder
    exact hpw.trans (Subgroup.orderOf_dvd_natCard W1 hw.1)
  rcases hP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, hDercomp, _hRest⟩
  have hpMFcard : p ∣ Nat.card MF := by
    change p ∣ Nat.card MF at hpMF
    exact hpMF
  have hpD : p ∣ Nat.card (ambientDerivedSubgroup M) :=
    hpMFcard.trans (Subgroup.card_dvd_of_le hDercomp.1)
  have hcop : Nat.Coprime (Nat.card W1) (Nat.card (ambientDerivedSubgroup M)) :=
    Section8.theorem_8_13_typeP_W1_coprime_ambientDerived (G := G) hPFull
  exact hpPrime.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpW1card hpD)

public theorem theorem_10_8_typeP_prime_support_mem_AZeroSet
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    {x : G}
    {p : ℕ}
    (hpPrime : p.Prime)
    (hpMF : (⟨p, hpPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet MF)
    (hxOrder : p ∣ orderOf x)
    (hxM : x ∈ M) :
    x ∈ section16AZeroSet M W1 := by
  classical
  have hPFull : Section8.typePDefinitionData M MF U W1 W2 := hP
  rcases theorem_10_8_exists_prime_order_zpower_centralized
      (G := G) hpPrime hxOrder with
    ⟨a, haZ, hane, haOrder, hxCentTop⟩
  have haM : a ∈ M := (Subgroup.zpowers_le).2 hxM haZ
  let A : Subgroup G := Subgroup.zpowers a
  have hAleM : A ≤ M := (Subgroup.zpowers_le).2 haM
  have hAcard : Nat.card A = p := by
    simpa [A] using (Nat.card_zpowers a).trans haOrder
  have hAsubP : IsPGroup p (A.subgroupOf M) := by
    have hAsubCard : Nat.card (A.subgroupOf M) = p :=
      (natCard_subgroupOf_eq A M hAleM).trans hAcard
    exact IsPGroup.of_card (hAsubCard.trans (pow_one p).symm)
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hRest⟩
  rcases hMF with ⟨hMFHallData, _hMFmax⟩
  rcases hMFHallData with ⟨_hMFM, hMFnormal, _hMFnil, hMFHall⟩
  let p' : Nat.Primes := ⟨p, hpPrime⟩
  have hAleMFsub : A.subgroupOf M ≤ MF.subgroupOf M := by
    have _ : (MF.subgroupOf M).Normal := hMFnormal
    exact section12_pSubgroup_le_normal_hall_of_prime_mem
      (R := M) (π := subgroupPrimeSet MF)
      (H := MF.subgroupOf M) (A := A.subgroupOf M) (p := p')
      hMFHall (by
        dsimp [p']
        exact hpMF) hAsubP
  have haMF : a ∈ MF := by
    have haSub : (⟨a, haM⟩ : M) ∈ MF.subgroupOf M :=
      hAleMFsub (by
        change (a : G) ∈ A
        exact Subgroup.mem_zpowers a)
    simpa [Subgroup.mem_subgroupOf] using haSub
  have hMFleSigma : MF ≤ section10Msigma M :=
    (theorem_15_2_chain (G := G) hM hPFull.1).2.1
  have haSigma : a ∈ section10Msigma M := hMFleSigma haMF
  have hxHat : x ∈ section16HatMsigmaSet M := by
    refine ⟨hxM, ?_⟩
    have haCentX : a ∈ elementCentralizerIn (section10Msigma M) x := by
      refine ⟨haSigma, ?_⟩
      have hcomm : Commute x a :=
        Subgroup.mem_centralizer_singleton_iff.mp hxCentTop.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let aC : elementCentralizerIn (section10Msigma M) x := ⟨a, haCentX⟩
    refine ⟨aC, ?_⟩
    intro haC
    exact hane (by simpa [aC] using congrArg Subtype.val haC)
  refine ⟨hxHat, ?_, theorem_10_8_ne_one_of_prime_dvd_order hpPrime hxOrder⟩
  exact theorem_10_8_typeP_not_conj_nonidentity_W1_of_prime_support
    (G := G) hPFull hpPrime hpMF hxOrder

public theorem theorem_10_8_typeP_not_mem_join_prime_support_conjugates_hatW_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {Smax SF U Wleft Wright : Subgroup G}
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hTypeP : Section8.typePDefinitionData Smax SF U Wleft Wright)
    {x : G}
    {p : ℕ}
    (_hpPrime : p.Prime)
    (_hpSF : (⟨p, _hpPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet SF)
    (_hxOrder : p ∣ orderOf x)
    (_hxS : x ∈ Smax)
    (_hxNotHU : x ∉ SF ⊔ U) :
    x ∈ section16ConjugatesOfSetBySet (section16HatW Wleft Wright) (Smax : Set G) := by
  classical
  have hMP : Smax ∈ section14MFamilyP G :=
    Section8.sourceTypeP_mFamilyP_of_source_typeP (G := G) _hSmax _hTypeP
  rcases Section8.sourceTypeP_exists_KUData_of_aligned_complement
      (G := G) _hSmax _hTypeP with
    ⟨Uc, hKU⟩
  have hxA0 : x ∈ section16AZeroSet Smax Wleft :=
    theorem_10_8_typeP_prime_support_mem_AZeroSet
      (G := G) _hSmax _hTypeP _hpPrime _hpSF _hxOrder _hxS
  have hxNotA : x ∉ section16ASet Smax Uc :=
    theorem_10_8_not_mem_ASet_of_typeP_not_mem_source_join
      (G := G) _hSmax _hTypeP hKU _hxNotHU
  have hxDiff :
      x ∈ section16AZeroSet Smax Wleft \ section16ASet Smax Uc :=
    ⟨hxA0, hxNotA⟩
  have hKU15 : section15KUData Smax Wleft Uc := by
    simpa [section16KUData] using hKU
  have hxHatZ :
      x ∈ section16ConjugatesOfSetBySet
        (section16HatZ Wleft (section16Kstar Smax Wleft)) (Smax : Set G) := by
    simpa [section16_conjugates_hatZ_eq_A0_diff_A
      (G := G) (M := Smax) (K := Wleft) (U := Uc) hMP hKU15] using hxDiff
  have hKstar : section16Kstar Smax Wleft = Wright :=
    theorem_10_7_section16Kstar_eq_W2_of_source_typeP
      (G := G) _hSmax _hTypeP
  simpa [section16HatZ, section16HatW, section16ZSubgroup, hKstar] using hxHatZ


public theorem theorem_10_8_mem_normalizer_of_conjugateSet_eq
    {G : Type u}
    [Group G]
    {X : Set G} {g : G}
    (hX : section16ConjugateSet X g = X) :
    g ∈ Subgroup.normalizer X := by
  change ∀ y : G, y ∈ X ↔ g * y * g⁻¹ ∈ X
  intro y
  constructor
  · intro hy
    rw [← hX]
    exact ⟨y, hy, rfl⟩
  · intro hy
    have hmem : g * y * g⁻¹ ∈ section16ConjugateSet X g := by
      simpa [hX] using hy
    rcases hmem with ⟨x, hx, hxy⟩
    have hyx : y = x := by
      simpa [mul_assoc] using congrArg (fun z : G => g⁻¹ * z * g) hxy
    simpa [hyx] using hx

public theorem theorem_10_8_card_conjugatesOfSetBySet_eq_card_mul_index_of_ti
    {G : Type u}
    [Group G]
    [Finite G]
    {X : Set G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubset X) :
    Nat.card (section16ConjugatesOfSetBySet X Set.univ) =
      Nat.card X * (Subgroup.normalizer X).index := by
  classical
  let N : Subgroup G := Subgroup.normalizer X
  let Ω := Quotient (QuotientGroup.rightRel N)
  let X0 := {x : G // x ∈ X}
  let f : Ω × X0 → {z : G // z ∈ section16ConjugatesOfSetBySet X Set.univ} :=
    fun qx =>
      let a : G := Quotient.out qx.1
      ⟨a⁻¹ * qx.2.1 * a,
        ⟨qx.2.1, qx.2.2, a⁻¹, Set.mem_univ _, by simp [mul_assoc]⟩⟩
  have hfBij : Function.Bijective f := by
    constructor
    · intro qx1 qx2 hEq
      rcases qx1 with ⟨q1, x1⟩
      rcases qx2 with ⟨q2, x2⟩
      let a1 : G := Quotient.out q1
      let a2 : G := Quotient.out q2
      have hval : a1⁻¹ * x1.1 * a1 = a2⁻¹ * x2.1 * a2 :=
        congrArg Subtype.val hEq
      by_cases hq : q1 = q2
      · have ha : a2 = a1 := by
          simpa [a1, a2] using congrArg Quotient.out hq.symm
        have hx : x1 = x2 := by
          apply Subtype.ext
          rw [ha] at hval
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, mul_assoc] using hconj
        cases hq
        cases hx
        rfl
      · have hgNotN : a1 * a2⁻¹ ∉ N := by
          intro hgN
          apply hq
          have hginv : a2 * a1⁻¹ ∈ N := by
            simpa using N.inv_mem hgN
          calc
            q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
            _ = Quotient.mk'' a2 :=
              Quotient.sound' (QuotientGroup.rightRel_apply.mpr hginv)
            _ = q2 := Quotient.out_eq' q2
        have hx1Conj : x1.1 ∈ section16ConjugateSet X (a1 * a2⁻¹) := by
          refine ⟨x2.1, x2.2, ?_⟩
          have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
          simpa [a1, a2, mul_assoc] using hconj
        rcases hXti (a1 * a2⁻¹) with hsame | hsmall
        · exact False.elim
            (hgNotN (theorem_10_8_mem_normalizer_of_conjugateSet_eq hsame))
        · have hx1one : x1.1 = 1 := by
            simpa using hsmall ⟨x1.2, hx1Conj⟩
          exact False.elim (hX1 (hx1one ▸ x1.2))
    · intro z
      rcases z.2 with ⟨x, hxX, y, _hy, hzy⟩
      let q : Ω := Quotient.mk'' y⁻¹
      let a : G := Quotient.out q
      have hyaN : y⁻¹ * a⁻¹ ∈ N := by
        have hqa : (Quotient.mk'' a : Ω) = Quotient.mk'' y⁻¹ := by
          simp [q, a]
        exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
      let n : G := y⁻¹ * a⁻¹
      have hnInvNorm : n⁻¹ ∈ N := N.inv_mem hyaN
      have hx' : n⁻¹ * x * n ∈ X := by
        change ∀ z : G, z ∈ X ↔ n⁻¹ * z * (n⁻¹)⁻¹ ∈ X at hnInvNorm
        simpa [n] using (hnInvNorm x).1 hxX
      refine ⟨(q, ⟨n⁻¹ * x * n, hx'⟩), ?_⟩
      apply Subtype.ext
      calc
        ((f (q, ⟨n⁻¹ * x * n, hx'⟩)).1) = y * x * y⁻¹ := by
          simp [f, q, a, n, mul_assoc]
        _ = z := by simpa using hzy.symm
  have hcardOmega : Nat.card Ω = N.index := by
    calc
      Nat.card Ω = Nat.card (G ⧸ N) := by
        exact Nat.card_congr
          (QuotientGroup.quotientRightRelEquivQuotientLeftRel N)
      _ = N.index := N.index_eq_card.symm
  calc
    Nat.card (section16ConjugatesOfSetBySet X Set.univ) = Nat.card (Ω × X0) := by
      exact Nat.card_congr (Equiv.ofBijective f hfBij).symm
    _ = Nat.card Ω * Nat.card X0 := Nat.card_prod _ _
    _ = Nat.card Ω * Nat.card X := rfl
    _ = Nat.card X * N.index := by rw [hcardOmega, Nat.mul_comm]

public theorem theorem_10_8_conjugatesOfSetBySet_ratio_eq_of_tiNormalizer
    {G : Type u}
    [Group G]
    [Finite G]
    {X : Set G} {N : Subgroup G}
    (hX1 : (1 : G) ∉ X)
    (hXti : section16TISubsetWithNormalizer X N) :
    (((section16ConjugatesOfSetBySet X Set.univ).ncard : ℚ) /
        (Nat.card G : ℚ)) =
      ((X.ncard : ℚ) / (Nat.card N : ℚ)) := by
  rcases hXti with ⟨hTI, hNorm⟩
  have hcard :=
    theorem_10_8_card_conjugatesOfSetBySet_eq_card_mul_index_of_ti
      (X := X) hX1 hTI
  rw [hNorm] at hcard
  have hconjCard :
      ((section16ConjugatesOfSetBySet X Set.univ).ncard : ℚ) =
        (Nat.card X : ℚ) * (Subgroup.index N : ℚ) := by
    rw [← Nat.card_coe_set_eq (section16ConjugatesOfSetBySet X Set.univ),
      hcard]
    norm_num [Nat.cast_mul]
  have hXCard : (X.ncard : ℚ) = (Nat.card X : ℚ) := by
    rw [← Nat.card_coe_set_eq X]
  have hGcard : (Nat.card G : ℚ) =
      (Nat.card N : ℚ) * (Subgroup.index N : ℚ) := by
    exact_mod_cast (Subgroup.card_mul_index (H := N)).symm
  have hNpos : (Nat.card N : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := N)).ne'
  have hIdx : ((Subgroup.index N : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := N))
  rw [hconjCard, hXCard, hGcard]
  field_simp [hNpos, hIdx]

public theorem theorem_10_8_puncturedSubgroupSet_ncard_le_card
    {G : Type u}
    [Group G]
    [Finite G]
    (H : Subgroup G) :
    (Section7.puncturedSubgroupSet H).ncard ≤ Nat.card H := by
  have hsubset : Section7.puncturedSubgroupSet H ⊆ (H : Set G) := by
    intro x hx
    exact hx.1
  have hle := Set.ncard_le_ncard hsubset
  rwa [← Nat.card_coe_set_eq (H : Set G)] at hle

public theorem theorem_10_8_internalDirectProduct_card_mul
    {G : Type u}
    [Group G]
    [Finite G]
    {C H K : Subgroup G}
    (h : Section2.IsInternalDirectProduct C H K) :
    Nat.card C = Nat.card H * Nat.card K := by
  simpa using (Nat.card_congr (Section3.internalDirectProductMulEquiv h).toEquiv).symm

public theorem theorem_10_8_natCard_sup_eq_mul_of_section10_notation
    {G : Type u}
    [Group G]
    [Finite G]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    (hW1M : W1 ≤ M)
    (hW2M : W2 ≤ M)
    (hW12M : W1 ⊔ W2 ≤ M)
    (hW : W = (W1 ⊔ W2).subgroupOf M)
    (h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W) :
    Nat.card (W1 ⊔ W2 : Subgroup G) = Nat.card W1 * Nat.card W2 := by
  have hWcard :
      Nat.card W = Nat.card (W1.subgroupOf M) * Nat.card (W2.subgroupOf M) := by
    rcases h31 with ⟨_hW1, _hW2, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    exact theorem_10_8_internalDirectProduct_card_mul hIP
  have hSupSubCard :
      Nat.card ((W1 ⊔ W2 : Subgroup G).subgroupOf M) =
        Nat.card (W1 ⊔ W2 : Subgroup G) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (H := (W1 ⊔ W2 : Subgroup G)) (K := M) hW12M).toEquiv
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hW2card : Nat.card (W2.subgroupOf M) = Nat.card W2 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).toEquiv
  calc
    Nat.card (W1 ⊔ W2 : Subgroup G) =
        Nat.card ((W1 ⊔ W2 : Subgroup G).subgroupOf M) := hSupSubCard.symm
    _ = Nat.card W := by rw [← hW]
    _ = Nat.card (W1.subgroupOf M) * Nat.card (W2.subgroupOf M) := hWcard
    _ = Nat.card W1 * Nat.card W2 := by rw [hW1card, hW2card]

public theorem theorem_10_8_natCard_section16HatW_eq_of_section10_notation
    {G : Type u}
    [Group G]
    [Finite G]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    (hW1M : W1 ≤ M)
    (hW2M : W2 ≤ M)
    (hW : W = (W1 ⊔ W2).subgroupOf M)
    (h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W) :
    Nat.card (section16HatW W1 W2) =
      (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
  classical
  let e :
      (section16HatW W1 W2) ≃
        (Section3.cyclicTISetSubgroup (W1.subgroupOf M) (W2.subgroupOf M) W) :=
    { toFun := fun x =>
        let xM : M := ⟨x.1, (sup_le hW1M hW2M) x.2.1⟩
        let xW : W := ⟨xM, by
          have hxW : (xM : G) ∈ (W1 ⊔ W2 : Subgroup G) := x.2.1
          simpa [hW, Subgroup.mem_subgroupOf] using hxW⟩
        ⟨xW, by
          change
            (xM : M) ∈
              Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W
          refine ⟨xW.2, ?_⟩
          intro hbad
          rcases hbad with hleft | hright
          · exact x.2.2 (Or.inl (by simpa [Subgroup.mem_subgroupOf] using hleft))
          · exact x.2.2 (Or.inr (by simpa [Subgroup.mem_subgroupOf] using hright))⟩
      invFun := fun y =>
        let xG : G := ((y.1 : W) : M)
        ⟨xG, by
          have hyW : ((y.1 : W) : M) ∈ W := (y.1 : W).2
          have hsup : xG ∈ (W1 ⊔ W2 : Subgroup G) := by
            have hsub : ((y.1 : W) : M) ∈ (W1 ⊔ W2).subgroupOf M := by
              simpa [hW] using hyW
            simpa [xG, Subgroup.mem_subgroupOf] using hsub
          refine ⟨hsup, ?_⟩
          intro hbad
          rcases hbad with hleft | hright
          · exact y.2.2 (Or.inl (by simpa [xG, Subgroup.mem_subgroupOf] using hleft))
          · exact y.2.2 (Or.inr (by simpa [xG, Subgroup.mem_subgroupOf] using hright))⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl }
  have hW1card : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).toEquiv
  have hW2card : Nat.card (W2.subgroupOf M) = Nat.card W2 :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := W2) (K := M) hW2M).toEquiv
  calc
    Nat.card (section16HatW W1 W2) =
        Nat.card
          (Section3.cyclicTISetSubgroup (W1.subgroupOf M) (W2.subgroupOf M) W) :=
      Nat.card_congr e
    _ =
        (Nat.card (W1.subgroupOf M) - 1) *
          (Nat.card (W2.subgroupOf M) - 1) :=
      Section3.cyclicTISetSubgroup_card (W1.subgroupOf M) (W2.subgroupOf M) W h31
    _ = (Nat.card W1 - 1) * (Nat.card W2 - 1) := by
      rw [hW1card, hW2card]


public theorem frobeniusJoin_kernel_card_ge_two_mul_complement_add_one
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    2 * Nat.card R + 1 ≤ Nat.card K := by
  classical
  let L : Subgroup G := K ⊔ R
  let Ksub : Subgroup L := K.subgroupOf L
  let Rsub : Subgroup L := R.subgroupOf L
  have hfrobL : IsFrobeniusGroupWithKernelComplement Ksub Rsub := by
    simpa [section12FrobeniusJoinWithKernel, L, Ksub, Rsub] using hfrob
  have _ : Ksub.Normal := IsFrobeniusGroupWithKernelComplement.normal hfrobL
  have hcent : ∀ r : Rsub, r ≠ 1 → Section2.centralizerIn Ksub (r : L) = ⊥ := by
    intro r hr
    have hcentElem : elementCentralizerIn Ksub (r : L) = ⊥ :=
      (lemma_3_1 Ksub Rsub
        (IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobL)
        (IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobL)
        (IsFrobeniusGroupWithKernelComplement.normal hfrobL)
        (IsFrobeniusGroupWithKernelComplement.isComplement' hfrobL)).1
        hfrobL r hr
    simpa [Section2.centralizerIn, Section2.elementCentralizer, elementCentralizerIn]
      using hcentElem
  have hdvdSub : Nat.card Rsub ∣ Nat.card Ksub - 1 :=
    Section6.frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (Q := L) (K := Ksub) (R := Rsub) (N := Ksub) le_rfl hcent
  have hKcard : Nat.card Ksub = Nat.card K :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := L) le_sup_left).toEquiv
  have hRcard : Nat.card Rsub = Nat.card R :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := R) (K := L) le_sup_right).toEquiv
  have hdvd : Nat.card R ∣ Nat.card K - 1 := by
    rw [← hKcard, ← hRcard]
    exact hdvdSub
  have hKodd : Odd (Nat.card K) :=
    Odd.of_dvd_nat IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card K)
  have hRodd : Odd (Nat.card R) :=
    Odd.of_dvd_nat IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card R)
  have hKsub_gt : 1 < Nat.card Ksub :=
    (Subgroup.one_lt_card_iff_ne_bot Ksub).2
      (IsFrobeniusGroupWithKernelComplement.kernel_ne_bot hfrobL)
  have hKgt : 1 < Nat.card K := by
    rw [← hKcard]
    exact hKsub_gt
  rcases hdvd with ⟨k, hk⟩
  have hKminus_pos : 0 < Nat.card K - 1 := Nat.sub_pos_of_lt hKgt
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : Nat.card K - 1 = 0 := by
      simpa [hk0] using hk
    exact (Nat.ne_of_gt hKminus_pos) hzero
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    rcases hKodd with ⟨m, hm⟩
    rcases hRodd with ⟨n, hn⟩
    subst k
    omega
  have hk_ge_two : 2 ≤ k := by omega
  have hleR : 2 * Nat.card R ≤ Nat.card R * k := by
    calc
      2 * Nat.card R = Nat.card R * 2 := by rw [Nat.mul_comm]
      _ ≤ Nat.card R * k := Nat.mul_le_mul_left (Nat.card R) hk_ge_two
  have hle : 2 * Nat.card R ≤ Nat.card K - 1 := hleR.trans_eq hk.symm
  omega

public theorem frobeniusJoin_complement_ne_bot
    {G : Type u}
    [Group G]
    [Finite G]
    {K R : Subgroup G}
    (hfrob : section12FrobeniusJoinWithKernel K R) :
    R ≠ ⊥ := by
  intro hRbot
  let L : Subgroup G := K ⊔ R
  let Rsub : Subgroup L := R.subgroupOf L
  have hfrobL :
      IsFrobeniusGroupWithKernelComplement (K.subgroupOf L) Rsub := by
    simpa [section12FrobeniusJoinWithKernel, L, Rsub] using hfrob
  have hRsubBot : Rsub = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxR : (x : G) ∈ R := by
        simpa [Rsub, Subgroup.mem_subgroupOf, L] using hx
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hRbot] using hxR
      ext
      simpa using hxBot
    · exact bot_le
  exact IsFrobeniusGroupWithKernelComplement.complement_ne_bot hfrobL hRsubBot

public theorem typePDefinitionData_frobeniusJoinWithKernel
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hUne : U ≠ ⊥) :
    section12FrobeniusJoinWithKernel U W1 := by
  classical
  rcases hP with
    ⟨_hMF, _hW1cyc, hW1ne, _hW1Hall, hMcomp, _hUleD, _hUnil, hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2leInf, _hW2cyc,
      _hW2ne, hcentralizer, _hnorm⟩
  rcases hDercomp with ⟨_hMFleD, hUleD, _hD_eq, hMFUdisj⟩
  let S : Subgroup G := U ⊔ W1
  have hDdisjW1 : Disjoint (ambientDerivedSubgroup M) W1 := hMcomp.2.2.2
  have hUWdisj : Disjoint U W1 := by
    rw [disjoint_iff] at hDdisjW1 ⊢
    apply le_antisymm
    · exact (inf_le_inf_right W1 hUleD).trans (le_of_eq hDdisjW1)
    · exact bot_le
  have hW1leNormU : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).1
  have hUnormalS : (U.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := U) (K := S) (by simp [S])).2
    simpa [S] using sup_le Subgroup.le_normalizer hW1leNormU
  have hUWdisjSub : Disjoint (U.subgroupOf S) (W1.subgroupOf S) := by
    rw [disjoint_iff] at hUWdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ U ⊓ W1 := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, S] using hx.1,
          by simpa [Subgroup.mem_subgroupOf, S] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hUWdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hUWsupTop :
      U.subgroupOf S ⊔ W1.subgroupOf S = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := U) (A' := W1) (B := S)
      (by simp [S]) (by simp [S])]
    exact Subgroup.subgroupOf_eq_top.2 (by simp [S])
  have hUWcompSub : (U.subgroupOf S).IsComplement' (W1.subgroupOf S) := by
    let _ : (U.subgroupOf S).Normal := hUnormalS
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (U.subgroupOf S) (W1.subgroupOf S) hUWdisjSub hUWsupTop
  have hUsub_ne : U.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hUne
    have hcard :
        Nat.card (U.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := U.subgroupOf S)).1 hbot
    have hcardU : Nat.card U = 1 := by
      rw [natCard_subgroupOf_eq U S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := U)).2 hcardU
  have hW1sub_ne : W1.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hW1ne
    have hcard :
        Nat.card (W1.subgroupOf S) = 1 :=
      (Subgroup.eq_bot_iff_card (H := W1.subgroupOf S)).1 hbot
    have hcardW1 : Nat.card W1 = 1 := by
      rw [natCard_subgroupOf_eq W1 S (by simp [S])] at hcard
      exact hcard
    exact (Subgroup.eq_bot_iff_card (H := W1)).2 hcardW1
  have hcent :
      ∀ x : W1.subgroupOf S, x ≠ 1 →
        elementCentralizerIn (U.subgroupOf S) (x : S) = ⊥ := by
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have hyParts :
        y ∈ U.subgroupOf S ∧
          y ∈ Subgroup.centralizer ({(x : S)} : Set S) := by
      simpa [elementCentralizerIn] using hy
    let xG : G := ((x : S) : G)
    have hxW1 : xG ∈ W1 := by
      simpa [xG] using (Subgroup.mem_subgroupOf.mp x.property : ((x : S) : G) ∈ W1)
    have hxGne : xG ≠ 1 := by
      intro hxG
      apply hxne
      ext
      exact hxG
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf, S] using hyParts.1
    have hyDer : (y : G) ∈ ambientDerivedSubgroup M := hUleD hyU
    have hcentx : elementCentralizerIn (ambientDerivedSubgroup M) xG = W2 :=
      hcentralizer xG hxW1 hxGne
    have hyCommS : (y : S) * (x : S) = (x : S) * (y : S) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyParts.2
    have hyCommG : (y : G) * xG = xG * (y : G) := by
      simpa [xG] using congrArg Subtype.val hyCommS
    have hyCentX : (y : G) ∈ Subgroup.centralizer ({xG} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = xG := by simpa using hz
      subst z
      exact hyCommG.symm
    have hyElem : (y : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) xG := by
      simpa [elementCentralizerIn] using And.intro hyDer hyCentX
    have hyW2 : (y : G) ∈ W2 := by
      simpa [hcentx] using hyElem
    have hyMF : (y : G) ∈ MF := (hW2leInf hyW2).1
    have hyBot : (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hMFUdisj) hyMF hyU
    ext
    simpa using hyBot
  exact (lemma_3_1 (G := S) (K := U.subgroupOf S) (R := W1.subgroupOf S)
    hUsub_ne hW1sub_ne hUnormalS hUWcompSub).2 hcent

public theorem typePData_of_typePDefinitionData
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hP : Section8.typePDefinitionData M MF U W1 W2) :
    Section8.typePData M MF U W1 W2 := by
  have hT6 :=
    Section8.sourceTypeP_T6_of_source_typeP hM hMF hP
  exact ⟨hMF, Section8.section16TypeCommon_of_source_typeP_with_T6 hP hT6⟩



end Section10
