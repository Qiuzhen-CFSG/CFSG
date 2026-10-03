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
public import FeitThompson.PFsection10.PFsection10_foundations
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

public theorem exists_ne_base_column_of_hypothesis_10_4_supported_data_local
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ) :
    ∃ j : J, j ≠ j0 := by
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
    ⟨_hI, hJ, hPrime, _hdpos, _hδ, _hnpos, _hdeg, _hsign, _hdn⟩
  have hJcard : Fintype.card J = Nat.card W2 := by
    simpa [Nat.card_eq_fintype_card] using hJ
  have hJgt : 1 < Fintype.card J := by
    simpa [hJcard] using hPrime.one_lt
  exact Fintype.exists_ne_of_one_lt_card hJgt j0

public theorem muColumn_mem_of_hypothesis_10_4_supported_data_local
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    muColumn μ j ∈ S := by
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h
  have hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ :=
    section10FourSixNotation_of_hypothesis_10_4_supported_data h
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

public theorem degree_muColumn_of_hypothesis_10_4_supported_data_local
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section1.degree (muColumn μ j) = (d : ℂ) * (Nat.card W1 : ℂ) := by
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
    ⟨hI, _hJ, _hPrime, _hdpos, _hδ, _hnpos, hdeg, _hsign, _hdn⟩
  calc
    Section1.degree (muColumn μ j) = ∑ i : I, μ i j 1 := by
      simp [Section1.degree, muColumn]
    _ = ∑ _i : I, (d : ℂ) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simpa [Section1.degree] using hdeg i j hj
    _ = (Fintype.card I : ℂ) * (d : ℂ) := by simp
    _ = (Nat.card W1 : ℂ) * (d : ℂ) := by
      rw [← Nat.card_eq_fintype_card, hI]
    _ = (d : ℂ) * (Nat.card W1 : ℂ) := by ring

public theorem muColumn_sub_smul_xi_integerSpanOn_of_hypothesis_10_4_supported_data_local
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section5.integerSpanOn S Section5.puncturedSet (muColumn μ j - (d : ℂ) • ξ) := by
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨_h10, _hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  have hcolS : muColumn μ j ∈ S :=
    muColumn_mem_of_hypothesis_10_4_supported_data_local h hj
  have hspan_col : Section5.integerSpan S (muColumn μ j) := integerSpan_of_mem S hcolS
  have hspan_xi : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
  have hspan_dxi : Section5.integerSpan S ((d : ℂ) • ξ) := by
    simpa using integerSpan_int_smul (S := S) (φ := ξ) (z := (d : ℤ)) hspan_xi
  have hspan : Section5.integerSpan S (muColumn μ j - (d : ℂ) • ξ) :=
    integerSpan_sub hspan_col hspan_dxi
  have hsupp :
      Section1.supportedOn (muColumn μ j - (d : ℂ) • ξ) Section5.puncturedSet := by
    apply (supportedOn_puncturedSet_iff_degree_eq_zero (muColumn μ j - (d : ℂ) • ξ)).2
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_supported_data_local h hj
    have hcol1 : muColumn μ j 1 = (d : ℂ) * (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hcoldeg
    have hxi1 : ξ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hξDegree
    rw [Section1.degree]
    simp [Pi.sub_apply, Pi.smul_apply, hcol1, hxi1]
  exact ⟨hspan, hsupp⟩

public theorem tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_supported_data_local
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    τ₁ (muColumn μ j - (d : ℂ) • ξ) = τ (muColumn μ j - (d : ℂ) • ξ) := by
  have hExt := coherentExtension_of_hypothesis_10_4_supported_data h
  exact hExt.2.2 (muColumn μ j - (d : ℂ) • ξ)
    (muColumn_sub_smul_xi_integerSpanOn_of_hypothesis_10_4_supported_data_local h hj)

public theorem theorem_4_10_of_section10FourSixNotationSupportedData_local
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

public theorem supportedOn_sub_local
    {G : Type*} [Group G]
    {A : Set G} {f g : Section1.ClassFunction G}
    (hf : Section1.supportedOn f A)
    (hg : Section1.supportedOn g A) :
    Section1.supportedOn (f - g) A := by
  rw [Section1.supportedOn_iff] at hf hg ⊢
  intro x hx
  simp [hf x hx, hg x hx]

public theorem supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
    {G : Type u} [Group G] [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    {χ : Section1.ClassFunction M} (hχ : χ ∈ S) :
    Section1.supportedOn χ ((derivedSubgroup M : Subgroup M) : Set M) := by
  rcases h10 with
    ⟨_hM, _hType, hS, _hW1M, _hW2M, _hW12M, _hDade, _h46base,
      _hNotation10, _h52⟩
  rcases (hS χ).mp hχ with ⟨θ, _hθIrr, _hθNe, hχeq⟩
  rw [hχeq]
  exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ

public theorem supportedOn_primeDadeA0_of_supportedOn_derivedSubgroup_degree_zero
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
    (_hNotation : section10FourSixNotationSupportedData M W1 W2 W A A0
      i0 j0 μ δSign ω σ τ)
    (h46 : Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
      (derivedSubgroup M) A)
    {f : Section1.ClassFunction M}
    (hfClass : Section1.IsClassFunction f)
    (hfDerived :
      Section1.supportedOn f ((derivedSubgroup M : Subgroup M) : Set M))
    (hfDegree : Section1.degree f = 0) :
    Section1.supportedOn f
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  have hfA0 :
      Section1.supportedOn f
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    apply supportedOn_of_degree_eq_zero_of_punctured_subset _ hfDegree
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46
  have hSemi := h46.1.1
  have hfW1 : ∀ x : M, x ∈ W1.subgroupOf M → f x = 0 := by
    intro x hxW1
    by_cases hx1 : x = 1
    · subst x
      simpa [Section1.degree] using hfDegree
    · apply (Section1.supportedOn_iff.mp hfDerived) x
      intro hxDerived
      have hxInf : x ∈ derivedSubgroup M ⊓ W1.subgroupOf M :=
        ⟨hxDerived, hxW1⟩
      rw [hSemi.inf_eq_bot] at hxInf
      exact hx1 (Subgroup.mem_bot.mp hxInf)
  exact
    Section4Scratch.supportedOn_primeDadeA0Set_of_supportedOn_a0Set_of_vanishesOn_W1
      (W1.subgroupOf M) (W2.subgroupOf M) W A hfClass hfA0 hfW1

public theorem alphaChar_supportedOn_primeDadeA0_of_bridge_data
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {n : ℕ} {δ : ℤ}
    (hNotation : section10FourSixNotationSupportedData M W1 W2 W A A0
      i0 j0 μ δSign ω σ τ)
    (h46 : Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
      (derivedSubgroup M) A)
    (hξIrr : Section1.IsIrreducibleCharacterOnGroup ξ)
    (hξDerived :
      Section1.supportedOn ξ ((derivedSubgroup M : Subgroup M) : Set M))
    {i : I} {j : J}
    (hdegreeAlpha : Section1.degree (alphaChar μ ξ n δ j0 i j) = 0)
    (hδj : (δSign j : ℂ) = (δ : ℂ)) :
    Section1.supportedOn (alphaChar μ ξ n δ j0 i j)
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  classical
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, _hA0, _h46Selected, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
      _h45, _h48, _hTauA0, hFull⟩
  rcases hFull with ⟨σM, _xChar, _H_A, _H_A0, hSupported, _hGalois⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIsoFull, _hVirtFull, _hClassFull,
      _hPrinFull, _h22A, hRest⟩
  rcases hRest with
    ⟨_hωFull, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc,
      _hTauA0Full, _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hμClass : ∀ r k, Section1.IsClassFunction (μ r k) := fun r k =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (h43b.2.2.1 r k))
  have hξClass : Section1.IsClassFunction ξ :=
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
  have hαClass : Section1.IsClassFunction (alphaChar μ ξ n δ j0 i j) := by
    intro x g
    simp [alphaChar, hμClass i j x g, hμClass i j0 x g, hξClass x g]
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i j)
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    apply supportedOn_of_degree_eq_zero_of_punctured_subset _ hdegreeAlpha
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46
  rcases h46.1 with
    ⟨hSemi, _hHall, _hW1cyc, _hW1ne, _hW2cyc, _hW2ne, _hCentralizer,
      hW1W, _hW2W, hDirect, _hWodd⟩
  have hδ0 : (δSign j0 : ℂ) = 1 :=
    (Section4.proposition_4_4_base
      (W1.subgroupOf M) (W2.subgroupOf M) W I J i0 j0 ω σM μ
        (fun k => (δSign k : ℂ)) hω h43b).1
  have hαW1 :
      ∀ x : M, x ∈ W1.subgroupOf M → alphaChar μ ξ n δ j0 i j x = 0 := by
    intro x hxW1
    by_cases hx1 : x = 1
    · subst x
      simpa [Section1.degree] using hdegreeAlpha
    · have hxNotDerived : x ∉ derivedSubgroup M := by
        intro hxDerived
        have hxInf : x ∈ derivedSubgroup M ⊓ W1.subgroupOf M :=
          ⟨hxDerived, hxW1⟩
        rw [hSemi.inf_eq_bot] at hxInf
        exact hx1 (Subgroup.mem_bot.mp hxInf)
      have hξzero : ξ x = 0 :=
        (Section1.supportedOn_iff.mp hξDerived) x hxNotDerived
      have hxW : x ∈ W := hW1W hxW1
      have hxNotW2 : x ∉ W2.subgroupOf M := by
        intro hxW2
        have hxInf : x ∈ W1.subgroupOf M ⊓ W2.subgroupOf M :=
          ⟨hxW1, hxW2⟩
        rw [hDirect.inf_eq_bot] at hxInf
        exact hx1 (Subgroup.mem_bot.mp hxInf)
      have hxMinus : x ∈ ((W : Set M) \ (W2.subgroupOf M : Set M)) :=
        ⟨hxW, hxNotW2⟩
      let xW : W := ⟨x, hxW⟩
      have hωright : ω i0 j xW = 1 := by
        have hker := hω.right_kernel j ⟨xW, hxW1⟩
        simpa [hω.degree_one i0 j] using hker
      have hωeq : ω i j xW = ω i j0 xW := by
        rw [hω.product i j xW, hωright]
        ring
      have hμj : μ i j x = (δ : ℂ) * ω i j xW := by
        simpa [xW, hδj] using h43c.1 i j x hxMinus
      have hμ0 : μ i j0 x = ω i j0 xW := by
        simpa [xW, hδ0] using h43c.1 i j0 x hxMinus
      simp [alphaChar, hμj, hμ0, hξzero, hωeq]
  exact
    Section4Scratch.supportedOn_primeDadeA0Set_of_supportedOn_a0Set_of_vanishesOn_W1
      (W1.subgroupOf M) (W2.subgroupOf M) W A hαClass hαA0 hαW1


public theorem alphaChar_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    {i : I} {j : J} (hj : j ≠ j0) :
    Section1.supportedOn (alphaChar μ ξ n δ j0 i j)
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  classical
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨h10, hNotation, hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, _hδsign, _hnpos, hdeg, hsign, hdn⟩
  have hNotationAll := hNotation
  rcases hNotation with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
      _hW, hA0, h46, hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc,
      _h45, _h48, _hTauA0, hFull⟩
  rcases hFull with ⟨σM, _xChar, _H_A, _H_A0, hSupported, _hGalois⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIsoFull, _hVirtFull, _hClassFull,
      _hPrinFull, _h22A, hRest⟩
  rcases hRest with
    ⟨_hωFull, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc,
      _hTauA0Full, _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hdegreeAlpha :
      Section1.degree (alphaChar μ ξ n δ j0 i j) = 0 := by
    have hbase : Section1.degree (μ i j0) = 1 :=
      Section4.proposition_4_4_baseColumn_degree_one
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
        (deltaSign := fun k => (δSign k : ℂ))
        h46.1 hω h43b h43c i
    have hdnC : (d : ℂ) = (n : ℂ) * (Nat.card W1 : ℂ) + (δ : ℂ) := by
      exact_mod_cast hdn
    have hdegApply : μ i j 1 = (d : ℂ) := by
      simpa [Section1.degree] using hdeg i j hj
    have hbaseApply : μ i j0 1 = (1 : ℂ) := by
      simpa [Section1.degree] using hbase
    have hξApply : ξ 1 = (Nat.card W1 : ℂ) := by
      simpa [Section1.degree] using hξDegree
    unfold alphaChar Section1.degree
    simp [hdegApply, hbaseApply, hξApply, hdnC]
  have hξDerived :=
    supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
      h10 hξS
  have hδj : (δSign j : ℂ) = (δ : ℂ) := by
    exact_mod_cast hsign j hj
  exact alphaChar_supportedOn_primeDadeA0_of_bridge_data
    hNotationAll
      (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data
        h10 hNotationAll)
      hξIrr hξDerived hdegreeAlpha hδj

public theorem muColumn_sub_smul_xi_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {W : Subgroup M}
    {A A0 : Set M}
    {S : Finset (Section1.ClassFunction M)}
    {τ τ₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {ξ : Section1.ClassFunction M}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section1.supportedOn (muColumn μ j - (d : ℂ) • ξ)
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨h10, hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  have hcolS : muColumn μ j ∈ S :=
    muColumn_mem_of_hypothesis_10_4_supported_data_local h hj
  have hcolDerived :=
    supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
      h10 hcolS
  have hξDerived :=
    supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data_local
      h10 hξS
  have hsmulDerived :
      Section1.supportedOn ((d : ℂ) • ξ)
        ((derivedSubgroup M : Subgroup M) : Set M) := by
    rw [Section1.supportedOn_iff] at hξDerived ⊢
    intro x hx
    simp [hξDerived x hx]
  have hdiffDerived :
      Section1.supportedOn (muColumn μ j - (d : ℂ) • ξ)
        ((derivedSubgroup M : Subgroup M) : Set M) :=
    supportedOn_sub_local hcolDerived hsmulDerived
  have hdiffClass :
      Section1.IsClassFunction (muColumn μ j - (d : ℂ) • ξ) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    have hμClass : ∀ i k, Section1.IsClassFunction (μ i k) := fun i k =>
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          (h43b.2.2.1 i k))
    have hcolClass : Section1.IsClassFunction (muColumn μ j) := by
      intro x g
      unfold muColumn
      simpa using Finset.sum_congr rfl (fun i _hi => hμClass i j x g)
    have hξClass : Section1.IsClassFunction ξ :=
      Section1.isVirtualCharacter_isClassFunction
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr)
    intro x g
    simp [hcolClass x g, hξClass x g]
  have hdiffDegree :
      Section1.degree (muColumn μ j - (d : ℂ) • ξ) = 0 :=
    (supportedOn_puncturedSet_iff_degree_eq_zero
      (muColumn μ j - (d : ℂ) • ξ)).1
        (muColumn_sub_smul_xi_integerSpanOn_of_hypothesis_10_4_supported_data_local
          h hj).2
  exact supportedOn_primeDadeA0_of_supportedOn_derivedSubgroup_degree_zero
    hNotation
      (hypothesis_4_6_derived_of_hypothesis_10_1_supported_data h10 hNotation)
      hdiffClass hdiffDerived hdiffDegree

public theorem alphaChar_corrected_tau_isVirtualCharacter_of_hypothesis_10_4_supported_source
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    IsVirtualCharacter
      (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) := by
  classical
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨_h10, _hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, hdeg, _hsign, hdn⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1
  have hαvirt :
      IsVirtualCharacter (alphaChar μ ξ n δ j0 i0 j) := by
    have hentry :
        IsVirtualCharacter (μ i0 j) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμirr i0 j)
    have hbase :
        IsVirtualCharacter (μ i0 j0) :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hμirr i0 j0)
    have hξ :
        IsVirtualCharacter ξ :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hξIrr
    have hδbase :
        IsVirtualCharacter ((δ : ℂ) • μ i0 j0) :=
      isVirtualCharacter_intCast_smul_sec10_base δ hbase
    have hnξ :
        IsVirtualCharacter ((n : ℂ) • ξ) :=
      isVirtualCharacter_natCast_smul_sec10_base n hξ
    simpa [alphaChar] using
      Section3.isVirtualCharacter_sub
        (Section3.isVirtualCharacter_sub hentry hδbase) hnξ
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    alphaChar_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
      h hj
  have hτvirt :
      Section4Scratch.tau_maps_primeDadeA0_to_virtual_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, hτvirt, _hPF39⟩
    exact hτvirt
  exact Section3.isVirtualCharacter_add
    (hτvirt (alphaChar μ ξ n δ j0 i0 j) hαvirt hαA0)
    (isVirtualCharacter_natCast_smul_sec10_base n
      (tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_supported_data h))

public theorem alphaChar_scalarProduct_self_of_hypothesis_10_4_supported_source
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
      i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M
        (alphaChar μ ξ n δ j0 i j)
        (alphaChar μ ξ n δ j0 i j) =
      (2 : ℂ) + (n : ℂ) ^ 2 := by
  classical
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases h104a with
    ⟨h10, _hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, hnpos, hdeg, _hsign, hdn⟩
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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
        (1 : ℂ) = Section1.degree (μ i j0) := by
          rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
            ⟨σM, _xChar, _H_A, _H_A0, hSupported'⟩
          rcases hSupported' with
            ⟨h46', _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
              hRest'⟩
          rcases hRest' with
            ⟨hω, h43b', h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
              _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
          exact (Section4.proposition_4_4_baseColumn_degree_one
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
            h46'.1 hω h43b' h43c i).symm
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

public theorem alphaChar_tau_cfNormSq_of_hypothesis_10_4_supported_source
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
      i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section5.cfNormSq (τ (alphaChar μ ξ n δ j0 i j)) =
      (2 : ℝ) + (n : ℝ) ^ 2 := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have hαvirt :
      IsVirtualCharacter (alphaChar μ ξ n δ j0 i j) := by
    have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
    rcases h104a with ⟨_h10, _hNotation, _hξS, hξIrr, _hξDegree, _hUniform⟩
    have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
      rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
        ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
      rcases hSupported with
        ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
      rcases hRest with
        ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
          _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    alphaChar_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
      h hj
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hself :
      Section1.scalarProduct G
          (τ (alphaChar μ ξ n δ j0 i j))
          (τ (alphaChar μ ξ n δ j0 i j)) =
        (2 : ℂ) + (n : ℂ) ^ 2 := by
    have hαClass : Section1.IsClassFunction (alphaChar μ ξ n δ j0 i j) :=
      Section1.isVirtualCharacter_isClassFunction hαvirt
    rw [hτiso (alphaChar μ ξ n δ j0 i j)
      (alphaChar μ ξ n δ j0 i j) hαClass hαClass hαA0 hαA0]
    exact alphaChar_scalarProduct_self_of_hypothesis_10_4_supported_source h hj
  unfold Section5.cfNormSq
  rw [hself]
  simp [pow_two]

public theorem alphaChar_tau_plus_tauOne_xi_pairing_integral_of_hypothesis_10_4_supported_source
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    ∃ a : ℤ,
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ) := by
  have hYvirt :
      IsVirtualCharacter
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) :=
    alphaChar_corrected_tau_isVirtualCharacter_of_hypothesis_10_4_supported_source h hj
  have hξτvirt :
      IsVirtualCharacter (τ₁ ξ) :=
    tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_supported_data h
  exact Section3.scalarProduct_isVirtualCharacter_eq_int hYvirt hξτvirt

public theorem baseColumn_degree_one_of_section10FourSixNotationSupportedData_pairing
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

public theorem scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    (i : I) (j k : J) :
    Section1.scalarProduct M (μ i j) (muColumn μ k) =
      if j = k then 1 else 0 := by
  classical
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
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

public theorem alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) ξ = -(n : ℂ) := by
  classical
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, hnpos, hdeg, _hsign, hdn⟩
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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
          (baseColumn_degree_one_of_section10FourSixNotationSupportedData_pairing
            hNotation i).symm
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

public theorem alphaChar_scalarProduct_muColumn_eq_zero_of_ne_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
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
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_pairing h i j k
  have hbase :
      Section1.scalarProduct M (μ i j0) (muColumn μ k) = 0 := by
    simpa [hk.symm] using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_pairing h i j0 k
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, _hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hcolS : muColumn μ k ∈ S := muColumn_mem_of_hypothesis_10_4_supported_data_local h hk
  have hne : ξ ≠ muColumn μ k := by
    intro hEq
    have hdegEq :
        Section1.degree (muColumn μ k) = Section1.degree ξ := by
      rw [← hEq]
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_supported_data_local h hk
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
  rcases hypothesis_5_2_of_hypothesis_10_1_supported_data h10 with
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


public theorem alphaChar_isVirtualCharacter_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    (i : I) (j : J) :
    IsVirtualCharacter (alphaChar μ ξ n δ j0 i j) := by
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨_h10, hNotation, _hξS, hξIrr, _hξDegree, _hUniform⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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

public theorem alphaChar_tau_scalarProduct_tauOne_xi_eq_sub_of_pairing_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
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
    tauOne_xi_scalarProduct_self_of_hypothesis_10_4_supported_data h
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


public theorem alphaChar_scalarProduct_muColumn_sub_smul_xi_eq_d_mul_n_supported
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
      i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j k : J}
    (hj : j ≠ j0)
    (hk : k ≠ j0)
    (hjk : j ≠ k) :
    Section1.scalarProduct M
      (alphaChar μ ξ n δ j0 i j)
      (muColumn μ k - (d : ℂ) • ξ) = (d : ℂ) * (n : ℂ) := by
  have hcol :
      Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) (muColumn μ k) = 0 :=
    alphaChar_scalarProduct_muColumn_eq_zero_of_ne_of_hypothesis_10_4_supported_pairing
      h hj hk hjk
  have hxi :
      Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) ξ = -(n : ℂ) :=
    alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_supported_pairing h hj
  rw [Section5.scalarProduct_sub_right, Section1.scalarProduct_smul_right, hcol, hxi]
  simp

public theorem alphaChar_tau_scalarProduct_tauOne_muColumn_eq_d_mul_of_pairing_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
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
  let diff : Section1.ClassFunction M := muColumn μ k - (d : ℂ) • ξ
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have hαA0 :
      Section1.supportedOn α
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    simpa [α] using
      alphaChar_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
        h hj
  have hdiffA0 :
      Section1.supportedOn diff
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    simpa [diff] using
      muColumn_sub_smul_xi_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
        h hk
  have hαClass : Section1.IsClassFunction α :=
    Section1.isVirtualCharacter_isClassFunction
      (by
        simpa [α] using
          alphaChar_isVirtualCharacter_of_hypothesis_10_4_supported_pairing h i0 j)
  have hdiffClass : Section1.IsClassFunction diff := by
    rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
      ⟨_h10, hNotation', _hξS, hξIrr, _hξDegree, _hUniform⟩
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation' with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
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
    have hsmulClass : Section1.IsClassFunction ((d : ℂ) • ξ) :=
      Section1.isClassFunction_smul (d : ℂ) ξ hξClass
    intro x g
    simp [diff, hcolClass x g, hsmulClass x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hsource :
      Section1.scalarProduct M α diff = (d : ℂ) * (n : ℂ) := by
    simpa [α, diff] using
      alphaChar_scalarProduct_muColumn_sub_smul_xi_eq_d_mul_n_supported h hj hk hjk
  have htarget :
      Section1.scalarProduct G (τ α) (τ₁ diff) = (d : ℂ) * (n : ℂ) := by
    have hagree : τ₁ diff = τ diff := by
      simpa [diff] using
        tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_supported_data_local h hk
    rw [hagree]
    exact (hτiso α diff hαClass hdiffClass hαA0 hdiffA0).trans hsource
  have hsplit :
      Section1.scalarProduct G (τ α) (τ₁ diff) =
        Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) -
          (d : ℂ) *
            Section1.scalarProduct G (τ α) (τ₁ ξ) := by
    dsimp [diff]
    rw [map_sub, map_smul, Section5.scalarProduct_sub_right,
      Section1.scalarProduct_smul_right]
    simp
  have hxi :
      Section1.scalarProduct G (τ α) (τ₁ ξ) = (a : ℂ) - (n : ℂ) := by
    simpa [α] using
      alphaChar_tau_scalarProduct_tauOne_xi_eq_sub_of_pairing_supported h hj ha
  have htmp :
      Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) -
          (d : ℂ) * ((a : ℂ) - (n : ℂ)) = (d : ℂ) * (n : ℂ) := by
    simpa [hsplit, hxi] using htarget
  calc
    Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) =
        (Section1.scalarProduct G (τ α) (τ₁ (muColumn μ k)) -
          (d : ℂ) * ((a : ℂ) - (n : ℂ))) +
          (d : ℂ) * ((a : ℂ) - (n : ℂ)) := by ring
    _ = (d : ℂ) * (n : ℂ) + (d : ℂ) * ((a : ℂ) - (n : ℂ)) := by rw [htmp]
    _ = (d : ℂ) * (a : ℂ) := by ring

public theorem muColumn_scalarProduct_self_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
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
  simpa using
    scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_pairing h i k k

public theorem tauOne_muColumn_cfNormSq_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    {k : J}
    (hk : k ≠ j0) :
    Section5.cfNormSq (τ₁ (muColumn μ k)) = (Fintype.card I : ℝ) := by
  have hcolS : muColumn μ k ∈ S := muColumn_mem_of_hypothesis_10_4_supported_data_local h hk
  have hspanCol : Section5.integerSpan S (muColumn μ k) :=
    integerSpan_of_mem S hcolS
  have hself :
      Section1.scalarProduct G (τ₁ (muColumn μ k)) (τ₁ (muColumn μ k)) =
        (Fintype.card I : ℂ) := by
    calc
      Section1.scalarProduct G (τ₁ (muColumn μ k)) (τ₁ (muColumn μ k)) =
          Section1.scalarProduct M (muColumn μ k) (muColumn μ k) :=
        (extensionInterfaces_of_hypothesis_10_4_supported_data h).1
          (muColumn μ k) (muColumn μ k) hspanCol hspanCol
      _ = (Fintype.card I : ℂ) :=
        muColumn_scalarProduct_self_of_hypothesis_10_4_supported_pairing h k
  unfold Section5.cfNormSq
  rw [hself]
  simp

public theorem alphaChar_tau_muColumn_pairing_normSq_le_of_hypothesis_10_4_supported_pairing
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
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
    alphaChar_tau_scalarProduct_tauOne_muColumn_eq_d_mul_of_pairing_supported
      h hj hk hjk ha
  have hle :=
    scalarProduct_normSq_le_cfNormSq_mul
      (G := G)
      (τ (alphaChar μ ξ n δ j0 i0 j))
      (τ₁ (muColumn μ k))
  rw [hpair,
    alphaChar_tau_cfNormSq_of_hypothesis_10_4_supported_source h hj,
    tauOne_muColumn_cfNormSq_of_hypothesis_10_4_supported_pairing h hk] at hle
  simpa using hle

public theorem mu_entry_irreducible_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    (i : I) (j : J) :
    Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  exact h43b.2.2.1 i j

public theorem even_n_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    Even n := by
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, _hnpos, hdeg, _hsign, hdn⟩
  have hoddM : Odd (Nat.card M) :=
    odd_card_M_of_hypothesis_10_4_supported_data h
  have hdodd : Odd d :=
    odd_degree_nat_of_irreducible_of_odd_card_pf105 hoddM
      (mu_entry_irreducible_of_hypothesis_10_4_supported_pairing h i0 j)
      (hdeg i0 j hj)
  exact even_n_of_odd_degree_uniform_pf105
    (odd_card_W1_of_hypothesis_10_4_supported_data h) hdodd hδ hdn

public theorem exists_other_nonbase_column_of_hypothesis_10_4_supported_pairing
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
      i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    ∃ k : J, k ≠ j0 ∧ k ≠ j := by
  classical
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
  have hcard : 3 ≤ Nat.card (W2.subgroupOf M) :=
    Section3.natCard_right_ge_three_of_hypothesis_3_1 h31
  exact Section3.exists_other_col_ne_base_of_card_right_ge_three
    (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M) (W := W)
    (i0 := i0) (j0 := j0) (ω := ω) hω hj hcard

public theorem alphaChar_tau_pairing_coefficient_eq_zero_of_hypothesis_10_4_supported_source
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0)
    (ha :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
        (τ₁ ξ) = (a : ℂ)) :
    a = 0 := by
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
    ⟨hI, _hJ, _hPrime, _hdpos, hδ, hnpos, _hdeg, _hsign, hdn⟩
  rcases exists_other_nonbase_column_of_hypothesis_10_4_supported_pairing h hj with
    ⟨k, hk, hkj⟩
  have hle :=
    alphaChar_tau_muColumn_pairing_normSq_le_of_hypothesis_10_4_supported_pairing
      h hj hk hkj.symm ha
  have hleW :
      Complex.normSq ((d : ℂ) * (a : ℂ)) ≤
        ((2 : ℝ) + (n : ℝ) ^ 2) * (Nat.card W1 : ℝ) := by
    have hcardIR : (Fintype.card I : ℝ) = (Nat.card W1 : ℝ) := by
      exact_mod_cast (by simpa [Nat.card_eq_fintype_card] using hI)
    simpa [hcardIR] using hle
  exact coefficient_eq_zero_of_even_uniform_cauchy_bound_pf105
    (card_W1_ge_three_of_hypothesis_10_4_supported_data h)
    hnpos
    (even_n_of_hypothesis_10_4_supported_pairing h hj)
    hδ
    hdn
    hleW

public theorem alphaChar_corrected_tau_pairing_eq_zero_of_hypothesis_10_4_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (_hj : j ≠ j0) :
    Section1.scalarProduct G
      (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
      (τ₁ ξ) = 0 := by
  rcases alphaChar_tau_plus_tauOne_xi_pairing_integral_of_hypothesis_10_4_supported_source
      _h _hj with
    ⟨a, ha⟩
  have ha0 : a = 0 :=
    alphaChar_tau_pairing_coefficient_eq_zero_of_hypothesis_10_4_supported_source
      _h _hj ha
  simpa [ha0] using ha

public theorem alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (_hj : j ≠ j0) :
    Section5.cfNormSq
      (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) = 2 := by
  let Aτ : Section1.ClassFunction G := τ (alphaChar μ ξ n δ j0 i0 j)
  let Z : Section1.ClassFunction G := τ₁ ξ
  let Y : Section1.ClassFunction G := Aτ + (n : ℂ) • Z
  have hYZ : Section1.scalarProduct G Y Z = 0 := by
    dsimp [Y, Z, Aτ]
    exact alphaChar_corrected_tau_pairing_eq_zero_of_hypothesis_10_4_supported_source
      _h _hj
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
    exact alphaChar_tau_cfNormSq_of_hypothesis_10_4_supported_source _h _hj
  have hZZ : Section1.scalarProduct G Z Z = 1 := by
    dsimp [Z]
    exact tauOne_xi_scalarProduct_self_of_hypothesis_10_4_supported_data _h
  have hZnorm : Section5.cfNormSq Z = 1 := by
    unfold Section5.cfNormSq
    rw [hZZ]
    simp
  have hnZnorm : Section5.cfNormSq ((n : ℂ) • Z) = (n : ℝ) ^ 2 := by
    rw [Section5.cfNormSq_smul, hZnorm]
    simp [pow_two]
  change Section5.cfNormSq Y = 2
  nlinarith

public theorem alphaChar_corrected_tau_sigma_omega_count_le_two_of_hypothesis_10_4_supported
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (_hj : j ≠ j0) :
    Section3.coefficientNonzeroCount
        (fun i k =>
          Section1.scalarProduct G
            (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
            (σ (ω i k))) ≤ 2 := by
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
        (section10FourSixNotation_of_hypothesis_10_4_supported_data _h) i i' j j'
  have hχvirt : ∀ p : I × J, IsVirtualCharacter (χ p) := by
    intro p
    rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h with
      ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource,
        _hW, _hA0, _h46, hω, _hIso, hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0,
          _hFull⟩
    exact hVirt (ω p.1 p.2)
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hω.irreducible p.1 p.2))
  have hYvirt :
      IsVirtualCharacter
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) :=
    alphaChar_corrected_tau_isVirtualCharacter_of_hypothesis_10_4_supported_source
      _h _hj
  have hYnorm :
      Section5.cfNormSq
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) = 2 :=
    alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_supported_source _h _hj
  have hcount :=
    finite_orthonormal_virtual_coeff_support_card_le_two_pf105
      χ horth hχvirt hYvirt hYnorm
  simpa [Section3.coefficientNonzeroCount, χ] using hcount

public theorem alphaChar_corrected_tau_sigma_omega_normSq_sum_le_two_of_hypothesis_10_4_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (_hj : j ≠ j0) :
    (∑ p : I × J,
      Complex.normSq
        (Section1.scalarProduct G
          (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ)
          (σ (ω p.1 p.2)))) ≤ 2 := by
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
        (section10FourSixNotation_of_hypothesis_10_4_supported_data _h) i i' j j'
  have hYnorm :
      Section5.cfNormSq
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) = 2 :=
    alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_supported_source _h _hj
  simpa [χ] using
    finite_orthonormal_coeff_normSq_sum_le_two_pf105 χ horth hYnorm

public theorem alphaChar_corrected_tau_residual_sigma_omega_count_le_four_of_hypothesis_10_4_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
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
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have ha : Section3.coefficientNonzeroCount a ≤ 2 := by
    dsimp [a, Y]
    exact alphaChar_corrected_tau_sigma_omega_count_le_two_of_hypothesis_10_4_supported
      h hj
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
    apply hb
    dsimp [b, a] at ha0 ⊢
    rw [Section5.scalarProduct_sub_left, ha0, hZik]
    simp
  simpa [Y, Z, b] using
    coefficientNonzeroCount_le_four_of_two_cell_update_pf105 a b hzero ha

public theorem alphaChar_fourTenTerm_pairing_eq_signed_rectangle_pairing_of_hypothesis_10_4_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
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
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨h10, _hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, hnpos, hdeg, hsign, hdn⟩
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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
  have hξμ : ∀ a b, Section1.scalarProduct M ξ (μ a b) = 0 := by
    intro a b
    by_cases hb : b = j0
    · subst b
      have hbase_ne : μ a j0 ≠ ξ := by
        intro hEq
        have hdegEq : (1 : ℂ) = (Nat.card W1 : ℂ) := by
          calc
            (1 : ℂ) = Section1.degree (μ a j0) :=
              (baseColumn_degree_one_of_section10FourSixNotationSupportedData_pairing
                hnotation a).symm
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
    exact scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
      hnotation a c b e
  have hδj : (δSign j : ℂ) = (δ : ℂ) := by
    rw [hsign j hj]
  have hδsq : (δ : ℂ) * (δ : ℂ) = 1 := by
    rcases hδsign with rfl | rfl <;> norm_num
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


public theorem fourTenTerm_supportedOn_primeDadeA0_of_section10FourSixNotationSupportedData
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {M W1 W2 : Subgroup G}
    {W : Subgroup M}
    {A A0 : Set M}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {i0 : I} {j0 : J}
    {μ : I → J → Section1.ClassFunction M}
    {δSign : J → ℤ}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    (hnotation : section10FourSixNotationSupportedData M W1 W2 W A A0
      i0 j0 μ δSign ω σ τ)
    (h46 : Section4Scratch.hypothesis_4_6_statement
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W
      (derivedSubgroup M) A)
    (i : I) (k : J) :
    Section1.supportedOn
      ((δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0)
      (Section4Scratch.primeDadeA0Set
        (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
  classical
  let B : Section1.ClassFunction M :=
    (δSign k : ℂ) • μ i k - (δSign k : ℂ) • μ i0 k - μ i j0 + μ i0 j0
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨σM, xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46Selected, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin,
      _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
  have hμClass : ∀ r s, Section1.IsClassFunction (μ r s) := fun r s =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (h43b.2.2.1 r s))
  have hBClass : Section1.IsClassFunction B := by
    intro x g
    simp [B, hμClass i k x g, hμClass i0 k x g, hμClass i j0 x g,
      hμClass i0 j0 x g]
  have hδ0 : (δSign j0 : ℂ) = 1 :=
    (Section4.proposition_4_4_base
      (W1.subgroupOf M) (W2.subgroupOf M) W I J i0 j0 ω σM μ
        (fun s => (δSign s : ℂ)) hω h43b).1
  have hδksq : (δSign k : ℂ) * (δSign k : ℂ) = 1 := by
    rcases h43b.2.1 k with hk | hk
    · have hk' : (δSign k : ℂ) = 1 := by simpa using hk
      rw [hk']
      norm_num
    · have hk' : (δSign k : ℂ) = -1 := by simpa using hk
      rw [hk']
      norm_num
  have hBdegree : Section1.degree B = 0 := by
    have hdegCol : Section1.degree (μ i k) = Section1.degree (μ i0 k) := by
      have hi := congrFun (h45a.1 i k) 1
      have hi0 := congrFun (h45a.1 i0 k) 1
      calc
        Section1.degree (μ i k) = Section1.degree (xChar k) := by
          simpa [Section1.degree, Section1.subgroupRestriction] using hi
        _ = Section1.degree (μ i0 k) := by
          simpa [Section1.degree, Section1.subgroupRestriction] using hi0.symm
    have hbase_i : μ i j0 1 = (1 : ℂ) := by
      simpa [Section1.degree] using
        baseColumn_degree_one_of_section10FourSixNotationSupportedData_pairing hnotation i
    have hbase_i0 : μ i0 j0 1 = (1 : ℂ) := by
      simpa [Section1.degree] using
        baseColumn_degree_one_of_section10FourSixNotationSupportedData_pairing hnotation i0
    have hcol_eval : μ i k 1 = μ i0 k 1 := by
      simpa [Section1.degree] using hdegCol
    unfold Section1.degree
    simp [B, hcol_eval, hbase_i, hbase_i0, Pi.sub_apply, Pi.smul_apply]
  have hBA0 :
      Section1.supportedOn B
        (Section4Scratch.a0Set (W2.subgroupOf M) W A) := by
    apply supportedOn_of_degree_eq_zero_of_punctured_subset _ hBdegree
    exact Section4Scratch.puncturedSet_subset_a0Set_of_hypothesis_4_6_self h46
  rcases h46.1 with
    ⟨_hSemi, _hHall, _hW1cyc, _hW1ne, _hW2cyc, _hW2ne, _hCentralizer,
      hW1W, _hW2W, hDirect, _hWodd⟩
  have hBW1 : ∀ x : M, x ∈ W1.subgroupOf M → B x = 0 := by
    intro x hxW1
    by_cases hx1 : x = 1
    · subst x
      simpa [Section1.degree] using hBdegree
    · have hxW : x ∈ W := hW1W hxW1
      have hxNotW2 : x ∉ W2.subgroupOf M := by
        intro hxW2
        have hxInf : x ∈ W1.subgroupOf M ⊓ W2.subgroupOf M :=
          ⟨hxW1, hxW2⟩
        rw [hDirect.inf_eq_bot] at hxInf
        exact hx1 (Subgroup.mem_bot.mp hxInf)
      have hxMinus : x ∈ ((W : Set M) \ (W2.subgroupOf M : Set M)) :=
        ⟨hxW, hxNotW2⟩
      let xW : W := ⟨x, hxW⟩
      have hωright : ω i0 k xW = 1 := by
        have hker := hω.right_kernel k ⟨xW, hxW1⟩
        simpa [hω.degree_one i0 k] using hker
      have hωright0 : ω i0 j0 xW = 1 := by
        have hker := hω.right_kernel j0 ⟨xW, hxW1⟩
        simpa [hω.degree_one i0 j0] using hker
      have hωeq : ω i k xW = ω i j0 xW := by
        rw [hω.product i k xW, hωright]
        ring
      have hμik : μ i k x = (δSign k : ℂ) * ω i k xW := by
        simpa [xW] using h43c.1 i k x hxMinus
      have hμi0k : μ i0 k x = (δSign k : ℂ) := by
        simpa [xW, hωright] using h43c.1 i0 k x hxMinus
      have hμij0 : μ i j0 x = ω i j0 xW := by
        simpa [xW, hδ0] using h43c.1 i j0 x hxMinus
      have hμi0j0 : μ i0 j0 x = 1 := by
        simpa [xW, hδ0, hωright0] using h43c.1 i0 j0 x hxMinus
      simp only [B, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hμik, hμi0k, hμij0, hμi0j0, hωeq]
      rw [← mul_assoc, hδksq]
      ring
  simpa [B] using
    Section4Scratch.supportedOn_primeDadeA0Set_of_supportedOn_a0Set_of_vanishesOn_W1
      (W1.subgroupOf M) (W2.subgroupOf M) W A hBClass hBA0 hBW1

public theorem tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_residual
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
    (h :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∀ i j, Section1.scalarProduct G (τ₁ ξ) (σ (ω i j)) = 0 := by
  classical
  let : Fintype M := Fintype.ofFinite M
  intro i j
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h
  have hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ :=
    section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
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
      ⟨ξ, hξS⟩
      (hypothesis_5_2_a_of_hypothesis_10_1_supported_data h10)
      (inducedFromNonkernelFamily_of_hypothesis_10_1_supported_data h10)
  rcases hRpack with
    ⟨R, hsetup, h52a, h52b, h52c, h52d, h52e, hExtra⟩
  let X : S := ⟨ξ, hξS⟩
  have hξbarS :
      Section1.conjugateCharacter ξ ∈ S := by
    simpa [X] using (h52a X).1
  have hpairSubset :
      ({(X : Section1.ClassFunction M),
        Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
        Finset (Section1.ClassFunction M)) ⊆ S := by
    intro χ hχ
    simp at hχ
    rcases hχ with rfl | rfl
    · exact X.2
    · simpa [X] using hξbarS
  have hinterfaces := extensionInterfaces_of_hypothesis_10_4_supported_data h
  have hpairIso :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    isCFLinearIsometryOnSpan_mono hpairSubset hinterfaces.1
  have hpairVirt :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    mapsIntegerSpanToVirtualCharacters_mono hpairSubset hinterfaces.2.1
  have hdeg :
      Section1.degree ξ =
        Section1.degree (Section1.conjugateCharacter ξ) := by
    have hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ) := by
      rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
        ⟨_h10, _hNotation, _hξS, _hξIrr, hξDegree, _hUniform⟩
      exact hξDegree
    calc
      Section1.degree ξ = (Nat.card W1 : ℂ) := hξDegree
      _ = star (Nat.card W1 : ℂ) := by simp
      _ = Section1.degree (Section1.conjugateCharacter ξ) := by
        rw [← hξDegree]
        simp [Section1.degree, Section1.conjugateCharacter]
  have hagreeX :
      τ₁ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) =
        τ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) := by
    simpa [X] using
      coherentExtension_agreesOn_sub_of_mem_of_degree_eq
        (coherentExtension_of_hypothesis_10_4_supported_data h)
        hξS hξbarS hdeg
  have hsubset :
      Section5.isSubsetSumOf (R X) (τ₁ ξ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X) (τ₁ (X : Section1.ClassFunction M)) :=
      Section5.theorem_5_5 S τ R
        hsetup h52a h52b h52c h52d h52e X τ₁ hpairIso hpairVirt hagreeX
    simpa [X] using hsubsetX
  have horth :
      Section5.orthogonalFinsets (R X)
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
    hExtra X hξIrr
  have homega :
      σ (ω i j) ∈
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) := by
    exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩
  exact scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets hsubset horth homega

public theorem alphaChar_corrected_tau_residual_sigma_omega_base_rectangle_of_hypothesis_10_4_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J} (_hj : j ≠ j0)
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
      tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_residual
        _h i k
    have h2 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i0 k)) = 0 :=
      tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_residual
        _h i0 k
    have h3 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i j0)) = 0 :=
      tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_residual
        _h i j0
    have h4 : Section1.scalarProduct G (τ₁ ξ) (σ (ω i0 j0)) = 0 :=
      tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_residual
        _h i0 j0
    dsimp [R]
    rw [Section5.scalarProduct_sub_right, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right, h1, h2, h3, h4]
    simp
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h
  have hαA0 :
      Section1.supportedOn (alphaChar μ ξ n δ j0 i0 j)
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) :=
    alphaChar_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
      _h _hj
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
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact h43b.2.2.1
  have hμClass : ∀ i j, Section1.IsClassFunction (μ i j) := fun i j =>
    Section1.isVirtualCharacter_isClassFunction
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        (hμIrr i j))
  have hαClass :
      Section1.IsClassFunction (alphaChar μ ξ n δ j0 i0 j) :=
    Section1.isVirtualCharacter_isClassFunction
      (alphaChar_isVirtualCharacter_of_hypothesis_10_4_supported_pairing _h i0 j)
  have hBClass : Section1.IsClassFunction B := by
    intro x g
    simp [B, hμClass i k x g, hμClass i0 k x g, hμClass i j0 x g,
      hμClass i0 j0 x g]
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hRτB : τ B = R := by
    have h410 := theorem_4_10_of_section10FourSixNotationSupportedData_local
      hnotation i k
    simpa [B, R] using h410
  have hAτR : Section1.scalarProduct G Aτ R = Section1.scalarProduct G Z R := by
    have hsource :=
      alphaChar_fourTenTerm_pairing_eq_signed_rectangle_pairing_of_hypothesis_10_4_supported
        _h _hj i k
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

public theorem alphaChar_corrected_tau_residual_sigma_omega_rectangle_relation_of_hypothesis_10_4_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
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
      alphaChar_corrected_tau_residual_sigma_omega_base_rectangle_of_hypothesis_10_4_supported_source
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

public theorem alphaChar_corrected_tau_residual_sigma_omega_orthogonal_of_hypothesis_10_4_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
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
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have hnotationData := hnotation
  rcases hnotationData with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource, _hW, _hA0, h46, hω,
      _hσiso, _hσvirt, _hσprincipal, _hσAgreeCyc, _h45, _h48, _hTauA0, _hfull⟩
  have h31 :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W :=
    (Section4.theorem_4_3_a
      (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
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
    rcases uniformMuData_of_hypothesis_10_4_supported_data h with
      ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
    rcases hδsign with rfl | rfl <;> norm_num
  have ha_count : Section3.coefficientNonzeroCount a ≤ 2 := by
    dsimp [a, Y]
    exact alphaChar_corrected_tau_sigma_omega_count_le_two_of_hypothesis_10_4_supported
      h hj
  have ha_norm : (∑ p : I × J, Complex.normSq (a p.1 p.2)) ≤ 2 := by
    dsimp [a, Y]
    exact alphaChar_corrected_tau_sigma_omega_normSq_sum_le_two_of_hypothesis_10_4_supported_source
      h hj
  have hb_count : Section3.coefficientNonzeroCount b ≤ 4 := by
    dsimp [b, Y, Z]
    simpa using
      alphaChar_corrected_tau_residual_sigma_omega_count_le_four_of_hypothesis_10_4_supported
        h hj
  have hrect : ∀ i i' k k', b i k + b i' k' = b i k' + b i' k := by
    dsimp [b, Y, Z]
    simpa using
      alphaChar_corrected_tau_residual_sigma_omega_rectangle_relation_of_hypothesis_10_4_supported
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
        scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
          hnotation i0 i0 j j
    have hψφ :
        Section1.scalarProduct G (σ (ω i0 j0)) (σ (ω i0 j)) = 0 := by
      have hj' : j0 ≠ j := fun hEq => hj hEq.symm
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
    two_cell_update_base_row_vanish_of_small_shape_pf105
      a b hj hδnorm hI3 hJ3 ha_count ha_norm hshape
      hupdate_j hupdate_j0 hupdate_other

public theorem alphaChar_corrected_tau_residual_eq_of_hypothesis_10_4_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ =
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) := by
  let Y : Section1.ClassFunction G :=
    τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ
  let φ : Section1.ClassFunction G := σ (ω i0 j)
  let ψ : Section1.ClassFunction G := σ (ω i0 j0)
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hδnorm : Complex.normSq (δ : ℂ) = 1 := by
    rcases hδsign with rfl | rfl <;> norm_num
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have hφφ : Section1.scalarProduct G φ φ = 1 := by
    dsimp [φ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        hnotation i0 i0 j j
  have hψψ : Section1.scalarProduct G ψ ψ = 1 := by
    dsimp [ψ]
    simpa using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        hnotation i0 i0 j0 j0
  have hφψ : Section1.scalarProduct G φ ψ = 0 := by
    dsimp [φ, ψ]
    simpa [hj] using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        hnotation i0 i0 j j0
  have hψφ : Section1.scalarProduct G ψ φ = 0 := by
    have hj' : j0 ≠ j := fun hEq => hj hEq.symm
    dsimp [φ, ψ]
    simpa [hj'] using
      scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
        hnotation i0 i0 j0 j
  have hYnorm : Section5.cfNormSq Y = 2 := by
    dsimp [Y]
    exact alphaChar_corrected_tau_cfNormSq_of_hypothesis_10_4_supported_source h hj
  rcases alphaChar_corrected_tau_residual_sigma_omega_orthogonal_of_hypothesis_10_4_supported
      h hj with
    ⟨hRφ, hRψ⟩
  have hYeq : Y = (δ : ℂ) • (φ - ψ) :=
    classFunction_eq_signed_sub_of_norm_two_and_residual_orthogonal_pf105
      hδnorm hφφ hψψ hφψ hψφ hYnorm
      (by simpa [Y, φ, ψ] using hRφ)
      (by simpa [Y, φ, ψ] using hRψ)
  simpa [Y, φ, ψ] using hYeq

public theorem alphaChar_baseRow_tau_formula_of_hypothesis_10_4_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {j : J}
    (_hj : j ≠ j0) :
    τ (alphaChar μ ξ n δ j0 i0 j) =
      (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) - (n : ℂ) • τ₁ ξ := by
  have hY :=
    alphaChar_corrected_tau_residual_eq_of_hypothesis_10_4_supported _h _hj
  calc
    τ (alphaChar μ ξ n δ j0 i0 j) =
        (τ (alphaChar μ ξ n δ j0 i0 j) + (n : ℂ) • τ₁ ξ) -
          (n : ℂ) • τ₁ ξ := by
          ext x
          simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    _ = (δ : ℂ) • (σ (ω i0 j) - σ (ω i0 j0)) - (n : ℂ) • τ₁ ξ := by
          rw [hY]

public theorem alphaChar_tau_formula_of_hypothesis_10_4_supported_source
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    τ (alphaChar μ ξ n δ j0 i j) =
      (δ : ℂ) • (σ (ω i j) - σ (ω i j0)) - (n : ℂ) • τ₁ ξ := by
  have hbase :=
    alphaChar_baseRow_tau_formula_of_hypothesis_10_4_supported_source h hj
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have h410 := theorem_4_10_of_section10FourSixNotationSupportedData_local hNotation
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

public theorem irreducible_member_of_hypothesis_10_4_supported_data_local
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    ∃ X : S, Section1.IsIrreducibleCharacterOnGroup (X : Section1.ClassFunction M) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  exact ⟨⟨ξ, hξS⟩, hξIrr⟩

public theorem exists_conjugate_muColumn_index_of_hypothesis_10_4_supported_data_local
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
      i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    ∃ j' : J,
      j' ≠ j0 ∧
        Section1.conjugateCharacter (muColumn μ j) = muColumn μ j' ∧
          muColumn μ j' ≠ muColumn μ j := by
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases exists_supportedFourSixData_of_section10FourSixNotationSupportedData
      hnotation with
    ⟨H, σM, xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨hω, h43b, h43c, _h43d, h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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
  have hjMem : j ∈ Section4Scratch.equalDegreeColumnSet μ j0 j := by
    exact ⟨hj, rfl⟩
  rcases (h49a hj).1 j hjMem with ⟨j', hj'Mem, hconj, hne⟩
  exact ⟨j', hj'Mem.1,
    by simpa [muColumn, Section4Scratch.piColumn] using hconj,
    by simpa [muColumn, Section4Scratch.piColumn] using hne⟩

public theorem fiveEightAlternative_muColumn_of_hypothesis_10_4_supported_data_local
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    (τ₁ (muColumn μ j) =
        ((δSign j : ℂ) • Section4Scratch.omegaColumnSigma σ ω j)) ∨
      ∃ j' : J,
        j' ≠ j0 ∧
          Section1.conjugateCharacter (muColumn μ j) = muColumn μ j' ∧
            muColumn μ j' ≠ muColumn μ j ∧
              τ₁ (muColumn μ j) =
                  (-(δSign j : ℂ)) •
                    Section4Scratch.omegaColumnSigma σ ω j' ∧
                ∀ l : J, l ≠ j0 →
                  muColumn μ l ∈ S →
                    Section1.degree (muColumn μ l) =
                      Section1.degree (muColumn μ j) →
                      l = j' ∨ l = j := by
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases derivedSupportedFourSixData_of_hypothesis_10_1_supported_data
      h10 hnotation with
    ⟨σM, xChar, H_A, _H_A0, hSupported⟩
  rcases exists_conjugate_muColumn_index_of_hypothesis_10_4_supported_data_local h hj with
    ⟨j', hj'0, hconj, hne⟩
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
  have hAlt :=
    Section5.theorem_5_8_core
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
      (hypothesis_5_2_a_of_hypothesis_10_1_supported_data h10)
      (irreducible_member_of_hypothesis_10_4_supported_data_local h)
      (inducedFromNonkernelFamily_of_hypothesis_10_1_supported_data h10)
      j hj
      (by simpa [muColumn, Section4Scratch.piColumn] using
        muColumn_mem_of_hypothesis_10_4_supported_data_local h hj)
      j'
      (by simpa [muColumn, Section4Scratch.piColumn] using hconj)
      τ₁
      (extensionInterfaces_of_hypothesis_10_4_supported_data h).1
      (extensionInterfaces_of_hypothesis_10_4_supported_data h).2.1
      (extensionInterfaces_of_hypothesis_10_4_supported_data h).2.2
  rcases hAlt with hpos | hneg
  · exact Or.inl (by simpa [muColumn, Section4Scratch.piColumn] using hpos)
  · refine Or.inr ⟨j', hj'0, hconj, hne, ?_, ?_⟩
    · simpa [muColumn, Section4Scratch.piColumn] using hneg.1
    · intro l hl0 hlS hdeg
      exact hneg.2 l hl0
        (by simpa [muColumn, Section4Scratch.piColumn] using hlS)
        (by simpa [muColumn, Section4Scratch.piColumn] using hdeg)

public theorem scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_data_local
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
      i0 j0 μ δSign ω σ d n δ)
    (i : I) (j k : J) :
    Section1.scalarProduct M (μ i j) (muColumn μ k) =
      if j = k then 1 else 0 := by
  classical
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hnotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
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

public theorem baseColumn_degree_one_of_section10FourSixNotationSupportedData_local
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


public theorem alphaChar_isVirtualCharacter_of_hypothesis_10_4_supported_data_local
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
      i0 j0 μ δSign ω σ d n δ)
    (i : I) (j : J) :
    IsVirtualCharacter (alphaChar μ ξ n δ j0 i j) := by
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data h
  rcases h104a with ⟨_h10, hNotation, _hξS, hξIrr, _hξDegree, _hUniform⟩
  have hμirr : ∀ i j, Section1.IsIrreducibleCharacterOnGroup (μ i j) := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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

public theorem alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_supported_data_local
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
      i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) ξ = -(n : ℂ) := by
  classical
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, hNotation, _hξS, hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, _hdpos, hδ, hnpos, hdeg, _hsign, hdn⟩
  rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
    ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
  rcases hSupported with
    ⟨h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
  rcases hRest with
    ⟨_hω, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hτiso, _hτpunct, _hτvirt, _hPF39⟩
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
          (baseColumn_degree_one_of_section10FourSixNotationSupportedData_local hNotation i).symm
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

public theorem tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_data_local
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
    (h :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∀ i j, Section1.scalarProduct G (τ₁ ξ) (σ (ω i j)) = 0 := by
  classical
  let : Fintype M := Fintype.ofFinite M
  intro i j
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h
  have hnotation :
      section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
        μ δSign ω σ τ :=
    section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨_h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
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
      ⟨ξ, hξS⟩
      (hypothesis_5_2_a_of_hypothesis_10_1_supported_data h10)
      (inducedFromNonkernelFamily_of_hypothesis_10_1_supported_data h10)
  rcases hRpack with
    ⟨R, hsetup, h52a, h52b, h52c, h52d, h52e, hExtra⟩
  let X : S := ⟨ξ, hξS⟩
  have hξbarS :
      Section1.conjugateCharacter ξ ∈ S := by
    simpa [X] using (h52a X).1
  have hpairSubset :
      ({(X : Section1.ClassFunction M),
        Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
        Finset (Section1.ClassFunction M)) ⊆ S := by
    intro χ hχ
    simp at hχ
    rcases hχ with rfl | rfl
    · exact X.2
    · simpa [X] using hξbarS
  have hinterfaces := extensionInterfaces_of_hypothesis_10_4_supported_data h
  have hpairIso :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    isCFLinearIsometryOnSpan_mono hpairSubset hinterfaces.1
  have hpairVirt :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction M),
          Section1.conjugateCharacter (X : Section1.ClassFunction M)} :
          Finset (Section1.ClassFunction M)) τ₁ :=
    mapsIntegerSpanToVirtualCharacters_mono hpairSubset hinterfaces.2.1
  have hdeg :
      Section1.degree ξ =
        Section1.degree (Section1.conjugateCharacter ξ) := by
    have hξDegree : Section1.degree ξ = (Nat.card W1 : ℂ) := by
      rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
        ⟨_h10, _hNotation, _hξS, _hξIrr, hξDegree, _hUniform⟩
      exact hξDegree
    calc
      Section1.degree ξ = (Nat.card W1 : ℂ) := hξDegree
      _ = star (Nat.card W1 : ℂ) := by simp
      _ = Section1.degree (Section1.conjugateCharacter ξ) := by
        rw [← hξDegree]
        simp [Section1.degree, Section1.conjugateCharacter]
  have hagreeX :
      τ₁ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) =
        τ ((X : Section1.ClassFunction M) -
          Section1.conjugateCharacter (X : Section1.ClassFunction M)) := by
    simpa [X] using
      coherentExtension_agreesOn_sub_of_mem_of_degree_eq
        (coherentExtension_of_hypothesis_10_4_supported_data h)
        hξS hξbarS hdeg
  have hsubset :
      Section5.isSubsetSumOf (R X) (τ₁ ξ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X) (τ₁ (X : Section1.ClassFunction M)) :=
      Section5.theorem_5_5 S τ R
        hsetup h52a h52b h52c h52d h52e X τ₁ hpairIso hpairVirt hagreeX
    simpa [X] using hsubsetX
  have horth :
      Section5.orthogonalFinsets (R X)
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
    hExtra X hξIrr
  have homega :
      σ (ω i j) ∈
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) := by
    exact Finset.mem_image.mpr ⟨(i, j), by simp, rfl⟩
  exact scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets hsubset horth homega

public theorem sigma_omega_orthogonal_tauOne_xi_of_hypothesis_10_4_supported_data_local
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
    (h :
      hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
        μ δSign ω σ d n δ) :
    ∀ i j, Section1.scalarProduct G (σ (ω i j)) (τ₁ ξ) = 0 := by
  intro i j
  have hzero := tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_data_local h i j
  simpa [Section1.scalarProduct_star_swap] using congrArg star hzero

public theorem tauOne_xi_orthogonal_muColumn_of_hypothesis_10_4_supported_data_local
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
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
    {d n : ℕ} {δ : ℤ}
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    {j : J} (hj : j ≠ j0) :
    Section1.scalarProduct G (τ₁ ξ) (τ₁ (muColumn μ j)) = 0 := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, _hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hcolS : muColumn μ j ∈ S := muColumn_mem_of_hypothesis_10_4_supported_data_local h hj
  have hspanξ : Section5.integerSpan S ξ := integerSpan_of_mem S hξS
  have hspanCol : Section5.integerSpan S (muColumn μ j) := integerSpan_of_mem S hcolS
  have hne : ξ ≠ muColumn μ j := by
    intro hEq
    have hdegEq :
        Section1.degree (muColumn μ j) = Section1.degree ξ := by
      rw [← hEq]
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_supported_data_local h hj
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
  rcases hypothesis_5_2_of_hypothesis_10_1_supported_data h10 with
    ⟨_hSetup, _R, _h52a, _h52b, h52c, _h52d, _h52e⟩
  calc
    Section1.scalarProduct G (τ₁ ξ) (τ₁ (muColumn μ j)) =
        Section1.scalarProduct M ξ (muColumn μ j) :=
          (extensionInterfaces_of_hypothesis_10_4_supported_data h).1
            ξ (muColumn μ j) hspanξ hspanCol
    _ = 0 := h52c hξS hcolS hne

public theorem scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData_local
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

public theorem alphaChar_scalarProduct_muColumn_eq_one_of_hypothesis_10_4_supported_data_local
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
      i0 j0 μ δSign ω σ d n δ)
    {i : I}
    {j : J}
    (hj : j ≠ j0) :
    Section1.scalarProduct M (alphaChar μ ξ n δ j0 i j) (muColumn μ j) = 1 := by
  classical
  have hentry :
      Section1.scalarProduct M (μ i j) (muColumn μ j) = 1 := by
    simpa using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_data_local
        h i j j
  have hbase :
      Section1.scalarProduct M (μ i j0) (muColumn μ j) = 0 := by
    simpa [hj.symm] using
      scalarProduct_mu_entry_muColumn_eq_ite_of_hypothesis_10_4_supported_data_local
        h i j0 j
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, hUniform⟩
  rcases hUniform with
    ⟨_hI, _hJ, _hPrime, hdpos, _hδsign, _hnpos, _hdeg, _hsign, _hdn⟩
  have hcolS : muColumn μ j ∈ S := muColumn_mem_of_hypothesis_10_4_supported_data_local h hj
  have hne : ξ ≠ muColumn μ j := by
    intro hEq
    have hdegEq :
        Section1.degree (muColumn μ j) = Section1.degree ξ := by
      rw [← hEq]
    have hcoldeg := degree_muColumn_of_hypothesis_10_4_supported_data_local h hj
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
  rcases hypothesis_5_2_of_hypothesis_10_1_supported_data h10 with
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

public theorem alphaChar_mixed_scalarProduct_muColumn_transfer_obligation_supported
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
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
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data _h
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h
  rcases h104a with ⟨_h10, _hNotation', hξS, hξIrr, hξDegree, _hUniform⟩
  have hαA0 :
      Section1.supportedOn α
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    simpa [α] using
      alphaChar_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
        _h hj
  have hdiffA0 :
      Section1.supportedOn diff
        (Section4Scratch.primeDadeA0Set
          (W1.subgroupOf M) (W2.subgroupOf M) W A) := by
    simpa [diff, col] using
      muColumn_sub_smul_xi_supportedOn_primeDadeA0_of_hypothesis_10_4_supported_data_local
        _h hj
  have hτiso :
      Section4Scratch.tau_isometry_on_primeDadeA0_statement
        (W1.subgroupOf M) (W2.subgroupOf M) W A τ := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
      ⟨_hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
        hτiso, _hτpunct, _hτvirt, _hPF39⟩
    exact hτiso
  have hαClass : Section1.IsClassFunction α :=
    Section1.isVirtualCharacter_isClassFunction
      (by
        simpa [α] using
          alphaChar_isVirtualCharacter_of_hypothesis_10_4_supported_data_local _h i j)
  have hdiffClass : Section1.IsClassFunction diff := by
    rcases supportedFourSixData_of_section10FourSixNotationSupportedData hNotation with
      ⟨_σM, _xChar, _H_A, _H_A0, hSupported⟩
    rcases hSupported with
      ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A, hRest⟩
    rcases hRest with
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
      tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_supported_data_local _h hj
  have hτξself : Section1.scalarProduct G (τ₁ ξ) (τ₁ ξ) = 1 := by
    exact tauOne_xi_scalarProduct_self_of_hypothesis_10_4_supported_data _h
  have hτξ :
      Section1.scalarProduct G (τ α) (τ₁ ξ) = -(n : ℂ) := by
    have hformula :=
      alphaChar_tau_formula_of_hypothesis_10_4_supported_source _h (i := i) hj
    have homega :
        Section1.scalarProduct G (σ (ω i j) - σ (ω i j0)) (τ₁ ξ) = 0 := by
      rw [Section5.scalarProduct_sub_left]
      rw [sigma_omega_orthogonal_tauOne_xi_of_hypothesis_10_4_supported_data_local _h i j]
      rw [sigma_omega_orthogonal_tauOne_xi_of_hypothesis_10_4_supported_data_local _h i j0]
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
      alphaChar_scalarProduct_xi_eq_neg_n_of_hypothesis_10_4_supported_data_local _h hj
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

public theorem theorem_10_6_nonbase_column_formula_of_pairing_supported
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
      i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0)
    (hpair : ∀ i : I,
      Section1.scalarProduct G
        ((δ : ℂ) • (σ (ω i j) - σ (ω i j0)))
        (τ₁ (muColumn μ j)) = 1) :
    τ₁ (muColumn μ j) =
      (δ : ℂ) • (∑ i : I, σ (ω i j)) := by
  classical
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
    ⟨_hI, _hJ, _hPrime, _hdpos, _hδsign, _hnpos, _hdeg, hsign, _hdn⟩
  have hδj : δSign j = δ := hsign j hj
  rcases fiveEightAlternative_muColumn_of_hypothesis_10_4_supported_data_local h hj with hpos | hneg
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
        scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData_local
          hNotation i0 j j'
      have hbase :=
        scalarProduct_sigma_omega_omegaColumnSigma_eq_ite_of_section10FourSixNotationSupportedData_local
          hNotation i0 j0 j'
      rw [hsame, hbase]
      have hj0j' : j0 ≠ j' := fun hEq => hj'0 hEq.symm
      simp [hjj', hj0j']
    have hone := hpair i0
    rw [hzero] at hone
    norm_num at hone

public theorem theorem_10_6_nonbase_column_formula_obligation_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    ∀ j, j ≠ j0 →
      τ₁ (muColumn μ j) =
        (δ : ℂ) • (∑ i : I, σ (ω i j)) := by
  intro j hj
  refine theorem_10_6_nonbase_column_formula_of_pairing_supported _h hj ?_
  intro i
  have htauPair :
      Section1.scalarProduct G
        (τ (alphaChar μ ξ n δ j0 i j))
        (τ₁ (muColumn μ j)) = 1 := by
    rw [alphaChar_mixed_scalarProduct_muColumn_transfer_obligation_supported _h hj]
    exact alphaChar_scalarProduct_muColumn_eq_one_of_hypothesis_10_4_supported_data_local _h hj
  have halpha :=
    alphaChar_tau_formula_of_hypothesis_10_4_supported_source _h (i := i) hj
  have horth :=
    tauOne_xi_orthogonal_muColumn_of_hypothesis_10_4_supported_data_local _h hj
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

public theorem theorem_10_6_base_column_from_nonbase_and_alpha_formula_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ)
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
  rcases uniformMuData_of_hypothesis_10_4_supported_data h with
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

public theorem theorem_10_6_base_column_formula_obligation_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ) :
    τ (muColumn μ j0 - ξ) =
      (∑ i : I, σ (ω i j0)) - τ₁ ξ := by
  rcases exists_ne_base_column_of_hypothesis_10_4_supported_data_local _h with
    ⟨j, hj⟩
  refine theorem_10_6_base_column_from_nonbase_and_alpha_formula_supported _h
    (theorem_10_6_nonbase_column_formula_obligation_supported_source _h j hj) ?_ ?_
  · have hagree :=
      tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_supported_data_local
        _h hj
    rw [← hagree, map_sub, map_smul]
  · intro i
    exact alphaChar_tau_formula_of_hypothesis_10_4_supported_source _h (i := i) hj

public theorem theorem_10_6_tildeA_lower_bound_obligation_supported_source
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
    (_h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0
      μ δSign ω σ d n δ) :
    ∀ g : G, g ∉ tildeA → Nat.Coprime (orderOf g) (Nat.card W1) →
      1 ≤ Complex.normSq (τ₁ ξ g) := by
  -- PF `(10.6.b)`: combine the supported base-column formula, source Dade
  -- vanishing off `\widetilde A(M)`, and the `(3.9)` odd-integer parity.
  intro g hg hcop
  have hbase := theorem_10_6_base_column_formula_obligation_supported_source _h
  have hvanish :
      τ (muColumn μ j0 - ξ) g = 0 :=
    tildeAVanishing_of_hypothesis_10_4_supported_data _h tildeA _hTilde g hg
  have hvalue :
      τ₁ ξ g = ∑ i : I, σ (ω i j0) g := by
    have hzero :
        (0 : ℂ) = (∑ i : I, σ (ω i j0) g) - τ₁ ξ g := by
      calc
        (0 : ℂ) = τ (muColumn μ j0 - ξ) g := hvanish.symm
        _ = ((∑ i : I, σ (ω i j0)) - τ₁ ξ) g := congrFun hbase g
        _ = (∑ i : I, σ (ω i j0) g) - τ₁ ξ g := by simp
    exact (sub_eq_zero.mp hzero.symm).symm
  rcases baseColumnParity_of_hypothesis_10_4_supported_data _h g hcop with
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

public theorem theorem_10_8_counting_tildeA_supported_source
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
        μ δSign ω σ d n δ) :
    ∃ tildeA : Set G, section10TildeAData M MF tildeA := by
  classical
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h104 with
    ⟨MFsrc, Ms, Abook, A0book, A1book, hBook, _hRest⟩
  rcases hBook with ⟨_hApre, _hA0pre, hNotationSrc, _hDade⟩
  have hMFsrc : MFsrc = MF := by
    rcases h10 with
      ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
        _h46base, _hNotation10, _h52⟩
    rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
    exact section16MFSubgroup_unique hNotationSrc.2.1 hP.1
  have hNotationSrcOuter :
      Section8.notation_8_10_source_data M MF Ms Abook A0book A1book := by
    simpa [hMFsrc] using hNotationSrc
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46base, _hNotation10, _h52⟩
  have hTail := theorem_10_8_late_source_type_of_typeIIIIVVData hType
  have hA1A : A1book ⊆ Abook :=
    theorem_10_8_A1_subset_A_of_late_notation_8_10_source_data
      hNotationSrcOuter hTail
  have hAA0 : Abook ⊆ A0book :=
    theorem_10_8_A_subset_A0_of_notation_8_10_source_data hNotationSrcOuter
  rcases Section8.exists_mixed_notation_8_14_source_data_of_theorem_8_13
      M MF Ms Abook A0book A1book (inferInstance : IsMinCE G)
      hNotationSrcOuter hA1A hAA0 with
    ⟨R, tildeA, tildeA0, tildeA1, h14⟩
  exact ⟨tildeA, Ms, Abook, A0book, A1book,
    Section8.section8DSet M A0book, tildeA0, tildeA1, R, hNotationSrcOuter, h14⟩

public theorem theorem_10_8_counting_rho_section7_bounds_core_supported_source
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
      (1 : ℝ) -
          ((Nat.card W1 : ℝ) / (Nat.card (ambientDerivedSubgroup M) : ℝ)) ≤
        rho ∧
        rho ≤
          (((theorem_10_8_countingG1Set tildeA W1).ncard : ℝ) /
            (Nat.card G : ℝ)) +
            ((A.ncard : ℝ) / (Nat.card M : ℝ)) := by
  rcases theorem_10_8_counting_rho_section7_cover_supported_source _h104 _hTilde with
    ⟨rho, hlower, hSuzuki⟩
  refine ⟨rho, hlower, ?_⟩
  exact theorem_10_8_counting_rho_upper_bound_of_cover_excess
    (g1Ratio :=
      ((theorem_10_8_countingG1Set tildeA W1).ncard : ℝ) /
        (Nat.card G : ℝ))
    (aRatio := (A.ncard : ℝ) / (Nat.card M : ℝ))
    (coverExcess := theorem_10_8_countingRhoCoverExcess tildeA (τ₁ ξ))
    (theorem_10_8_counting_rho_coverExcess_lower_bound
      (W1 := W1)
      (χ := τ₁ ξ)
      (theorem_10_6_tildeA_lower_bound_obligation_supported_source
        _hTilde _h104))
    hSuzuki

public theorem theorem_10_8_counting_A_ratio_strict_supported_source
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
        μ δSign ω σ d n δ) :
    ((A.ncard : ℚ) / (Nat.card M : ℚ)) <
      1 / (Nat.card W1 : ℚ) := by
  have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h104 with
    ⟨_MFsrc, _Ms, _Abook, _A0book, _A1book, _hDade, _hW, _hA0,
      h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull⟩
  rcases h46 with
    ⟨_h42, _hKnorm, _hW2K, _hKK, _hcentA, hAinK⟩
  have hAcard :
      A.ncard < Nat.card (derivedSubgroup M) :=
    theorem_10_8_ncard_lt_card_subgroup_of_subset_punctured hAinK
  exact theorem_10_8_ratio_lt_recip_of_ncard_lt_subgroup_card
    (K := derivedSubgroup M) (A := A) hAcard
    (derivedSubgroup_index_eq_card_W1_of_hypothesis_10_1_supported_data h10)

public theorem theorem_10_8_counting_rho_section7_bounds_supported_source
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
      (1 : ℝ) -
          ((Nat.card W1 : ℝ) / (Nat.card (ambientDerivedSubgroup M) : ℝ)) ≤
        rho ∧
        rho ≤
          (((theorem_10_8_countingG1Set tildeA W1).ncard : ℝ) /
            (Nat.card G : ℝ)) +
            ((A.ncard : ℝ) / (Nat.card M : ℝ)) ∧
          ((A.ncard : ℝ) / (Nat.card M : ℝ)) <
            1 / (Nat.card W1 : ℝ) := by
  rcases theorem_10_8_counting_rho_section7_bounds_core_supported_source
      _h104 _hTilde with
    ⟨rho, hlower, hupper⟩
  have hAQ := theorem_10_8_counting_A_ratio_strict_supported_source _h104
  have hAR :
      ((A.ncard : ℝ) / (Nat.card M : ℝ)) <
        1 / (Nat.card W1 : ℝ) := by
    norm_num [← Rat.cast_lt (K := ℝ), Rat.cast_div, Rat.cast_natCast,
      Rat.cast_one] at hAQ ⊢
    exact hAQ
  exact ⟨rho, hlower, hupper, hAR⟩

public theorem theorem_10_8_counting_rho_gap_supported_source
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
    (1 : ℚ) -
        (((theorem_10_8_countingG1Set tildeA W1).ncard : ℚ) /
          (Nat.card G : ℚ)) -
        1 / (Nat.card W1 : ℚ) <
      ((Nat.card W1 : ℚ) / (Nat.card (ambientDerivedSubgroup M) : ℚ)) := by
  rcases theorem_10_8_counting_rho_section7_bounds_supported_source _h104 _hTilde with
    ⟨rho, hlower, hupper, hA⟩
  exact theorem_10_8_counting_rho_gap_of_real_source_bounds
    (g1 := (theorem_10_8_countingG1Set tildeA W1).ncard)
    (g := Nat.card G)
    (w1 := Nat.card W1)
    (m := Nat.card (ambientDerivedSubgroup M))
    (rho := rho)
    (aRatio := (A.ncard : ℝ) / (Nat.card M : ℝ))
    hlower hupper hA

public theorem theorem_10_8_counting_G1_support_bound_supported_source
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
    {Smax SF U : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (_hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hfrob : section12FrobeniusJoinWithKernel SF U)
    (hTypePAlign : Section8.typePDefinitionData Smax SF U W2 W1)
    {tildeA : Set G}
    (_hTilde : section10TildeAData M MF tildeA) :
    (((theorem_10_8_countingG1Set tildeA W1).ncard : ℚ) /
        (Nat.card G : ℚ)) ≤
      ((Nat.card SF : ℚ) / (Nat.card Smax : ℚ) +
        (1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
          1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ))) := by
  classical
  have hsubset :
      theorem_10_8_countingG1Set tildeA W1 ⊆
        theorem_10_8_countingHVSupportSet SF V := by
    intro x hx
    rcases hx with ⟨hxOutside, hxNoncoprime⟩
    rcases Nat.Prime.not_coprime_iff_dvd.mp hxNoncoprime with
      ⟨p, hpPrime, hpx, hpW1⟩
    rcases theorem_10_8_exists_prime_order_zpower_centralized hpPrime hpx with
      ⟨a, _haZ, _hane, haOrder, hxCent⟩
    have hpSF : (⟨p, hpPrime⟩ : Nat.Primes) ∈ subgroupPrimeSet SF :=
      typePDefinitionData_secondComplement_prime_mem_mf hTypePAlign hpPrime hpW1
    have hHallSF : IsHallSubgroup (subgroupPrimeSet SF) SF :=
      theorem_10_8_typeII_mf_isHallSubgroup hSmax hSF hTypeII
    rcases theorem_10_8_exists_conjugate_mem_of_isHallSubgroup_prime_order
        hHallSF hpPrime hpSF haOrder with
      ⟨y, haySFmem⟩
    let ay : G := y * a * y⁻¹
    let xy : G := y * x * y⁻¹
    have hayOrder : orderOf ay = p := by
      calc
        orderOf ay = orderOf a := by
          simpa [ay, MulAut.conj_apply] using (MulAut.conj y).orderOf_eq a
        _ = p := haOrder
    have hayNe : ay ≠ 1 := by
      intro hay1
      have hpOne : p = 1 := by
        rw [← hayOrder]
        exact orderOf_eq_one_iff.mpr hay1
      exact hpPrime.ne_one hpOne
    have haySF : ay ∈ Section7.puncturedSubgroupSet SF :=
      ⟨by simpa [ay] using haySFmem, hayNe⟩
    have hxyCent : xy ∈ elementCentralizerIn (⊤ : Subgroup G) ay := by
      simpa [xy, ay] using
        theorem_10_8_conj_mem_elementCentralizerIn_top (y := y) hxCent
    have hxyOrder : p ∣ orderOf xy := by
      have horder : orderOf xy = orderOf x := by
        simpa [xy, MulAut.conj_apply] using (MulAut.conj y).orderOf_eq x
      simpa [horder] using hpx
    have hxyHV : xy ∈ theorem_10_8_countingHVSupportSet SF V := by
      have hSrcII : Section8.typeIIDefinitionData Smax SF :=
        Section8.theorem_8_8_typeII_to_source_public
          (G := G) hSmax hSF hTypeII
      have hTI :
          section16TISubsetWithNormalizer
            (Section7.puncturedSubgroupSet SF) Smax := by
        simpa [Section7.puncturedSubgroupSet, section16NonidentityElements] using
          Section8.theorem_8_16_typeII_mf_punctured_tiWithNormalizer
            (G := G) (M := Smax) (MF := SF) hSmax hSrcII
      have hxyS : xy ∈ Smax :=
        theorem_10_8_mem_normalizer_of_ti_subset_centralizes_mem
          hTI haySF haySF.2 hxyCent
      by_cases hxyHU : xy ∈ SF ⊔ U
      · have hxySF : xy ∈ SF :=
          theorem_10_8_frobeniusJoin_mem_kernel_of_mem_join_centralizes_ne
            hfrob hxyHU haySF.1 haySF.2 hxyCent
        have hxyNe : xy ≠ 1 :=
          theorem_10_8_ne_one_of_prime_dvd_order hpPrime hxyOrder
        left
        refine ⟨xy, ⟨hxySF, hxyNe⟩, 1, Set.mem_univ 1, ?_⟩
        group
      · have hLocal :
            xy ∈ section16ConjugatesOfSetBySet
              (section16HatW W2 W1) (Smax : Set G) :=
          theorem_10_8_typeP_not_mem_join_prime_support_conjugates_hatW_source
            hSmax hTypePAlign hpPrime hpSF hxyOrder hxyS hxyHU
        have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data h104
        rcases h10 with
          ⟨_hM, hType, _hS, _hW1M, _hW2M, _hW12M, _hDade,
            _h46base, _hNotation10, _h52⟩
        rcases hType with ⟨hV, _U0, _hP, _hTypeTail⟩
        right
        rcases hLocal with ⟨z, hz, t, _ht, hzt⟩
        refine ⟨z, ?_, t, Set.mem_univ t, hzt⟩
        rw [hV]
        simpa [theorem_10_8_section16HatW_swap (W1 := W1) (W2 := W2)] using hz
    exact theorem_10_8_countingHVSupportSet_conj_inv (y := y) hxyHV
  have hH :
      (((section16ConjugatesOfSetBySet
            (Section7.puncturedSubgroupSet SF) Set.univ).ncard : ℚ) /
          (Nat.card G : ℚ)) ≤
        ((Nat.card SF : ℚ) / (Nat.card Smax : ℚ)) := by
    have hSrcII : Section8.typeIIDefinitionData Smax SF :=
      Section8.theorem_8_8_typeII_to_source_public
        (G := G) hSmax hSF hTypeII
    have hTI :
        section16TISubsetWithNormalizer
          (Section7.puncturedSubgroupSet SF) Smax := by
      simpa [Section7.puncturedSubgroupSet, section16NonidentityElements] using
        Section8.theorem_8_16_typeII_mf_punctured_tiWithNormalizer
          (G := G) (M := Smax) (MF := SF) hSmax hSrcII
    have hOne : (1 : G) ∉ Section7.puncturedSubgroupSet SF := by
      intro h
      exact h.2 rfl
    have hratio :=
      theorem_10_8_conjugatesOfSetBySet_ratio_eq_of_tiNormalizer
        (X := Section7.puncturedSubgroupSet SF) (N := Smax) hOne hTI
    rw [hratio]
    have hcard := theorem_10_8_puncturedSubgroupSet_ncard_le_card SF
    have hcardQ :
        ((Section7.puncturedSubgroupSet SF).ncard : ℚ) ≤
          (Nat.card SF : ℚ) := by
      exact_mod_cast hcard
    have hden_nonneg : (0 : ℚ) ≤ (Nat.card Smax : ℚ) := by positivity
    exact div_le_div_of_nonneg_right hcardQ hden_nonneg
  have hVratio :
      (((section16ConjugatesOfSetBySet V Set.univ).ncard : ℚ) /
          (Nat.card G : ℚ)) ≤
        (1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
          1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ)) := by
    have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data h104
    rcases h10 with
      ⟨_hM, hType, _hS, hW1M, hW2M, hW12M, _hDade, _h46base,
        _hNotation10, _h52⟩
    rcases hType with ⟨hV, U0, hP, _hTypeTail⟩
    have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h104
    rcases hNotation with
      ⟨_MFbook, _Ms, _Abook, _A0book, _A1book, _hSource,
        hW, _hA0, h46, _hω, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
          _hTauA0, _hFull⟩
    have h31 :
        Section3.hypothesis_3_1_statement
          (W1.subgroupOf M) (W2.subgroupOf M) W :=
      (Section4.theorem_4_3_a
        (derivedSubgroup M) (W1.subgroupOf M) (W2.subgroupOf M) W h46.1).2
    have hTI :
        section16TISubsetWithNormalizer
          (section16HatW W1 W2) (W1 ⊔ W2 : Subgroup G) :=
      Section8.theorem_8_5_c M MF U0 W1 W2 hP
    have hOne : (1 : G) ∉ section16HatW W1 W2 := by
      intro h
      exact h.2 (Or.inl W1.one_mem)
    have hratio :=
      theorem_10_8_conjugatesOfSetBySet_ratio_eq_of_tiNormalizer
        (X := section16HatW W1 W2) (N := (W1 ⊔ W2 : Subgroup G)) hOne hTI
    have hhat_card :
        Nat.card (section16HatW W1 W2) =
          (Nat.card W1 - 1) * (Nat.card W2 - 1) :=
      theorem_10_8_natCard_section16HatW_eq_of_section10_notation
        hW1M hW2M hW h31
    have hWsup_card :
        Nat.card (W1 ⊔ W2 : Subgroup G) = Nat.card W1 * Nat.card W2 :=
      theorem_10_8_natCard_sup_eq_mul_of_section10_notation
        hW1M hW2M hW12M hW h31
    rw [hV, hratio]
    have hhat_ncard :
        (((section16HatW W1 W2).ncard : ℚ)) =
          (((Nat.card W1 - 1) * (Nat.card W2 - 1) : ℕ) : ℚ) := by
      rw [← Nat.card_coe_set_eq (section16HatW W1 W2), hhat_card]
    have hden :
        (Nat.card (W1 ⊔ W2 : Subgroup G) : ℚ) =
          ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ) := by
      rw [hWsup_card, Nat.cast_mul]
    have hvalue :
        ((section16HatW W1 W2).ncard : ℚ) /
            (Nat.card (W1 ⊔ W2 : Subgroup G) : ℚ) =
          1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
            1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ) := by
      have hW1posNat : 0 < Nat.card W1 := Nat.card_pos (α := W1)
      have hW2posNat : 0 < Nat.card W2 := Nat.card_pos (α := W2)
      have hW1one : 1 ≤ Nat.card W1 := Nat.succ_le_of_lt hW1posNat
      have hW2one : 1 ≤ Nat.card W2 := Nat.succ_le_of_lt hW2posNat
      have hW1pos : (0 : ℚ) < Nat.card W1 := by exact_mod_cast hW1posNat
      have hW2pos : (0 : ℚ) < Nat.card W2 := by exact_mod_cast hW2posNat
      rw [hhat_ncard, hden]
      repeat rw [Nat.cast_mul]
      rw [Nat.cast_sub hW1one, Nat.cast_sub hW2one]
      field_simp [hW1pos.ne', hW2pos.ne']
      ring_nf
    exact le_of_eq hvalue
  have hHV :
      (((theorem_10_8_countingHVSupportSet SF V).ncard : ℚ) /
          (Nat.card G : ℚ)) ≤
        ((Nat.card SF : ℚ) / (Nat.card Smax : ℚ) +
          (1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
            1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ))) := by
    simpa [theorem_10_8_countingHVSupportSet] using
      theorem_10_8_counting_union_ratio_bound
        (G := G)
        (X := section16ConjugatesOfSetBySet
          (Section7.puncturedSubgroupSet SF) Set.univ)
        (Y := section16ConjugatesOfSetBySet V Set.univ)
        (a := (Nat.card SF : ℚ) / (Nat.card Smax : ℚ))
        (b := 1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
          1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ))
        hH hVratio
  exact theorem_10_8_counting_ratio_le_of_subset_ratio_le hsubset hHV

public theorem theorem_10_8_counting_rho_gap_and_g1_support_bound_supported_source
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
    {Smax SF U : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hfrob : section12FrobeniusJoinWithKernel SF U)
    (hTypePAlign : Section8.typePDefinitionData Smax SF U W2 W1) :
    ∃ g1 : ℕ,
      (1 : ℚ) - ((g1 : ℚ) / (Nat.card G : ℚ)) - 1 / (Nat.card W1 : ℚ) <
          ((Nat.card W1 : ℚ) / (Nat.card (ambientDerivedSubgroup M) : ℚ)) ∧
        ((g1 : ℚ) / (Nat.card G : ℚ)) ≤
          ((Nat.card SF : ℚ) / (Nat.card Smax : ℚ) +
            (1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
              1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ))) := by
  rcases theorem_10_8_counting_tildeA_supported_source h104 with ⟨tildeA, hTilde⟩
  let g1 : ℕ := (theorem_10_8_countingG1Set tildeA W1).ncard
  refine ⟨g1, ?_, ?_⟩
  · simpa [g1] using theorem_10_8_counting_rho_gap_supported_source h104 hTilde
  · simpa [g1] using
      theorem_10_8_counting_G1_support_bound_supported_source
        h104 hSmax hSF hTypeII hsemi hfrob hTypePAlign hTilde

public theorem theorem_10_8_counting_ratio_support_estimate_supported_source
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
    {Smax SF U : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hfrob : section12FrobeniusJoinWithKernel SF U)
    (hTypePAlign : Section8.typePDefinitionData Smax SF U W2 W1) :
    ((Nat.card W1 : ℚ) / (Nat.card (ambientDerivedSubgroup M : Subgroup G) : ℚ)) >
      1 - ((Nat.card SF : ℚ) / (Nat.card Smax : ℚ) +
        (1 - 1 / (Nat.card W2 : ℚ) - 1 / (Nat.card W1 : ℚ) +
          1 / ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ))) -
        1 / (Nat.card W1 : ℚ) := by
  rcases theorem_10_8_counting_rho_gap_and_g1_support_bound_supported_source
      h104 hSmax hSF hTypeII hsemi hfrob hTypePAlign with
    ⟨g1, hgap, hg1⟩
  exact theorem_10_8_counting_ratio_support_estimate_of_g1_bounds
    (m := Nat.card (ambientDerivedSubgroup M))
    (w1 := Nat.card W1)
    (w2 := Nat.card W2)
    (sf := Nat.card SF)
    (s := Nat.card Smax)
    (g1 := g1)
    (g := Nat.card G)
    hgap hg1

public theorem theorem_10_8_counting_ratio_half_supported_source
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
    {Smax SF U : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hfrob : section12FrobeniusJoinWithKernel SF U)
    (hTypePAlign : Section8.typePDefinitionData Smax SF U W2 W1) :
    (1 / 2 : ℚ) <
      ((Nat.card W1 * Nat.card W2 : ℕ) : ℚ) /
        (Nat.card (ambientDerivedSubgroup M) : ℚ) := by
  have hUlower :
      2 * Nat.card W2 + 1 ≤ Nat.card U :=
    frobeniusJoin_kernel_card_ge_two_mul_complement_add_one
      (typePDefinitionData_frobeniusJoinWithKernel hTypePAlign
        (frobeniusJoin_complement_ne_bot hfrob))
  have hUseven : 7 ≤ Nat.card U := by
    have hW2three : 3 ≤ Nat.card W2 :=
      card_W2_ge_three_of_hypothesis_10_4_supported_data h104
    omega
  exact theorem_10_8_counting_ratio_half_of_bound
    (m := Nat.card (ambientDerivedSubgroup M))
    (w1 := Nat.card W1)
    (w2 := Nat.card W2)
    (u := Nat.card U)
    (Nat.card_pos (α := ambientDerivedSubgroup M))
    (card_W1_ge_three_of_hypothesis_10_4_supported_data h104)
    (Nat.card_pos (α := W2))
    hUseven
    (theorem_10_8_counting_ratio_bound_of_support_estimate
      (m := Nat.card (ambientDerivedSubgroup M))
      (w1 := Nat.card W1)
      (w2 := Nat.card W2)
      (u := Nat.card U)
      (sf := Nat.card SF)
      (s := Nat.card Smax)
      (Nat.card_pos (α := W1))
      (Nat.card_pos (α := W2))
      (Nat.card_pos (α := U))
      (Nat.card_pos (α := SF))
      (theorem_10_8_counting_selected_Smax_card_eq hsemi hTypePAlign)
      (theorem_10_8_counting_ratio_support_estimate_supported_source
        h104 hSmax hSF hTypeII hsemi hfrob hTypePAlign))

public theorem theorem_10_8_counting_estimates_supported_source
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
    {Smax SF U : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hfrob : section12FrobeniusJoinWithKernel SF U)
    (hTypePAlign : Section8.typePDefinitionData Smax SF U W2 W1) :
    2 * Nat.card W1 + 1 ≤
        (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) ∧
      Nat.card W2 ≤ Nat.card (section16SecondDerivedSubgroup M) ∧
        Nat.card (ambientDerivedSubgroup M) <
          2 * Nat.card W1 * Nat.card W2 := by
  have hquotes :
      2 * Nat.card W1 + 1 ≤
          (section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M) ∧
        Nat.card (ambientDerivedSubgroup M) <
          2 * Nat.card W1 * Nat.card W2 :=
    ⟨theorem_10_8_counting_quotient_lower_bound_supported_source h104,
      theorem_10_8_counting_strict_upper_of_ratio_half
        (m := Nat.card (ambientDerivedSubgroup M))
        (w1 := Nat.card W1)
        (w2 := Nat.card W2)
        (Nat.card_pos (α := ambientDerivedSubgroup M))
        (theorem_10_8_counting_ratio_half_supported_source
          h104 hSmax hSF hTypeII hsemi hfrob hTypePAlign)⟩
  rcases hquotes with ⟨hquot, hlt⟩
  exact ⟨hquot, theorem_10_8_counting_secondDerived_card_lower_bound_supported h104,
    hlt⟩

public theorem theorem_10_8_counting_cardinality_bounds_supported_source
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
    {Smax SF U : Subgroup G}
    (hSmax : Smax ∈ section9MaximalSubgroups G)
    (hSF : section16MFSubgroup Smax SF)
    (hTypeII : section16TypeII Smax SF)
    (hsemi : Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U)
    (hfrob : section12FrobeniusJoinWithKernel SF U)
    (hTypePAlign : Section8.typePDefinitionData Smax SF U W2 W1) :
    ∃ q r : ℕ,
      Nat.card (ambientDerivedSubgroup M) = q * r ∧
        2 * Nat.card W1 + 1 ≤ q ∧
          Nat.card W2 ≤ r ∧
            Nat.card (ambientDerivedSubgroup M) <
              2 * Nat.card W1 * Nat.card W2 := by
  rcases theorem_10_8_counting_estimates_supported_source
      h104 hSmax hSF hTypeII hsemi hfrob hTypePAlign with
    ⟨hquot, hsecond, hlt⟩
  refine ⟨(section16SecondDerivedSubgroup M).relIndex (ambientDerivedSubgroup M),
    Nat.card (section16SecondDerivedSubgroup M), ?_, hquot, hsecond, hlt⟩
  exact theorem_10_8_ambientDerived_card_eq_secondDerived_relIndex_mul_card M

public theorem theorem_10_7_hypothesis_9_5_pair_core_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    {U W1S W2S U1 U0 : Subgroup G}
    (_hPData : Section8.typePData Smax SF U W1S W2S)
    (_hTypeP : Section8.typePDefinitionData Smax SF U W1S W2S)
    (_hTypeIIToIV : Section8.typeIIToIVSourceCondition Smax U W1S)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ Smax)
    (_hF : Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0) :
    ∃ H0 C Cprime : Subgroup G,
      ∃ T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G,
      ∃ S9 : Finset (Section1.ClassFunction Smax),
        Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9 ∧
          Section5.hypothesis_5_2_statement S9 T ∧
            theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T := by
  have h92 : Section9.hypothesis_9_2_statement Smax SF U W1S W2S (Nat.card W1S) :=
    theorem_10_7_hypothesis_9_2_pair_source_data
      _hSmax _hSF _hTypeII _hPData _hTypeP _hTypeIIToIV _hUcomm _hUnorm _hF
  rcases Section9.theorem_9_4 Smax SF U W1S W2S (Nat.card W1S) h92 with
    ⟨H0, p, hpData⟩
  rcases theorem_10_7_kernelInducedFamily_tail_source_data h92 p hpData with
    ⟨S9, hKernel⟩
  rcases Section9.msChoice_of_hypothesis_9_2_sec9 Smax SF U W1S W2S h92 with
    ⟨Ms, hMs⟩
  rcases theorem_10_7_quotientCentralizerIn_tail_source_data
      _hSmax _hSF _hTypeII _hTypeP _hTypeIIToIV _hUcomm _hUnorm h92
      p hpData with
    ⟨C, hC⟩
  rcases theorem_10_7_section8_fullData_dade_tail_source_data
      _hSmax _hSF _hTypeII h92 hMs with
    ⟨d52, hDade⟩
  have hS9ne : S9.Nonempty :=
    theorem_10_7_kernelInducedFamily_nonempty_tail_source_data
      h92 p hpData S9 hKernel
  have hS8 : Section8.section8InducedNonkernelFamily Smax Ms S9 :=
    Section9.section8InducedNonkernelFamily_of_kernelInducedFamily_msChoice_nonempty_sec9
      Smax SF U W1S W2S Ms H0 S9 h92 hMs hKernel hS9ne
  have h52 : Section5.hypothesis_5_2_statement S9 d52.tau :=
    Section8.theorem_8_15_hypothesis_5_2_of_fullData
      (G := G) (M := Smax) (Ms := Ms) (W1 := W1S) (W2 := W2S)
      (A := Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms)
      (S := S9) (by infer_instance : IsMinCE G) d52 hS8
  have hBarU : ∃ u : ℕ, Section9.quotientBarUCardinality U C u :=
    theorem_10_7_exists_quotientBarUCardinality_of_quotientCentralizerIn
      _hUcomm hC
  rcases h52 with ⟨hsetup, R5, h52a, h52b, h52c, h52d, h52e⟩
  let Cprime : Subgroup G := (_root_.commutator C).map C.subtype
  have hCprime_le : Cprime ≤ C := by
    simpa [Cprime] using theorem_10_7_commutator_map_subtype_le_self C
  have hCprime_eq : Cprime = (_root_.commutator C).map C.subtype := rfl
  exact
    ⟨H0, C, Cprime, d52.tau, S9,
      theorem_10_7_hypothesis_9_5_of_tail_fields h92 ⟨p, hpData⟩
        hC hBarU hCprime_le hCprime_eq hDade hKernel h52b,
      ⟨hsetup, R5, h52a, h52b, h52c, h52d, h52e⟩,
      ⟨Ms, hMs, d52, rfl⟩⟩

public theorem theorem_10_7_forbidden_character_reducible_partner_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (u : ℕ)
    (_hBarU : Section9.quotientBarUCardinality U C u)
    (χ : Section1.ClassFunction Smax)
    (_hχ_mem :
      χ ∈
        Section9.kernelInducedSubfamily_sec9 Smax
          (ambientDerivedSubgroup Smax) SF (H0 ⊔ Cprime) S9)
    (_hχ_forbidden :
      Section9.degreeQuIrreducibleFromLinearHC
        Smax SF C (Nat.card W1S) u χ) :
    ∃ ν : Section1.ClassFunction Smax,
      ν ∈ S9 ∧
        ¬ Section1.IsIrreducibleCharacterOnGroup ν ∧
          Section1.degree ν = Section1.degree χ := by
  classical
  have h95Full := _h95
  rcases _h95 with
    ⟨h92, hp95, hCcentralizer, _hBarU95, hCprimeC, hCprimeEq, _hDade, hS,
      _h52b⟩
  rcases hp95 with ⟨p, hpData⟩
  have hp96 :
      ∃ hp' : Nat.Primes,
        hp'.val = p.val ∧
          Section9.hoReductionData Smax SF U W2S H0 hp' ∧
            Section9.quotientChiefFactorData_9_6 Smax SF H0 W1S hp' := by
    refine ⟨p, rfl, hpData, ?_⟩
    rcases Section9.theorem_9_6_source_core_sec9
        Smax SF U W1S W2S H0 C Cprime T S9 p h95Full hpData with
      ⟨_hUC, hchief, hWbar2, hcard⟩
    exact Section9.quotientChiefFactorData_9_6_of_source_facts
      Smax SF U W1S W2S H0 p h92 hpData hchief hWbar2 hcard
  rcases h92.typeP with ⟨_hSFtype, hcommon⟩
  rcases hcommon with
    ⟨_hHallD, _hSFleD, hcomp, _hUnil, _hW1norm, _hW1cyc, _hW1card,
      _hSFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hPrimeCentralizer⟩
  let N : Subgroup G := ambientDerivedSubgroup Smax
  have hS_N : Section9.kernelInducedFamily Smax N SF H0 S9 := by
    simpa [N] using hS
  have hUN : U ≤ N := by
    simpa [N] using Section9.complement_le_right_sec9 hcomp
  have hCN : C ≤ N := hCcentralizer.1.trans hUN
  have hCprimeN : Cprime ≤ N := hCprimeC.trans hCN
  have hH0C_N : H0 ⊔ C ≤ N := sup_le hS_N.1 hCN
  have hH0Cprime_N : H0 ⊔ Cprime ≤ N := sup_le hS_N.1 hCprimeN
  let SH0C : Finset (Section1.ClassFunction Smax) :=
    Section9.kernelInducedSubfamily_sec9 Smax N SF (H0 ⊔ C) S9
  have hSH0C_N :
      Section9.kernelInducedFamily Smax N SF (H0 ⊔ C) SH0C :=
    Section9.kernelInducedFamily_subfamily_of_le_sec9
      Smax N SF H0 (H0 ⊔ C) S9 hH0C_N le_sup_left hS_N
  have hSH0C :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF
        (H0 ⊔ C) SH0C := by
    simpa [N, SH0C] using hSH0C_N
  let SH0Cprime : Finset (Section1.ClassFunction Smax) :=
    Section9.kernelInducedSubfamily_sec9 Smax N SF (H0 ⊔ Cprime) S9
  have hSH0Cprime_N :
      Section9.kernelInducedFamily Smax N SF (H0 ⊔ Cprime) SH0Cprime :=
    Section9.kernelInducedFamily_subfamily_of_le_sec9
      Smax N SF H0 (H0 ⊔ Cprime) S9 hH0Cprime_N le_sup_left hS_N
  have hSH0Cprime :
      Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF
        (H0 ⊔ Cprime) SH0Cprime := by
    simpa [N, SH0Cprime] using hSH0Cprime_N
  rcases Section9.theorem_9_7_source_core_sec9
      Smax SF U W1S W2S H0 C p.val (Nat.card W1S) u
      h92 hp96 hCcentralizer _hBarU with
    hcaseA | hcaseB
  · rcases hcaseA with ⟨a, hcaseA⟩
    let Uprime : Subgroup G := (_root_.commutator U).map U.subtype
    have hUprimeU : Uprime ≤ U := by
      intro x hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hUprimeN : Uprime ≤ N := hUprimeU.trans hUN
    have hH0Uprime_N : H0 ⊔ Uprime ≤ N := sup_le hS_N.1 hUprimeN
    let SH0U : Finset (Section1.ClassFunction Smax) :=
      Section9.kernelInducedSubfamily_sec9 Smax N SF (H0 ⊔ Uprime) S9
    have hSH0U_N :
        Section9.kernelInducedFamily Smax N SF (H0 ⊔ Uprime) SH0U :=
      Section9.kernelInducedFamily_subfamily_of_le_sec9
        Smax N SF H0 (H0 ⊔ Uprime) S9 hH0Uprime_N le_sup_left hS_N
    have hSH0U :
        Section9.kernelInducedFamily Smax (ambientDerivedSubgroup Smax) SF
          (H0 ⊔ Uprime) SH0U := by
      simpa [N, SH0U] using hSH0U_N
    have hchar :
        Section9.case_9_7_a_characterData
          Smax SF U H0 C Uprime p.val (Nat.card W1S) a u S9 SH0C SH0U :=
      (Section9.theorem_9_8
        Smax SF U W1S W2S H0 C Uprime p.val (Nat.card W1S) a u
        S9 SH0C SH0U hcaseA _hBarU rfl hS hSH0C hSH0U).2
    rcases hchar with ⟨_hdiv, _hUnderlyingDiv, _hbarU, hR, _hχ, _hI⟩
    rcases hR with ⟨R, hRcard, hRdata, _hRsubSH0C, _hRlin⟩
    exact theorem_10_7_reducible_partner_of_subfamily_card
      p.property hRcard hRdata _hχ_forbidden.2.1
  · have hchar :
        Section9.case_9_7_b_characterData
          Smax SF H0 C p.val (Nat.card W1S) u S9 SH0C SH0Cprime :=
      (Section9.theorem_9_9
        Smax SF U W1S W2S H0 C Cprime p.val (Nat.card W1S) u
        S9 SH0C SH0Cprime hcaseB hCprimeEq hS hSH0C hSH0Cprime).2
    rcases hchar with ⟨_hdiv, _hdegreeInduced, hR, _hnoIrreducible⟩
    rcases hR with ⟨R, hRcard, hRdata, _hRsubSH0C⟩
    exact theorem_10_7_reducible_partner_of_subfamily_card
      p.property hRcard hRdata _hχ_forbidden.2.1

public theorem theorem_10_7_tau_muColumn_sub_smul_xi_eq_column_sum_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    {j : J}
    (hj : j ≠ j0) :
    τ (muColumn μ j - (d : ℂ) • ξ) =
      (δ : ℂ) • (∑ i : I, σ (ω i j)) - (d : ℂ) • τ₁ ξ := by
  have hagree :
      τ₁ (muColumn μ j - (d : ℂ) • ξ) =
        τ (muColumn μ j - (d : ℂ) • ξ) :=
    tauOne_muColumn_sub_smul_xi_eq_tau_of_hypothesis_10_4_supported_data_local
      h hj
  have hcol :
      τ₁ (muColumn μ j) = (δ : ℂ) • (∑ i : I, σ (ω i j)) :=
    theorem_10_6_nonbase_column_formula_obligation_supported_source h j hj
  calc
    τ (muColumn μ j - (d : ℂ) • ξ) =
        τ₁ (muColumn μ j - (d : ℂ) • ξ) := hagree.symm
    _ = τ₁ (muColumn μ j) - (d : ℂ) • τ₁ ξ := by
          simp
    _ = (δ : ℂ) • (∑ i : I, σ (ω i j)) - (d : ℂ) • τ₁ ξ := by
          rw [hcol]

public theorem theorem_10_7_omega_column_row_scalarProduct_eq_one_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
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
    (hnotation : section10FourSixNotationSupportedData M W1 W2 W A A0 i0 j0
      μ δSign ω σ τ)
    (r : I)
    (s : J) :
    Section1.scalarProduct G
      (∑ i : I, σ (ω i s))
      (∑ j : J, σ (ω r j)) = 1 := by
  classical
  have hleft :
      ((∑ i : I, σ (ω i s) : Section1.ClassFunction G)) =
        fun g => ∑ i : I, σ (ω i s) g := by
    ext g
    simp
  have hright :
      ((∑ j : J, σ (ω r j) : Section1.ClassFunction G)) =
        fun g => ∑ j : J, σ (ω r j) g := by
    ext g
    simp
  rw [hleft, Section1.scalarProduct_fintype_sum_left]
  simp_rw [hright, Section1.scalarProduct_fintype_sum_right]
  calc
    (∑ i : I, ∑ j : J,
        Section1.scalarProduct G (σ (ω i s)) (σ (ω r j))) =
        ∑ i : I, ∑ j : J, if (i, s) = (r, j) then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact scalarProduct_sigma_omega_eq_pair_ite_of_section10FourSixNotationSupportedData
            hnotation i r s j
    _ = ∑ i : I, if i = r then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hir : i = r
          · subst i
            simp
          · simp [hir]
    _ = 1 := by
          simp

public theorem theorem_10_7_tauOne_xi_orthogonal_omegaRowSum_supported
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (r : I) :
    Section1.scalarProduct G (τ₁ ξ) (∑ j : J, σ (ω r j)) = 0 := by
  classical
  have hright :
      ((∑ j : J, σ (ω r j) : Section1.ClassFunction G)) =
        fun g => ∑ j : J, σ (ω r j) g := by
    ext g
    simp
  rw [hright, Section1.scalarProduct_fintype_sum_right]
  simp [tauOne_xi_orthogonal_sigma_omega_of_hypothesis_10_4_supported_data_local h]

public theorem theorem_10_7_scalar_contradiction_from_partner_image_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax : Subgroup G}
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
      i0 j0 μ δSign ω σ d n δ)
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {χ ν : Section1.ClassFunction Smax}
    {s : J}
    (_hs : s ≠ j0)
    {r : I}
    {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1)
    (hT4ν : T4 ν = (ε : ℂ) • (∑ j : J, σ (ω r j)))
    (hσχ :
      ∀ i j, Section1.scalarProduct G (σ (ω i j)) (T4 χ) = 0)
    (hτχ : Section1.scalarProduct G (τ₁ ξ) (T4 χ) = 0)
    (hzero :
      Section1.scalarProduct G
        ((δ : ℂ) • (∑ i : I, σ (ω i s)) - (d : ℂ) • τ₁ ξ)
        (T4 (ν - χ)) = 0) :
    False := by
  classical
  have hnotation := section10FourSixNotation_of_hypothesis_10_4_supported_data h
  have hcolrow :
      Section1.scalarProduct G
        (∑ i : I, σ (ω i s))
        (∑ j : J, σ (ω r j)) = 1 :=
    theorem_10_7_omega_column_row_scalarProduct_eq_one_supported hnotation r s
  have hxirow :
      Section1.scalarProduct G (τ₁ ξ) (∑ j : J, σ (ω r j)) = 0 :=
    theorem_10_7_tauOne_xi_orthogonal_omegaRowSum_supported h r
  have hcolχ :
      Section1.scalarProduct G (∑ i : I, σ (ω i s)) (T4 χ) = 0 :=
    theorem_10_7_omegaColumn_orthogonal_of_pointwise hσχ s
  have heval :
      Section1.scalarProduct G
        ((δ : ℂ) • (∑ i : I, σ (ω i s)) - (d : ℂ) • τ₁ ξ)
        (T4 (ν - χ)) = (δ : ℂ) * star (ε : ℂ) := by
    rw [map_sub, hT4ν]
    rw [Section5.scalarProduct_sub_left, Section5.scalarProduct_sub_right,
      Section5.scalarProduct_sub_right]
    simp [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right,
      hcolrow, hcolχ, hxirow, hτχ]
    ring
  have hδ : δ = 1 ∨ δ = -1 := by
    rcases uniformMuData_of_hypothesis_10_4_supported_data h with
      ⟨_hI, _hJ, _hprime, _hd, hδ, _hn, _hdeg, _hsign, _hdn⟩
    exact hδ
  have hprod0 : (δ : ℂ) * star (ε : ℂ) = 0 := by
    rw [heval] at hzero
    exact hzero
  rcases hδ with hδ | hδ <;> rcases hε with hε | hε <;>
    subst δ <;> subst ε <;> norm_num at hprod0

public theorem theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ) :
    Section8.typeIIIDefinitionData M MF ∨
      Section8.typeIVDefinitionData M MF ∨
        Section8.typeVDefinitionData M MF := by
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  exact theorem_10_7_late_source_type_of_typeIIIIVVData hType

public theorem theorem_10_7_mf_eq_of_hypothesis_10_1_supported_and_notation_8_10
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF MFsrc Ms : Subgroup G}
    {W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {A A0 A1 : Set G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hNotation : Section8.notation_8_10_source_data M MFsrc Ms A A0 A1) :
    MFsrc = MF := by
  rcases h10 with
    ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
      _h46, _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, _U, hP, _hCases⟩
  exact section16MFSubgroup_unique hNotation.2.1 hP.1

public theorem theorem_10_7_supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    {χ : Section1.ClassFunction M}
    (hχS : χ ∈ S) :
    Section1.supportedOn χ ((derivedSubgroup M : Subgroup M) : Set M) := by
  rcases h10 with
    ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation10, _h52⟩
  rcases (hS χ).mp hχS with ⟨θ, _hθirr, _hθne, rfl⟩
  exact inducedCF_supportedOn_subgroup (derivedSubgroup M) θ

public theorem theorem_10_7_integerSpanOn_supportedOn_A1_preimage_of_hypothesis_10_4_supported_data
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
    (h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    {Ms : Subgroup G}
    {Abook A0book A1book : Set G}
    (hNotation : Section8.notation_8_10_source_data M MF Ms Abook A0book A1book)
    (α : Section1.ClassFunction M)
    (hα : Section5.integerSpanOn S Section5.puncturedSet α) :
    Section1.supportedOn α (Section8.section8SubgroupSetPreimage M A1book) := by
  classical
  have h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data h104
  have hTail := theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data h10
  have hA1eq :
      A1book = section16NonidentityElements (ambientDerivedSubgroup M : Set G) :=
    theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
      hNotation hTail
  have hDerived :
      Section1.supportedOn α ((derivedSubgroup M : Subgroup M) : Set M) :=
    theorem_10_7_supportedOn_of_integerSpan_generators
      (fun χ hχ =>
        theorem_10_7_supportedOn_derivedSubgroup_of_mem_hypothesis_10_1_supported_data
          h10 hχ)
      hα.1
  have hPunct : Section1.supportedOn α Section5.puncturedSet := hα.2
  rw [Section1.supportedOn_iff]
  intro x hxA1
  by_cases hx1 : x = 1
  · exact (Section1.supportedOn_iff.mp hPunct) x (by
      simp [Section5.puncturedSet, hx1])
  by_cases hxD : x ∈ ((derivedSubgroup M : Subgroup M) : Set M)
  · have hxDsub : x ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [section12_ambientDerivedSubgroup_subgroupOf_eq] using hxD
    have hxDG : (x : G) ∈ ambientDerivedSubgroup M := hxDsub
    have hxGne : (x : G) ≠ 1 := by
      intro hxG
      exact hx1 (Subtype.ext hxG)
    have hxA1G : (x : G) ∈ A1book := by
      rw [hA1eq]
      exact ⟨hxDG, hxGne⟩
    have hxA1pre : x ∈ Section8.section8SubgroupSetPreimage M A1book := by
      simpa [Section8.section8SubgroupSetPreimage] using hxA1G
    exact False.elim (hxA1 hxA1pre)
  · exact (Section1.supportedOn_iff.mp hDerived) x hxD

public theorem theorem_10_7_A_subset_A_of_late_notation_8_10_source_data_supported
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
  have hTail := theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data h10
  have hBookA :
      Abook = A1book :=
    theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data hBook hTail
  have hTildeA :
      Atilde = A1tilde :=
    theorem_10_7_A_eq_A1_of_late_notation_8_10_source_data hTilde hTail
  have hBookA1 :
      A1book = section16NonidentityElements (ambientDerivedSubgroup M : Set G) :=
    theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
      hBook hTail
  have hTildeA1 :
      A1tilde = section16NonidentityElements (ambientDerivedSubgroup M : Set G) :=
    theorem_10_7_A1_eq_derived_nonidentity_of_late_notation_8_10_source_data
      hTilde hTail
  intro x hx
  rw [hTildeA, hTildeA1]
  rw [hBookA, hBookA1] at hx
  exact hx

public theorem theorem_10_7_selectedDadeComplement_mem_D_of_not_centralizer_le_supported
    {G : Type u}
    [Group G]
    [Finite G]
    {M MF W1 W2 MsBook MsTilde : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {Abook A0book A1book Atilde A0tilde A1tilde D tildeA tildeA0 tildeA1 : Set G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {R : G → Subgroup G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hBook :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book A1book)
    (hTilde :
      Section8.notation_8_10_source_data M MF MsTilde Atilde A0tilde A1tilde)
    (h14 :
      Section8.notation_8_14_source_data M Atilde A0tilde A1tilde
        D tildeA tildeA0 tildeA1 R)
    {a : G}
    (ha : a ∈ Abook)
    (hCentM : ¬ Subgroup.centralizer ({a} : Set G) ≤ M) :
    a ∈ D := by
  have hAbookAtilde :
      Abook ⊆ Atilde :=
    theorem_10_7_A_subset_A_of_late_notation_8_10_source_data_supported
      h10 hBook hTilde
  have hNotLe :
      ¬ Subgroup.centralizer ({a} : Set G) ≤ M := hCentM
  rcases h14 with
    ⟨_hA1A, hAA0, hD, _hRbot, _hUnique, _hReq, _htildeA,
      _htildeA0, _htildeA1⟩
  rw [hD]
  exact ⟨hAA0 (hAbookAtilde ha), hNotLe⟩

public theorem theorem_10_7_selectedDadeComplement_le_tildeR_source_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 MsBook MsTilde : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {Abook A0book A1book Atilde A0tilde A1tilde D tildeA tildeA0 tildeA1 : Set G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {H_A0 R : G → Subgroup G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hBook :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book A1book)
    (hTilde :
      Section8.notation_8_10_source_data M MF MsTilde Atilde A0tilde A1tilde)
    (h14 :
      Section8.notation_8_14_source_data M Atilde A0tilde A1tilde
        D tildeA tildeA0 tildeA1 R)
    (hA0M : Section2.Hypothesis2 A0book M H_A0)
    (_hτ : ∀ α : Section1.ClassFunction M,
      Section2.CFOn M A0book α →
        τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) :
    ∀ a : G, a ∈ Abook → H_A0 a ≤ R a := by
  have hAbookA0book : Abook ⊆ A0book :=
    theorem_10_7_A_subset_A0_of_notation_8_10_source_data hBook
  have hAbookAtilde : Abook ⊆ Atilde :=
    theorem_10_7_A_subset_A_of_late_notation_8_10_source_data_supported
      h10 hBook hTilde
  have h14Data := h14
  rcases h14 with
    ⟨_hA1A, hAtildeA0tilde, hD, hRbot, _hUnique, hReq, _htildeA,
      _htildeA0, _htildeA1⟩
  intro a ha h hh
  have haA0tilde : a ∈ A0tilde := hAtildeA0tilde (hAbookAtilde ha)
  by_cases hCentM : Subgroup.centralizer ({a} : Set G) ≤ M
  · have hHbot : H_A0 a ≤ ⊥ :=
      theorem_10_7_hypothesis2_complement_le_bot_of_centralizer_le
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
      theorem_10_7_selectedDadeComplement_mem_D_of_not_centralizer_le_supported
        h10 hBook hTilde h14Data ha hCentM
    rcases Section8.theorem_8_15_support_of_mem_D
        (G := G) (M := M) (MF := MF) (Ms := MsTilde)
        (A := Atilde) (A0 := A0tilde) (A1 := A1tilde)
        (D := D) (tildeA := tildeA) (tildeA0 := tildeA0)
        (tildeA1 := tildeA1) (R := R)
        (hG := inferInstance) hTilde h14Data haD with
      ⟨L, LF, hSupp, _hReq⟩
    rcases hSupp with
      ⟨_hLmax, hLF, hSet, _hSemiL, _hSemiC, _hCoprime, _hType⟩
    have hHleCentLF : H_A0 a ≤ elementCentralizerIn LF a :=
      by
        have hHprod :
            Section2.IsInternalSemidirectProduct (Section2.elementCentralizer a)
              (H_A0 a) (Section2.centralizerIn M a) :=
          hA0M.centralizer_eq_product (hAbookA0book ha)
        have hSemiC' :
            Section8.section8SemidirectProductIn (Section2.elementCentralizer a)
              (elementCentralizerIn LF a) (Section2.centralizerIn M a) := by
          simpa [Section2.elementCentralizer, Section2.centralizerIn,
            elementCentralizerIn] using _hSemiC
        exact theorem_10_7_left_le_left_of_common_coprime_complement hHprod hSemiC'
          (hA0M.coprime_orders (hAbookA0book ha) (hAbookA0book ha))
    have hR : R a = elementCentralizerIn LF a :=
      hReq a haD L LF hSet hLF
    rw [hR]
    exact hHleCentLF hh

public theorem theorem_10_7_selectedDadeComplement_le_tildeR_on_late_A1_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {M MF W1 W2 MsBook MsTilde : Subgroup G}
    {V : Set G}
    {S : Finset (Section1.ClassFunction M)}
    {Abook A0book A1book Atilde A0tilde A1tilde D tildeA tildeA0 tildeA1 : Set G}
    {τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G}
    {H_A0 R : G → Subgroup G}
    (h10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ)
    (hBook :
      Section8.notation_8_10_source_data M MF MsBook Abook A0book A1book)
    (hTilde :
      Section8.notation_8_10_source_data M MF MsTilde Atilde A0tilde A1tilde)
    (h14 :
      Section8.notation_8_14_source_data M Atilde A0tilde A1tilde
        D tildeA tildeA0 tildeA1 R)
    (hA0M : Section2.Hypothesis2 A0book M H_A0)
    (hτ : ∀ α : Section1.ClassFunction M,
      Section2.CFOn M A0book α →
        τ α = Section2.dadeTransform H_A0 hA0M.subset_L α) :
    ∀ a : G, a ∈ A1tilde → H_A0 a ≤ R a := by
  have hTail := theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data h10
  have hA1TildeAtilde : A1tilde ⊆ Atilde :=
    theorem_10_7_A1_subset_A_of_late_notation_8_10_source_data hTilde hTail
  have hAtildeAbook : Atilde ⊆ Abook :=
    theorem_10_7_A_subset_A_of_late_notation_8_10_source_data_supported
      h10 hTilde hBook
  have hHleBook :
      ∀ a : G, a ∈ Abook → H_A0 a ≤ R a :=
    theorem_10_7_selectedDadeComplement_le_tildeR_source_supported
      h10 hBook hTilde h14 hA0M hτ
  intro a ha
  exact hHleBook a (hAtildeAbook (hA1TildeAtilde ha))

public theorem theorem_10_7_support_orthogonality_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9) :
    ∀ α : Section1.ClassFunction M,
      Section5.integerSpanOn S Section5.puncturedSet α →
        ∀ β : Section1.ClassFunction Smax,
          Section5.integerSpanOn S9 Section5.puncturedSet β →
            Section1.scalarProduct G (τ α) (T β) = 0 := by
  intro α hα β hβ
  rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h104 with
    ⟨MFsrc, Ms, AM, A0M, A1M, hSource10, _hW, _hA0,
      _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull⟩
  rcases hSource10 with
    ⟨_hApre, _hA0pre, hNotation10, H_A0, hA0M, hτ_dade⟩
  have hHyp10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  have hMFsrc_eq : MFsrc = MF :=
    theorem_10_7_mf_eq_of_hypothesis_10_1_supported_and_notation_8_10
      hHyp10 hNotation10
  subst MFsrc
  have hTail := theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data
    hHyp10
  have hA1A : A1M ⊆ AM :=
    theorem_10_7_A1_subset_A_of_late_notation_8_10_source_data
      hNotation10 hTail
  have hAA0 : AM ⊆ A0M :=
    theorem_10_7_A_subset_A0_of_notation_8_10_source_data hNotation10
  rcases Section8.exists_mixed_notation_8_14_source_data_of_theorem_8_13
      M MF Ms AM A0M A1M (by infer_instance : IsMinCE G)
      hNotation10 hA1A hAA0 with
    ⟨RM, tildeAM, tildeA0M, tildeA1M, h14M⟩
  have hnotI : ¬ Section8.typeIDefinitionData Smax SF :=
    Section8.not_typeIDefinitionData_of_typeP_source_data
      _h95.hypothesis92.typePDefinitionData
  have hNotConj : ¬ section16ConjugateSubgroupsIn ⊤ M Smax := by
    intro hConj
    rcases hHyp10 with
      ⟨_hM, _hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
        _h46h, _hNotationh, _h52h⟩
    have hMF : section16MFSubgroup M MF := hNotation10.2.1
    have hNotTypeII : ¬ Section8.typeIIDefinitionData M MF :=
      (section10_source_not_typeI_typeII_of_msChoice_tail
        hNotation10.2.2.1 hTail).2
    rcases hConj with ⟨g, _hg, hSmax_eq⟩
    subst Smax
    have hSrcIIConj : Section8.typeIIDefinitionData (M.conjBy g) SF :=
      Section8.theorem_8_8_typeII_to_source_public
        (G := G) _hSmax _hSF _hTypeII
    have hSrcII : Section8.typeIIDefinitionData M MF :=
      Section8.theorem_8_18_typeIIDefinitionData_conj_back
        g hMF _hSF hSrcIIConj
    exact hNotTypeII hSrcII
  have hNoSupport : ∀ g : G,
      ¬ Section8.supportsSubgroupSource M (Smax.conjBy g)
        (Section8.section8DSet M A0M) := by
    rcases hHyp10 with
      ⟨_hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, _hDade,
        _h46h, _hNotationh, _h52h⟩
    rcases hType with ⟨_hVeq, Up, hP, _hCases⟩
    have hnotFrob : ¬ Section8.section8FrobeniusGroupWithKernel M MF :=
      theorem_10_7_typeP_not_section8FrobeniusGroupWithKernel hP
    have h13 :=
      Section8.theorem_8_13 M MF Ms AM A0M A1M A0M
        (by infer_instance) hNotation10 (Or.inr rfl)
    have hDM : Section8.section8DSet M A0M = Section8.section8DSet M A0M := rfl
    intro g hSupp
    rcases hSupp with ⟨hLmax, x, hxDM, hxCent⟩
    have hxD : x ∈ Section8.section8DSet M A0M := by
      simpa [hDM] using hxDM
    have hLmem :
        Smax.conjBy g ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({x} : Set G)) :=
      ⟨hLmax, hxCent⟩
    rcases h13.2.2.2 x hxD (Smax.conjBy g) hLmem with ⟨LF, hSuppData⟩
    rcases hSuppData with
      ⟨_hLmax, hLF, _hUnique, _hSemiL, _hSemiC, _hCoprime, hCases⟩
    rcases hCases with hTypeI | hTypeII
    · exact hnotI
        (Section8.theorem_8_18_typeIDefinitionData_conj_back
          (G := G) (M := Smax) (MF := SF) (LF := LF) g _hSF hLF hTypeI.1)
    · exact hnotFrob hTypeII.2.2
  rcases theorem_10_7_exists_notation_8_10_of_typeII_not_typeI_source_data
      _hTypeII _h95.hypothesis92 hnotI with
    ⟨AS, A0S, A1S, h10S⟩
  rcases theorem_10_7_exists_notation_8_14_of_typeII_notation_8_10_source_data
      _hTypeII _h95.hypothesis92 h10S with
    ⟨DS, tildeAS, tildeA0S, tildeA1S, RS, h14S⟩
  have h18Notation :
      Section8.theorem_8_18_source_notation_data M Smax MF SF Ms SF
        AM A0M A1M (Section8.section8DSet M A0M) tildeAM tildeA0M tildeA1M
        AS A0S A1S DS tildeAS tildeA0S tildeA1S RM RS :=
    ⟨hNotConj, hNotation10, h10S, h14M, h14S⟩
  have hASetAS :
      section16ASet Smax U ⊆ AS :=
    theorem_10_7_section16ASet_subset_AS_of_typeII_notation_8_10_source_data
      _hTypeII _h95.hypothesis92 h10S
  have hβCFOn :
      Section2.CFOn Smax (section16ASet Smax U) β :=
    theorem_10_7_CFon_of_integerSpanOn_kernelInducedFamily_ASet
      _h95.hypothesis92 _h95.kernelInduced hβ
  have hαA1M :
      Section1.supportedOn α (Section8.section8SubgroupSetPreimage M A1M) :=
    theorem_10_7_integerSpanOn_supportedOn_A1_preimage_of_hypothesis_10_4_supported_data
      _h104 hNotation10 α hα
  have hH_A0_le_RM :
      ∀ a : G, a ∈ A1M → H_A0 a ≤ RM a :=
    theorem_10_7_selectedDadeComplement_le_tildeR_on_late_A1_supported
      hHyp10 hNotation10 hNotation10 h14M hA0M hτ_dade
  have hDadeSupportM :
      Section2.dadeSupport A1M H_A0 ⊆ tildeA1M :=
    theorem_10_7_dadeSupport_subset_tildeA1_of_notation_8_14_and_H_le
      h14M hH_A0_le_RM
  have hαClass : Section1.IsClassFunction α := by
    rcases hα.1 with ⟨v, rfl⟩
    refine theorem_10_7_isClassFunction_evalCoeff
      (fun X : S => (X : Section1.ClassFunction M)) ?_ v
    intro X
    rcases hHyp10 with
      ⟨_hM, _hType, hS, _hW1, _hW2, _hW12, _hDade, _h46, _hNotation, _h52⟩
    rcases (hS (X : Section1.ClassFunction M)).mp X.property with
      ⟨θ, _hθirr, _hθne, hX⟩
    simpa [hX] using Section1.inducedCF_isClassFunction (derivedSubgroup M) θ
  have hA1A0 : A1M ⊆ A0M := hA1A.trans hAA0
  have hαCFOn : Section2.CFOn M A0M α := by
    refine ⟨hαClass, ?_⟩
    intro l hl
    exact (Section1.supportedOn_iff.mp hαA1M) l (by
      intro hlA1
      exact hl (hA1A0 (by simpa [Section8.section8SubgroupSetPreimage] using hlA1)))
  have hτ : Section1.supportedOn (τ α) tildeA1M := by
    rw [hτ_dade α hαCFOn]
    exact
      theorem_10_7_dadeTransform_supportedOn_of_supportedOn_subgroup_preimage_of_dadeSupport_subset
        hA0M.subset_L α hαA1M hDadeSupportM
  rcases _h95.dade with ⟨H95, hAMG95, hT_dade95⟩
  have hHleRS :
      ∀ a : G, a ∈ section16ASet Smax U → H95 a ≤ RS a :=
    theorem_10_7_hypothesis2_le_tildeR_of_subset_notation_8_14
      h10S h14S hASetAS hAMG95
  have hDadeSupport :
      Section2.dadeSupport (section16ASet Smax U) H95 ⊆ tildeAS :=
    theorem_10_7_dadeSupport_subset_tildeA_of_notation_8_14_and_H_le
      h14S hASetAS hHleRS
  have hT : Section1.supportedOn (T β) tildeAS := by
    rw [hT_dade95 β hβCFOn]
    exact theorem_10_7_dadeTransform_supportedOn_of_dadeSupport_subset
      hAMG95.subset_L β hDadeSupport
  have h18 :=
    Section8.theorem_8_18 M Smax MF SF Ms SF
      AM A0M A1M (Section8.section8DSet M A0M) tildeAM tildeA0M tildeA1M
      AS A0S A1S DS tildeAS tildeA0S tildeA1S RM RS
      (by infer_instance : IsMinCE G) h18Notation
  rcases h18 with ⟨_hSupportInter, _hCentralizer, hConjSupportInter, _hDisjAlt⟩
  have hNoInter : ¬ (tildeA1M ∩ tildeAS).Nonempty := by
    intro hInter
    rcases hConjSupportInter.2 hInter with ⟨g, hSupport⟩
    exact hNoSupport g hSupport
  have hDisjoint : Disjoint tildeA1M tildeAS := by
    rw [Set.disjoint_iff]
    intro x hx
    exact False.elim (hNoInter ⟨x, hx⟩)
  exact theorem_10_7_scalarProduct_eq_zero_of_disjoint_supports hτ hT hDisjoint

public theorem xi_sub_conjugate_tauOne_eq_tau_of_hypothesis_10_4_supported_data
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
    (h : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    τ₁ (ξ - Section1.conjugateCharacter ξ) =
      τ (ξ - Section1.conjugateCharacter ξ) := by
  rcases hypothesis_10_4_a_of_hypothesis_10_4_supported_data h with
    ⟨h10, _hNotation, hξS, _hξIrr, hξDegree, _hUniform⟩
  have h52a : Section5.hypothesis_5_2_a_statement S :=
    hypothesis_5_2_a_of_hypothesis_10_1_supported_data h10
  have hξbarS : Section1.conjugateCharacter ξ ∈ S :=
    (h52a ⟨ξ, hξS⟩).1
  have hdeg :
      Section1.degree ξ =
        Section1.degree (Section1.conjugateCharacter ξ) := by
    calc
      Section1.degree ξ = (Nat.card W1 : ℂ) := hξDegree
      _ = star (Nat.card W1 : ℂ) := by simp
      _ = Section1.degree (Section1.conjugateCharacter ξ) := by
        rw [← hξDegree]
        simp [Section1.degree, Section1.conjugateCharacter]
  simpa using
    coherentExtension_agreesOn_sub_of_mem_of_degree_eq
      (coherentExtension_of_hypothesis_10_4_supported_data h)
      hξS hξbarS hdeg

public theorem theorem_10_7_typeP_pair_witness_reverse_supported_source_data
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ) :
    ∃ Wcase Smax Tmax SF TF U U1 U0 : Subgroup G,
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tmax Smax TF SF ∧
        section16TypeII Smax SF ∧
          Section8.typePDefinitionData Smax SF U W2 W1 ∧
            Section8.typeIIToIVSourceCondition Smax U W2 ∧
              IsMulCommutative U ∧
                (¬ Subgroup.normalizer (U : Set G) ≤ Smax) ∧
                  Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0 ∧
                    Tmax = M := by
  classical
  have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases h10 with
    ⟨hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, hDade, _h46,
      _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, Usource, hP, hCases⟩
  rcases hDade with ⟨Ms, _Abook, _A0book, _A1book, _H, hNotation, _hA0M, _hτ⟩
  have hPFull : Section8.typePDefinitionData M MF Usource W1 W2 := hP
  rcases hPFull with
    ⟨hMF, _hW1cyc, hW1ne, _hW1hall, hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      _hW2leInf, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF := by
    rcases hCases with hIII | hIV | hV
    · exact Or.inl
        ⟨Usource, W1, W2, hP, hIII.1, hIII.2.1, hIII.2.2⟩
    · exact Or.inr <| Or.inl
        ⟨Usource, W1, W2, hP, hIV.1, hIV.2.1, hIV.2.2⟩
    · exact Or.inr <| Or.inr
        ⟨Usource, W1, W2, hP, hV.1, hV.2⟩
  have hSourceLateM :
      Section8.typeIIDefinitionData M MF ∨
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF :=
    Or.inr hTail
  have hMs : Section8.msChoiceSource M MF Ms := hNotation.2.2.1
  rcases Section8.sourceTypeP_exists_KUData_of_aligned_complement
      (G := G) hM hP with
    ⟨Uc, hKU⟩
  have hCaseP1 : section16CaseP1 W1 Uc :=
    section10_caseP1_of_msChoice_tail
      (G := G) (M := M) (MF := MF) (W1 := W1) (Uc := Uc) (Ms := Ms)
      hM hMF hMs hKU hTail
  have hC : section16TheoremCConclusions M MF W1 Uc :=
    theorem_16_C (G := G) hM hMF hKU hCaseP1.1
  let Kstar : Subgroup G := section16Kstar M W1
  rcases hC with
    ⟨_hUcommM, _hNormM, _hKstarCyclic, hKstarPos, _hKstarMF,
      _hMFnotCyclic, _hDerEq, _hKstarSecond, Mstar, hMstarP, _hUnique,
      hKstarStar, hKstarHall, _hPrimeX, _hPrimeY, hInter, hProd, hZcyc,
      hCase, hCover, hHatTI, _hHatEq, _hHatTISubset, _hKprimeIfUne,
      _hKstarPrimeIfBot⟩
  have hKstar_eq_W2 : Kstar = W2 := by
    dsimp [Kstar]
    exact theorem_10_7_section16Kstar_eq_W2_of_source_typeP hM hP
  have hKstarStar_eq_W1 : section16Kstar Mstar Kstar = W1 := by
    dsimp [Kstar]
    exact hKstarStar.symm
  have hKstarStarW2_eq_W1 : section16Kstar Mstar W2 = W1 := by
    rw [← hKstar_eq_W2]
    exact hKstarStar_eq_W1
  have hMstarP2 : Mstar ∈ section14MFamilyP2 G := by
    rcases hCase with hCaseP2 | hMstarP2
    · exact False.elim (hCaseP2.2 hCaseP1.2)
    · simpa [section16MaximalTypeP2] using hMstarP2
  have hMstarMax : Mstar ∈ section9MaximalSubgroups G := hMstarP.1
  rcases section16_exists_mfSubgroup (G := G) Mstar with ⟨SF, hSF⟩
  rcases section16_exists_KUData_of_kappa_hall
      (G := G) (M := Mstar) (K := Kstar) hMstarP hKstarHall with
    ⟨U, hKUT⟩
  have hTypeIIMstar : section16TypeII Mstar SF :=
    section16_typeII_of_MFamilyP2 (G := G) hSF hKUT hMstarP2
  rcases Section8.theorem_8_8_typeII_to_source_with_KUData_public
      (G := G) (M := Mstar) (MF := SF) (K := Kstar) (U := U)
      hMstarMax hSF hKUT hTypeIIMstar with
    ⟨U1, U0, _hPData, hTypePsrc, hTypeIIToIVsrc, hUcomm, hUnorm, hF⟩
  have hTypePAlign : Section8.typePDefinitionData Mstar SF U W2 W1 := by
    simpa [hKstar_eq_W2, hKstarStarW2_eq_W1] using hTypePsrc
  have hTypeIIToIVAlign : Section8.typeIIToIVSourceCondition Mstar U W2 := by
    simpa [hKstar_eq_W2] using hTypeIIToIVsrc
  have hTypeIIDefMstar : Section8.typeIIDefinitionData Mstar SF :=
    ⟨U, Kstar, section16Kstar Mstar Kstar, U1, U0, hTypePsrc,
      hTypeIIToIVsrc, hUcomm, hUnorm, hF⟩
  have hCompMstar :
      section12ComplementIn Mstar Kstar (ambientDerivedSubgroup Mstar) := by
    simpa [section16KappaPrimes] using
      theorem_14_7_h (G := G) (M := Mstar) (K := Kstar) hMstarP
        (by simpa [section16KappaPrimes] using hKstarHall)
  let Wcase : Subgroup G := section16ZSubgroup W1 W2
  have hZcycW : IsCyclic (W1 ⊔ W2 : Subgroup G) := by
    rw [← hKstar_eq_W2]
    exact hZcyc
  have hProdW : section12InternalDirectProduct W1 W2 Wcase := by
    simpa [Wcase, Kstar, hKstar_eq_W2, section16ZSubgroup] using hProd
  have hCycW : IsCyclic Wcase := by
    change IsCyclic (W1 ⊔ W2 : Subgroup G)
    exact hZcycW
  have hW2ne : W2 ≠ ⊥ := by
    simpa [← hKstar_eq_W2] using (ne_of_gt hKstarPos)
  have hNormalizer :
      ∀ W0 : Set G,
        W0.Nonempty →
          W0 ⊆ (Wcase : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) →
            Subgroup.normalizer W0 = Wcase := by
    intro W0 hW0ne hW0sub
    have hHatWTI :
        section16TISubsetWithNormalizer (section16HatW W1 W2)
          (W1 ⊔ W2 : Subgroup G) := by
      simpa [Kstar, hKstar_eq_W2, section16HatW, section16HatZ,
        section16ZSubgroup] using hHatTI
    have hWcomm : IsMulCommutative (W1 ⊔ W2 : Subgroup G) := by
      have hCyc : IsCyclic (W1 ⊔ W2 : Subgroup G) := by
        exact hZcycW
      let _ : IsCyclic (W1 ⊔ W2 : Subgroup G) := hCyc
      infer_instance
    have hW0subHat : W0 ⊆ section16HatW W1 W2 := by
      simpa [Wcase, section16HatW, section16ZSubgroup] using hW0sub
    simpa [Wcase, section16ZSubgroup] using
      section16_hatW_subset_normalizer_eq_of_ti
        (G := G) hHatWTI hWcomm hW0ne hW0subHat
  have hSeq : M = ambientDerivedSubgroup M ⊔ W1 := hMcomp.2.2.1
  have hSdisj : Disjoint (ambientDerivedSubgroup M) W1 := hMcomp.2.2.2
  have hTeq : Mstar = ambientDerivedSubgroup Mstar ⊔ W2 := by
    calc
      Mstar = Kstar ⊔ ambientDerivedSubgroup Mstar := hCompMstar.2.2.1
      _ = ambientDerivedSubgroup Mstar ⊔ Kstar :=
        sup_comm Kstar (ambientDerivedSubgroup Mstar)
      _ = ambientDerivedSubgroup Mstar ⊔ W2 := by rw [hKstar_eq_W2]
  have hTdisj : Disjoint (ambientDerivedSubgroup Mstar) W2 := by
    rw [← hKstar_eq_W2]
    exact hCompMstar.2.2.2.symm
  have hST : M ⊓ Mstar = Wcase := by
    simpa [Wcase, Kstar, hKstar_eq_W2, section16ZSubgroup] using hInter
  have hCoverSource :
      ∀ N : Subgroup G, N ∈ section9MaximalSubgroups G →
        (∃ g : G, N = M.conjBy g) ∨
          (∃ g : G, N = Mstar.conjBy g) ∨
            ∃ NF : Subgroup G, section16MFSubgroup N NF ∧
              Section8.typeIDefinitionData N NF := by
    intro N hN
    by_cases hNP : N ∈ section14MFamilyP G
    · rcases hCover N (by simpa [section16MaximalTypeP] using hNP) with hNM | hNMstar
      · exact Or.inl hNM
      · exact Or.inr <| Or.inl hNMstar
    · rcases section16_exists_mfSubgroup (G := G) N with ⟨NF, hNF⟩
      exact Or.inr <| Or.inr <|
        ⟨NF, hNF,
          Section8.theorem_8_8_typeI_to_source_public
            (G := G) hN hNF (section16_typeI_of_not_MFamilyP (G := G) hN hNF hNP)⟩
  have hcase :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 M Mstar MF SF := by
    exact ⟨hProdW, hCycW, hW1ne, hW2ne, hNormalizer, hM, hMstarMax,
      hMF, hSF, hSeq, hTeq, hSdisj, hTdisj, hST, Or.inr hTypeIIDefMstar,
      hSourceLateM, Or.inl hTypeIIDefMstar, hCoverSource⟩
  exact ⟨Wcase, Mstar, M, SF, MF, U, U1, U0, hcase, hTypeIIMstar,
    hTypePAlign, hTypeIIToIVAlign, hUcomm, hUnorm, hF, rfl⟩

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_pair_xdefW_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G}
    (_hcasePair :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair)
    (_hTypeIIPair : section16TypeII Spair SFpair)
    (_hTypePPair : Section8.typePDefinitionData Spair SFpair Upair W2 W1)
    (_hTypeIIToIVPair : Section8.typeIIToIVSourceCondition Spair Upair W2)
    (_hUcommPair : IsMulCommutative Upair)
    (_hUnormPair : ¬ Subgroup.normalizer (Upair : Set G) ≤ Spair)
    (_hFPair : Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair)
    (gPair : G)
    (_hSmax_eq_Spair : Smax = Spair.conjBy gPair)
    (_hSF_eq : SF = SFpair.conjBy gPair)
    (hW1S_eq : W1S = W2.conjBy gPair) :
    W1S = W2.conjBy gPair ∧ W2S = W1.conjBy gPair := by
  classical
  have hW1S :
      W1S = W2.conjBy gPair :=
    hW1S_eq
  have hLF : section16MFSubgroup (Spair.conjBy gPair) SF := by
    simpa [_hSmax_eq_Spair] using _hSF
  have hPconj :
      Section8.typePDefinitionData (Spair.conjBy gPair) SF U W1S W2S := by
    simpa [_hSmax_eq_Spair] using _h95.hypothesis92.typePDefinitionData
  have hSFpair : section16MFSubgroup Spair SFpair := by
    rcases _hcasePair with
      ⟨_hprodPair, _hcycPair, _hW1nePair, _hW2nePair, _hnormPair,
        _hTpairMax, _hSpairMax, _hTFpair, hSFpair, _hrest⟩
    exact hSFpair
  have hPback :
      Section8.typePDefinitionData Spair SFpair
        (U.conjBy gPair⁻¹) (W1S.conjBy gPair⁻¹) (W2S.conjBy gPair⁻¹) :=
    Section8.theorem_8_18_typePDefinitionData_conj_back
      (G := G) (M := Spair) (MF := SFpair) (LF := SF)
      (U := U) (W1 := W1S) (W2 := W2S) gPair hSFpair hLF hPconj
  have hW1back : W1S.conjBy gPair⁻¹ = W2 := by
    rw [hW1S]
    exact section11_conjBy_inv (G := G) W2 gPair
  have hPback' :
      Section8.typePDefinitionData Spair SFpair
        (U.conjBy gPair⁻¹) W2 (W2S.conjBy gPair⁻¹) := by
    simpa [hW1back] using hPback
  have hcaseSwap :
      Section8.theorem_8_8_source_case_b_data Wcase W2 W1 Spair Tpair SFpair TFpair :=
    Section8.theorem_8_8_source_case_b_data_swap _hcasePair
  have hW2Sback :
      W1 = W2S.conjBy gPair⁻¹ :=
    (Section8.theorem_8_9 (G := G) Wcase W2 W1 Spair Tpair SFpair TFpair
      (U.conjBy gPair⁻¹) (W2S.conjBy gPair⁻¹)) hcaseSwap hPback'
  have hW2S : W2S = W1.conjBy gPair := by
    have hconj :=
      congrArg (fun H : Subgroup G => H.conjBy gPair) hW2Sback.symm
    calc
      W2S = (W2S.conjBy gPair⁻¹).conjBy gPair :=
        (section11_conjBy_inv' (G := G) W2S gPair).symm
      _ = W1.conjBy gPair := hconj
  exact ⟨hW1S, hW2S⟩

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_pair_carrier_equiv_with_apply_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G}
    (_hcasePair :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair)
    (_hTypeIIPair : section16TypeII Spair SFpair)
    (_hTypePPair : Section8.typePDefinitionData Spair SFpair Upair W2 W1)
    (_hTypeIIToIVPair : Section8.typeIIToIVSourceCondition Spair Upair W2)
    (_hUcommPair : IsMulCommutative Upair)
    (_hUnormPair : ¬ Subgroup.normalizer (Upair : Set G) ≤ Spair)
    (_hFPair : Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair)
    (gPair : G)
    (_hSmax_eq_Spair : Smax = Spair.conjBy gPair)
    (_hSF_eq : SF = SFpair.conjBy gPair)
    (hW1S_eq : W1S = W2.conjBy gPair) :
    ∃ e : W ≃* d52.W,
      ∀ x : W, (((e x : d52.W) : Smax) : G) =
        gPair * ((x : M) : G) * gPair⁻¹ := by
  classical
  rcases theorem_10_7_typeP_partner_cyclicTI_selected_pair_xdefW_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
      _h95 _hMs _hT_eq _hcasePair _hTypeIIPair _hTypePPair
      _hTypeIIToIVPair _hUcommPair _hUnormPair _hFPair gPair
      _hSmax_eq_Spair _hSF_eq hW1S_eq with
    ⟨hW1S, hW2S⟩
  have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases h10 with
    ⟨_hM, _hType, _hFamily, _hW1M, _hW2M, hW12M, _hDade,
      _h46exists, _hNotationExists, _h52⟩
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h104
  rcases hNotation with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
      hWloc, _hA010, _h46, _hω10, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, _hFull10⟩
  have hW12Spair : W1 ⊔ W2 ≤ Spair := by
    rcases _hTypePPair with
      ⟨hSFpair, _hW2cyc, _hW2ne, hW2Hall, _hSpairComp,
        _hUpairDer, _hUnil, _hW2norm, _hDerComp, _hSFnoncyc,
        _hSecond, _hFit, _hFitLe, hW1le, _hW1cyc, _hW1ne,
        _hCentralizer, _hNormalizer⟩
    have hSFpair_le : SFpair ≤ Spair := by
      rcases hSFpair.1 with ⟨hSFpair_le, _hSFpair_normal, _hSFpair_nilpotent,
        _hSFpair_hall⟩
      exact hSFpair_le
    have hW2_le : W2 ≤ Spair := hW2Hall.1
    have hW1_le : W1 ≤ Spair := ((le_inf_iff.mp hW1le).1).trans hSFpair_le
    exact sup_le hW1_le hW2_le
  have hconjSup :
      (W1 ⊔ W2).conjBy gPair = W1S ⊔ W2S := by
    calc
      (W1 ⊔ W2).conjBy gPair =
          W1.conjBy gPair ⊔ W2.conjBy gPair := by
            change (W1 ⊔ W2).map (MulAut.conj gPair).toMonoidHom =
              W1.map (MulAut.conj gPair).toMonoidHom ⊔
                W2.map (MulAut.conj gPair).toMonoidHom
            rw [Subgroup.map_sup]
      _ = W2S ⊔ W1S := by
            rw [hW1S, hW2S, sup_comm]
      _ = W1S ⊔ W2S := by
            rw [sup_comm]
  have hWsupS : W1S ⊔ W2S ≤ Smax := by
    rw [← hconjSup, _hSmax_eq_Spair]
    exact Subgroup.map_mono hW12Spair
  let eLoc : W ≃* ((W1 ⊔ W2).subgroupOf M) :=
    MulEquiv.subgroupCongr hWloc
  let eAmb : ((W1 ⊔ W2).subgroupOf M) ≃* (W1 ⊔ W2 : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe (H := W1 ⊔ W2) (K := M) hW12M
  let eConj : (W1 ⊔ W2 : Subgroup G) ≃* (W1 ⊔ W2).conjBy gPair :=
    theorem_10_7_conjByMulEquiv (W1 ⊔ W2) gPair
  let eSel : (W1 ⊔ W2).conjBy gPair ≃* (W1S ⊔ W2S : Subgroup G) :=
    MulEquiv.subgroupCongr hconjSup
  let eSub : (W1S ⊔ W2S : Subgroup G) ≃* ((W1S ⊔ W2S).subgroupOf Smax) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1S ⊔ W2S) (K := Smax) hWsupS).symm
  let eD52 : ((W1S ⊔ W2S).subgroupOf Smax) ≃* d52.W :=
    MulEquiv.subgroupCongr d52.W_eq.symm
  let e : W ≃* d52.W :=
    ((eLoc.trans eAmb).trans eConj).trans (eSel.trans (eSub.trans eD52))
  refine ⟨e, ?_⟩
  intro x
  simp [e, eLoc, eAmb, eConj, eSel, eSub, eD52,
    theorem_10_7_conjByMulEquiv, Subgroup.subgroupOfEquivOfLe,
    MulEquiv.subgroupCongr_apply]

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_alignment_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau) :
    ∃ Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G,
      ∃ gPair : G,
        Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair ∧
          section16TypeII Spair SFpair ∧
            Section8.typePDefinitionData Spair SFpair Upair W2 W1 ∧
              Section8.typeIIToIVSourceCondition Spair Upair W2 ∧
                IsMulCommutative Upair ∧
                  (¬ Subgroup.normalizer (Upair : Set G) ≤ Spair) ∧
                    Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair ∧
                      Smax = Spair.conjBy gPair ∧
                        SF = SFpair.conjBy gPair ∧
                          W1S = W2.conjBy gPair := by
  classical
  rcases theorem_10_7_typeP_pair_witness_reverse_supported_source_data
      _h104 with
    ⟨Wcase, Spair, Tpair, SFpair, TFpair, Upair, U1pair, U0pair,
      hcasePair, hTypeIIPair, hTypePPair, hTypeIIToIVPair, hUcommPair,
      hUnormPair, hFPair, hTpair_eq_M⟩
  have hcasePairFull := hcasePair
  rcases hcasePair with
    ⟨_hprodPair, _hcycPair, _hW1nePair, _hW2nePair, _hnormPair,
      _hTpairMax, _hSpairMax, _hTFpair, hSFpair, _hTpairSeq,
      _hSpairSeq, _hTpairDisj, _hSpairDisj, _hInterPair,
      _hTypeEither, _hTpairSource, _hSpairSource, hCover⟩
  have hHyp10 : hypothesis_10_1_supported_data M MF W1 W2 V S τ :=
    hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  have hNotation10 := section10FourSixNotation_of_hypothesis_10_4_supported_data
    _h104
  rcases hNotation10 with
    ⟨MFsrc, Ms10, AM10, A0M10, A1M10, hSource10, _hW10, _hA010,
      _h46, _h33, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull⟩
  rcases hSource10 with
    ⟨_hApre, _hA0pre, hNotationM, _H_A0, _hA0M, _hτ_dade⟩
  have hMFsrc_eq : MFsrc = MF :=
    theorem_10_7_mf_eq_of_hypothesis_10_1_supported_and_notation_8_10
      hHyp10 hNotationM
  subst MFsrc
  have hTail :=
    theorem_10_7_late_source_type_of_hypothesis_10_1_supported_data hHyp10
  have hNotConj : ¬ section16ConjugateSubgroupsIn ⊤ M Smax := by
    intro hConj
    have hMF : section16MFSubgroup M MF := hNotationM.2.1
    have hNotTypeII : ¬ Section8.typeIIDefinitionData M MF :=
      (section10_source_not_typeI_typeII_of_msChoice_tail
        hNotationM.2.2.1 hTail).2
    rcases hConj with ⟨g, _hg, hSmax_eq⟩
    subst Smax
    have hSrcIIConj : Section8.typeIIDefinitionData (M.conjBy g) SF :=
      Section8.theorem_8_8_typeII_to_source_public
        (G := G) _hSmax _hSF _hTypeII
    have hSrcII : Section8.typeIIDefinitionData M MF :=
      Section8.theorem_8_18_typeIIDefinitionData_conj_back
        g hMF _hSF hSrcIIConj
    exact hNotTypeII hSrcII
  have hnotI : ¬ Section8.typeIDefinitionData Smax SF :=
    Section8.not_typeIDefinitionData_of_typeP_source_data
      _h95.hypothesis92.typePDefinitionData
  rcases hCover Smax _hSmax with hTpair | hRest
  · rcases hTpair with ⟨g, hSmax_eq_Tpair⟩
    exfalso
    exact hNotConj ⟨g, by simp, by simpa [hTpair_eq_M] using hSmax_eq_Tpair⟩
  rcases hRest with hSpair | hTypeI
  · rcases hSpair with ⟨g0, hSmax_eq_Spair0⟩
    have hSFpairg :
        section16MFSubgroup (Spair.conjBy g0) (SFpair.conjBy g0) :=
      Section8.theorem_8_18_mfSubgroup_conjBy (G := G) g0 hSFpair
    have hSFpairS :
        section16MFSubgroup Smax (SFpair.conjBy g0) := by
      simpa [hSmax_eq_Spair0] using hSFpairg
    have hSF_eq0 : SF = SFpair.conjBy g0 :=
      section16MFSubgroup_unique _hSF hSFpairS
    have hLF : section16MFSubgroup (Spair.conjBy g0) SF := by
      simpa [hSmax_eq_Spair0] using _hSF
    have hPconj :
        Section8.typePDefinitionData (Spair.conjBy g0) SF U W1S W2S := by
      simpa [hSmax_eq_Spair0] using _h95.hypothesis92.typePDefinitionData
    have hPback :
        Section8.typePDefinitionData Spair SFpair
          (U.conjBy g0⁻¹) (W1S.conjBy g0⁻¹) (W2S.conjBy g0⁻¹) :=
      Section8.theorem_8_18_typePDefinitionData_conj_back
        (G := G) (M := Spair) (MF := SFpair) (LF := SF)
        (U := U) (W1 := W1S) (W2 := W2S) g0 hSFpair hLF hPconj
    rcases theorem_10_7_typeP_outer_complements_conj_source_data
        hTypePPair hPback with
      ⟨dPair, hW1back⟩
    let gPair : G := g0 * (dPair : G)
    have hdSpair : (dPair : G) ∈ Spair := dPair.property
    have hSpair_d : Spair.conjBy (dPair : G) = Spair :=
      section11_conjBy_eq_of_mem_normalizer (G := G)
        ((Subgroup.le_normalizer : Spair ≤ Subgroup.normalizer (Spair : Set G))
          hdSpair)
    have hSmax_eq : Smax = Spair.conjBy gPair := by
      calc
        Smax = Spair.conjBy g0 := hSmax_eq_Spair0
        _ = (Spair.conjBy (dPair : G)).conjBy g0 := by rw [hSpair_d]
        _ = Spair.conjBy (g0 * (dPair : G)) :=
          section11_conjBy_conjBy (G := G) Spair (dPair : G) g0
    have hSFpair_norm : Spair ≤ Subgroup.normalizer (SFpair : Set G) := by
      rcases hSFpair.1 with ⟨hSFpair_le, hSFpair_normal, _hSFpair_nil,
        _hSFpair_hall⟩
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSFpair_le).1
        hSFpair_normal
    have hSFpair_d : SFpair.conjBy (dPair : G) = SFpair :=
      section11_conjBy_eq_of_mem_normalizer (G := G)
        (hSFpair_norm hdSpair)
    have hSF_eq : SF = SFpair.conjBy gPair := by
      calc
        SF = SFpair.conjBy g0 := hSF_eq0
        _ = (SFpair.conjBy (dPair : G)).conjBy g0 := by rw [hSFpair_d]
        _ = SFpair.conjBy (g0 * (dPair : G)) :=
          section11_conjBy_conjBy (G := G) SFpair (dPair : G) g0
    have hW1S_eq : W1S = W2.conjBy gPair := by
      have hconj :=
        congrArg (fun H : Subgroup G => H.conjBy g0) hW1back
      calc
        W1S = (W1S.conjBy g0⁻¹).conjBy g0 :=
          (section11_conjBy_inv' (G := G) W1S g0).symm
        _ = (W2.conjBy (dPair : G)).conjBy g0 := hconj
        _ = W2.conjBy (g0 * (dPair : G)) :=
          section11_conjBy_conjBy (G := G) W2 (dPair : G) g0
    exact ⟨Wcase, Spair, Tpair, SFpair, TFpair, Upair, U1pair, U0pair,
      gPair, hcasePairFull, hTypeIIPair, hTypePPair, hTypeIIToIVPair,
      hUcommPair, hUnormPair, hFPair, hSmax_eq, hSF_eq, hW1S_eq⟩
  · rcases hTypeI with ⟨NF, hNF, hI⟩
    have hNF_eq_SF : NF = SF := section16MFSubgroup_unique hNF _hSF
    exfalso
    exact hnotI (by simpa [hNF_eq_SF] using hI)

public theorem theorem_10_7_sigma_omega_signed_of_hypothesis_10_4_supported_data
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
    (h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (i : I)
    (j : J) :
    Section3.IsSignedIrreducibleCharacter (σ (ω i j)) := by
  classical
  rcases section10FourSixNotation_of_hypothesis_10_4_supported_data h104 with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
      _hW10, _hA010, _h46, hω10, hIso10, hVirt10, _hPrin10,
      _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull10⟩
  have hvirtW : IsVirtualCharacter (ω i j) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hω10.irreducible i j)
  have hvirtG : IsVirtualCharacter (σ (ω i j)) :=
    hVirt10 (ω i j) hvirtW
  have hself :
      Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) = 1 := by
    calc
      Section1.scalarProduct G (σ (ω i j)) (σ (ω i j)) =
          Section1.scalarProduct W (ω i j) (ω i j) :=
            hIso10 _ _ (hω10.is_class i j) (hω10.is_class i j)
      _ = 1 := by
        simpa using hω10.orthonormal (i, j) (i, j)
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirtG hself

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_source_restrict_nonprincipal_supported_source_data
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (i : I)
    (j : J)
    (_hNonprincipal : i ≠ i0 ∨ j ≠ j0) :
    ∀ z : M,
      ∀ hz : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
        σ (ω i j) (z : G) =
          (ω i j) ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hz⟩ := by
  classical
  rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h104 with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
      _hW10, _hA010, _h46, hω10, _hIso10, _hVirt10, _hPrin10,
      _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull10⟩
  exact sigma_agrees_cyclicTI_of_hypothesis_10_4_supported_data _h104
    (ω i j) (hω10.is_class i j)

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_source_restrict_supported_source_data
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (i : I)
    (j : J) :
    ∀ z : M,
      ∀ hz : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
        σ (ω i j) (z : G) =
          (ω i j) ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hz⟩ := by
  classical
  by_cases hi : i = i0
  · by_cases hj : j = j0
    · subst i
      subst j
      intro z hz
      rcases section10FourSixNotation_of_hypothesis_10_4_supported_data _h104 with
        ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
          _hW10, _hA010, _h46, hω10, _hIso10, _hVirt10, hPrin10,
          _h45, _h48, _hTauA0, _hFull10⟩
      simp [hω10.principal, hPrin10, Section1.principalCharacter]
    · exact
        theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_source_restrict_nonprincipal_supported_source_data
          _h104 i j (Or.inr hj)
  · exact
      theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_source_restrict_nonprincipal_supported_source_data
        _h104 i j (Or.inl hi)

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_transport_signed_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G}
    (_hcasePair :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair)
    (_hTypeIIPair : section16TypeII Spair SFpair)
    (_hTypePPair : Section8.typePDefinitionData Spair SFpair Upair W2 W1)
    (_hTypeIIToIVPair : Section8.typeIIToIVSourceCondition Spair Upair W2)
    (_hUcommPair : IsMulCommutative Upair)
    (_hUnormPair : ¬ Subgroup.normalizer (Upair : Set G) ≤ Spair)
    (_hFPair : Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair)
    (gPair : G)
    (_hSmax_eq_Spair : Smax = Spair.conjBy gPair)
    (_hSF_eq : SF = SFpair.conjBy gPair)
    (_hW1S_eq : W1S = W2.conjBy gPair)
    (e : W ≃* d52.W)
    (_he :
      ∀ x : W, (((e x : d52.W) : Smax) : G) =
        gPair * ((x : M) : G) * gPair⁻¹)
    (i : I)
    (j : J) :
    Section3.IsSignedIrreducibleCharacter
      (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j))) := by
  classical
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h104
  rcases hNotation with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
      _hW10, _hA010, _h46, hω10, _hIso10, _hVirt10, _hPrin10,
      _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull10⟩
  rcases d52.fullHypothesis with
    ⟨_h46d, _hW2K, _h31d, hIsoD, hVirtD, _hClassD, _hPrinD, _h22A,
      _hFullRest⟩
  have htransportIrr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    Section6.theorem_6_8_transportClassFunction_irreducible e
      (hω10.irreducible i j)
  have htransportClass :
      Section1.IsClassFunction
        (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    Section6.theorem_6_8_transportClassFunction_isClass e
      (hω10.is_class i j)
  have htransportVirt :
      IsVirtualCharacter
        (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup htransportIrr
  have hImageVirt :
      IsVirtualCharacter
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j))) :=
    hVirtD _ htransportVirt
  have hselfW :
      Section1.scalarProduct W (ω i j) (ω i j) = 1 := by
    simpa using hω10.orthonormal (i, j) (i, j)
  have hself :
      Section1.scalarProduct G
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)))
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j))) = 1 := by
    calc
      Section1.scalarProduct G
          (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)))
          (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j))) =
        Section1.scalarProduct d52.W
          (Section6.theorem_6_8_transportClassFunction e (ω i j))
          (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
          hIsoD _ _ htransportClass htransportClass
      _ = Section1.scalarProduct W (ω i j) (ω i j) :=
          Section6.theorem_6_8_scalarProduct_transportClassFunction e (ω i j) (ω i j)
      _ = 1 := hselfW
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hImageVirt hself

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_selected_restrict_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G}
    (_hcasePair :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair)
    (_hTypeIIPair : section16TypeII Spair SFpair)
    (_hTypePPair : Section8.typePDefinitionData Spair SFpair Upair W2 W1)
    (_hTypeIIToIVPair : Section8.typeIIToIVSourceCondition Spair Upair W2)
    (_hUcommPair : IsMulCommutative Upair)
    (_hUnormPair : ¬ Subgroup.normalizer (Upair : Set G) ≤ Spair)
    (_hFPair : Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair)
    (gPair : G)
    (_hSmax_eq_Spair : Smax = Spair.conjBy gPair)
    (_hSF_eq : SF = SFpair.conjBy gPair)
    (hW1S_eq : W1S = W2.conjBy gPair)
    (e : W ≃* d52.W)
    (he :
      ∀ x : W, (((e x : d52.W) : Smax) : G) =
        gPair * ((x : M) : G) * gPair⁻¹)
    (i : I)
    (j : J) :
    ∀ z : M,
      ∀ hz : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
        d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) (z : G) =
          (ω i j) ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hz⟩ := by
  classical
  intro z hz
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h104
  rcases hNotation with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
      _hW10, _hA010, _h46, hω10, _hIso10, _hVirt10, _hPrin10,
      _hσAgreeCyc, _h45, _h48, _hTauA0, _hFull10⟩
  rcases d52.fullHypothesis with
    ⟨_h46d, _hW2K, _h31d, _hIsoD, _hVirtD, hClassD, _hPrinD, _h22A,
      _hFullRest⟩
  have hclass : Section1.IsClassFunction
      (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    Section6.theorem_6_8_transportClassFunction_isClass e
      (hω10.is_class i j)
  have hsigmaClass : Section1.IsClassFunction
      (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j))) :=
    hClassD _ hclass
  have hzW : z ∈ (W : Set M) :=
    Section3.cyclicTISet_subset (W1.subgroupOf M) (W2.subgroupOf M) W hz
  let zS : Smax :=
    ⟨gPair * (z : G) * gPair⁻¹, by
      have hzD : (((e ⟨z, hzW⟩ : d52.W) : Smax) : G) ∈ (Smax : Set G) :=
        ((e ⟨z, hzW⟩ : d52.W) : Smax).property
      simpa [he ⟨z, hzW⟩] using hzD⟩
  have hzlocal :
      zS ∈ Section3.cyclicTISet
        (W1S.subgroupOf Smax) (W2S.subgroupOf Smax) d52.W := by
    refine ⟨?_, ?_⟩
    · have hzD : ((e ⟨z, hzW⟩ : d52.W) : Smax) ∈ (d52.W : Set Smax) :=
        (e ⟨z, hzW⟩).property
      have hzS_eq : zS = ((e ⟨z, hzW⟩ : d52.W) : Smax) := by
        ext
        simp [zS, he ⟨z, hzW⟩]
      rw [hzS_eq]
      exact hzD
    · intro hmem
      rcases hmem with hleft | hright
      · have hW2 : (z : G) ∈ (W2 : Set G) := by
          have hconj : gPair * (z : G) * gPair⁻¹ ∈ (W2.conjBy gPair : Set G) := by
            simpa [zS, hW1S_eq, Subgroup.mem_subgroupOf] using hleft
          simpa [Subgroup.conjBy] using hconj
        exact (Section3.cyclicTISet_not_mem_right
          (W1.subgroupOf M) (W2.subgroupOf M) W hz)
          (by simpa [Subgroup.mem_subgroupOf] using hW2)
      · have hxdef :=
          theorem_10_7_typeP_partner_cyclicTI_selected_pair_xdefW_supported_source_data
            _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
            _h95 _hMs _hT_eq _hcasePair _hTypeIIPair _hTypePPair
            _hTypeIIToIVPair _hUcommPair _hUnormPair _hFPair gPair
            _hSmax_eq_Spair _hSF_eq hW1S_eq
        have hW1 : (z : G) ∈ (W1 : Set G) := by
          have hconj : gPair * (z : G) * gPair⁻¹ ∈ (W1.conjBy gPair : Set G) := by
            simpa [zS, hxdef.2, Subgroup.mem_subgroupOf] using hright
          simpa [Subgroup.conjBy] using hconj
        exact (Section3.cyclicTISet_not_mem_left
          (W1.subgroupOf M) (W2.subgroupOf M) W hz)
          (by simpa [Subgroup.mem_subgroupOf] using hW1)
  have hagree :=
    Section8.section8Hypothesis52FullData_sigma_agrees_on_cyclicTI_source_data
      d52 (Section6.theorem_6_8_transportClassFunction e (ω i j)) hclass zS hzlocal
  have harg :
      e.symm
          ⟨zS, Section3.cyclicTISet_subset
            (W1S.subgroupOf Smax) (W2S.subgroupOf Smax) d52.W hzlocal⟩ =
        ⟨z, hzW⟩ := by
    apply e.injective
    ext
    simp [zS, he ⟨z, hzW⟩]
  calc
    d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) (z : G) =
        d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) (zS : G) := by
          simpa [zS] using
            (hsigmaClass gPair (z : G)).symm
    _ = Section6.theorem_6_8_transportClassFunction e (ω i j)
        ⟨zS, Section3.cyclicTISet_subset
          (W1S.subgroupOf Smax) (W2S.subgroupOf Smax) d52.W hzlocal⟩ := hagree
    _ = (ω i j) ⟨z, hzW⟩ := by
      simp [Section6.theorem_6_8_transportClassFunction, harg]

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_eq_in_cycTIiso_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G}
    (_hcasePair :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair)
    (_hTypeIIPair : section16TypeII Spair SFpair)
    (_hTypePPair : Section8.typePDefinitionData Spair SFpair Upair W2 W1)
    (_hTypeIIToIVPair : Section8.typeIIToIVSourceCondition Spair Upair W2)
    (_hUcommPair : IsMulCommutative Upair)
    (_hUnormPair : ¬ Subgroup.normalizer (Upair : Set G) ≤ Spair)
    (_hFPair : Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair)
    (gPair : G)
    (_hSmax_eq_Spair : Smax = Spair.conjBy gPair)
    (_hSF_eq : SF = SFpair.conjBy gPair)
    (_hW1S_eq : W1S = W2.conjBy gPair)
    (e : W ≃* d52.W)
    (_he :
      ∀ x : W, (((e x : d52.W) : Smax) : G) =
        gPair * ((x : M) : G) * gPair⁻¹)
    (i : I)
    (j : J)
    (hSourceSigned : Section3.IsSignedIrreducibleCharacter (σ (ω i j)))
    (hSelectedSigned :
      Section3.IsSignedIrreducibleCharacter
        (d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j))))
    (hSourceRestrict :
      ∀ z : M,
        ∀ hz : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
          σ (ω i j) (z : G) =
            (ω i j) ⟨z, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hz⟩)
    (hSelectedRestrict :
      ∀ z : M,
        ∀ hz : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W,
          d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) (z : G) =
            (ω i j) ⟨z, Section3.cyclicTISet_subset
              (W1.subgroupOf M) (W2.subgroupOf M) W hz⟩) :
    σ (ω i j) =
      d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) := by
  classical
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h104
  rcases hNotation with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hDade10,
      _hW10, _hA010, _h46, hω10, _hIso10, _hVirt10, _hPrin10,
      _hσAgreeCyc, _h45, _h48, _hTauA0, hFull10⟩
  rcases hFull10 with ⟨_σM10, _xChar10, _H_A10, _H_A010, hSupported10,
    _hBaseRow10⟩
  rcases hSupported10 with
    ⟨_h46full, _hW2Kfull, h31Image, _hIsoFull, _hVirtFull, _hClassFull,
      _hPrinFull, _h22AFull, _hFullRest⟩
  let eImg := Section8.subgroupImageEquiv M W
  let EImg := Section1.classFunctionLinearEquivOfMulEquiv eImg
  have hωImg :
      Section3.notation_3_3_statement
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M W)
        I J i0 j0
        (fun i j => EImg (ω i j)) := by
    simpa [eImg, EImg] using
      (Section8.notation_3_3_statement_of_subgroupImageEquiv
        (M := M) (W1 := W1.subgroupOf M) (W2 := W2.subgroupOf M)
        (W := W) (I := I) (J := J) (i0 := i0) (j0 := j0)
        (omega := ω) hω10)
  rcases Section3.proposition_3_9_a_uniqueness
      (W1 := Section4Scratch.subgroupImage M (W1.subgroupOf M))
      (W2 := Section4Scratch.subgroupImage M (W2.subgroupOf M))
      (W := Section4Scratch.subgroupImage M W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := fun i j => EImg (ω i j)) h31Image hωImg with
    ⟨χpf, _horth, _hvirt, _hsigned, _h00, _hInd, huniq⟩
  have hsourceV :
      ∀ x : G,
        ∀ hx : x ∈
          Section3.cyclicTISet
            (Section4Scratch.subgroupImage M (W1.subgroupOf M))
            (Section4Scratch.subgroupImage M (W2.subgroupOf M))
            (Section4Scratch.subgroupImage M W),
          σ (ω i j) x =
            EImg (ω i j)
              ⟨x, Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                (Section4Scratch.subgroupImage M W) hx⟩ := by
    intro x hx
    have hxW :
        x ∈ (Section4Scratch.subgroupImage M W : Set G) :=
      Section3.cyclicTISet_subset
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M W) hx
    rcases hxW with ⟨z, hzW, rfl⟩
    have hzV : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W := by
      rw [Section3.cyclicTISet_mem_iff] at hx ⊢
      refine ⟨hzW, ?_, ?_⟩
      · intro hz1
        exact hx.2.1 ⟨z, hz1, rfl⟩
      · intro hz2
        exact hx.2.2 ⟨z, hz2, rfl⟩
    have hagree := hSourceRestrict z hzV
    have harg :
        (Section8.subgroupImageEquiv M W).symm
            ⟨((z : M) : G),
              Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                (Section4Scratch.subgroupImage M W) hx⟩ =
          ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hzV⟩ := by
      apply (Section8.subgroupImageEquiv M W).injective
      ext
      simp [Section8.subgroupImageEquiv_apply_coe]
    calc
      σ (ω i j) ((z : M) : G) =
          (ω i j) ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hzV⟩ := hagree
      _ =
          EImg (ω i j)
            ⟨((z : M) : G),
              Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                (Section4Scratch.subgroupImage M W) hx⟩ := by
        simp [EImg, eImg, Section1.classFunctionLinearEquivOfMulEquiv, harg]
  have hsourceEq :
      σ (ω i j) =
        Section3.sigmaOfPF35 (fun i j => EImg (ω i j)) χpf (EImg (ω i j)) :=
    have hωijImgIrr :
        Section1.IsIrreducibleCharacterOnGroup (EImg (ω i j)) := by
      exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        eImg (hω10.irreducible i j)
    huniq hωijImgIrr hSourceSigned hsourceV
  have hselectedV :
      ∀ x : G,
        ∀ hx : x ∈
          Section3.cyclicTISet
            (Section4Scratch.subgroupImage M (W1.subgroupOf M))
            (Section4Scratch.subgroupImage M (W2.subgroupOf M))
            (Section4Scratch.subgroupImage M W),
          d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) x =
            EImg (ω i j)
              ⟨x, Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                (Section4Scratch.subgroupImage M W) hx⟩ := by
    intro x hx
    have hxW :
        x ∈ (Section4Scratch.subgroupImage M W : Set G) :=
      Section3.cyclicTISet_subset
        (Section4Scratch.subgroupImage M (W1.subgroupOf M))
        (Section4Scratch.subgroupImage M (W2.subgroupOf M))
        (Section4Scratch.subgroupImage M W) hx
    rcases hxW with ⟨z, hzW, rfl⟩
    have hzV : z ∈ Section3.cyclicTISet (W1.subgroupOf M) (W2.subgroupOf M) W := by
      rw [Section3.cyclicTISet_mem_iff] at hx ⊢
      refine ⟨hzW, ?_, ?_⟩
      · intro hz1
        exact hx.2.1 ⟨z, hz1, rfl⟩
      · intro hz2
        exact hx.2.2 ⟨z, hz2, rfl⟩
    have hagree := hSelectedRestrict z hzV
    have harg :
        (Section8.subgroupImageEquiv M W).symm
            ⟨((z : M) : G),
              Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                (Section4Scratch.subgroupImage M W) hx⟩ =
          ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hzV⟩ := by
      apply (Section8.subgroupImageEquiv M W).injective
      ext
      simp [Section8.subgroupImageEquiv_apply_coe]
    calc
      d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) ((z : M) : G) =
          (ω i j) ⟨z, Section3.cyclicTISet_subset
            (W1.subgroupOf M) (W2.subgroupOf M) W hzV⟩ := hagree
      _ =
          EImg (ω i j)
            ⟨((z : M) : G),
              Section3.cyclicTISet_subset
                (Section4Scratch.subgroupImage M (W1.subgroupOf M))
                (Section4Scratch.subgroupImage M (W2.subgroupOf M))
                (Section4Scratch.subgroupImage M W) hx⟩ := by
        simp [EImg, eImg, Section1.classFunctionLinearEquivOfMulEquiv, harg]
  have hselectedEq :
      d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) =
        Section3.sigmaOfPF35 (fun i j => EImg (ω i j)) χpf (EImg (ω i j)) :=
    have hωijImgIrr :
        Section1.IsIrreducibleCharacterOnGroup (EImg (ω i j)) := by
      exact Section1.isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
        eImg (hω10.irreducible i j)
    huniq hωijImgIrr hSelectedSigned hselectedV
  rw [hsourceEq, hselectedEq]

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_compat_aligned_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {Wcase Spair Tpair SFpair TFpair Upair U1pair U0pair : Subgroup G}
    (_hcasePair :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tpair Spair TFpair SFpair)
    (_hTypeIIPair : section16TypeII Spair SFpair)
    (_hTypePPair : Section8.typePDefinitionData Spair SFpair Upair W2 W1)
    (_hTypeIIToIVPair : Section8.typeIIToIVSourceCondition Spair Upair W2)
    (_hUcommPair : IsMulCommutative Upair)
    (_hUnormPair : ¬ Subgroup.normalizer (Upair : Set G) ≤ Spair)
    (_hFPair : Section8.typeFData (ambientDerivedSubgroup Spair) SFpair Upair U1pair U0pair)
    (gPair : G)
    (_hSmax_eq_Spair : Smax = Spair.conjBy gPair)
    (_hSF_eq : SF = SFpair.conjBy gPair)
    (hW1S_eq : W1S = W2.conjBy gPair)
    (e : W ≃* d52.W)
    (_he :
      ∀ x : W, (((e x : d52.W) : Smax) : G) =
        gPair * ((x : M) : G) * gPair⁻¹) :
    ∀ i : I, ∀ j : J,
      σ (ω i j) =
        d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω i j)) := by
  intro i j
  exact
    theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_eq_in_cycTIiso_supported
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
      _h95 _hMs _hT_eq _hcasePair _hTypeIIPair _hTypePPair _hTypeIIToIVPair
      _hUcommPair _hUnormPair _hFPair gPair _hSmax_eq_Spair _hSF_eq hW1S_eq
      e _he i j
      (theorem_10_7_sigma_omega_signed_of_hypothesis_10_4_supported_data
        _h104 i j)
      (theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_transport_signed_supported
        _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
        _h95 _hMs _hT_eq _hcasePair _hTypeIIPair _hTypePPair
        _hTypeIIToIVPair _hUcommPair _hUnormPair _hFPair gPair
        _hSmax_eq_Spair _hSF_eq hW1S_eq e _he i j)
      (theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_source_restrict_supported_source_data
        _h104 i j)
      (theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_selected_restrict_supported
        _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
        _h95 _hMs _hT_eq _hcasePair _hTypeIIPair _hTypePPair
        _hTypeIIToIVPair _hUcommPair _hUnormPair _hFPair gPair
        _hSmax_eq_Spair _hSF_eq hW1S_eq e _he i j)


public theorem theorem_10_7_typeP_partner_cyclicTI_selected_row_package_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau) :
    ∃ e : W ≃* d52.W,
      (∀ i : I, ∀ j : J, ∃ i' : d52.I, ∃ j' : d52.J,
        Section6.theorem_6_8_transportClassFunction e (ω i j) =
          d52.omega i' j') ∧
        (∀ i : I, ∀ j : J,
          σ (ω i j) =
            d52.sigma
              (Section6.theorem_6_8_transportClassFunction e (ω i j))) ∧
          theorem_10_7_typeP_partner_cyclicTI_selected_column_to_transported_row_reindex_data
            ω d52 e := by
  classical
  rcases
      theorem_10_7_typeP_partner_cyclicTI_selected_row_alignment_supported_source_data
        _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
        _h95 _hMs _hT_eq with
    ⟨Wcase, Spair, Tpair, SFpair, TFpair, Upair, U1pair, U0pair, gPair,
      hcasePair, hTypeIIPair, hTypePPair, hTypeIIToIVPair, hUcommPair,
      hUnormPair, hFPair, hSmax_eq_Spair, hSF_eq, hW1S_eq⟩
  rcases
      theorem_10_7_typeP_partner_cyclicTI_selected_pair_xdefW_supported_source_data
        _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
        _h95 _hMs _hT_eq hcasePair hTypeIIPair hTypePPair hTypeIIToIVPair
        hUcommPair hUnormPair hFPair gPair hSmax_eq_Spair hSF_eq hW1S_eq with
    ⟨_hW1S_eq, hW2S_eq⟩
  rcases
      theorem_10_7_typeP_partner_cyclicTI_selected_pair_carrier_equiv_with_apply_supported
        _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
        _h95 _hMs _hT_eq hcasePair hTypeIIPair hTypePPair hTypeIIToIVPair
        hUcommPair hUnormPair hFPair gPair hSmax_eq_Spair hSF_eq hW1S_eq with
    ⟨e, he⟩
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  have hNotation := section10FourSixNotation_of_hypothesis_10_4_supported_data _h104
  rcases hNotation with
    ⟨_MF10, _Ms10, _Abook10, _A0book10, _A1book10, _hSource10,
      _hW10, _hA010, _h46, hω10, _hIso, _hVirt, _hPrin, _hσAgreeCyc, _h45, _h48,
      _hTauA0, _hFull10⟩
  rcases d52.fullHypothesis with
    ⟨_h46d, _hW2K, _h31d, _hIsoD, _hVirtD, _hClassD, _hPrinD, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hωd52, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0d,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases h10 with
    ⟨_hM10, _hType10, _hFamily10, hW1M, hW2M, _hW12M, _hDade10',
      _h46exists10, _hNotationExists10, _h5210⟩
  rcases _h95.hypothesis92.typePDefinitionData with
    ⟨_hSF95, _hW1cyc95, _hW1ne95, hW1Hall95, _hComp95, _hUle95,
      _hUnil95, _hW1norm95, _hDerComp95, _hSFnoncyc95, _hSecond95,
      _hFit95, _hFitLe95, hW2le95, _hW2cyc95, _hW2ne95,
      _hCentralizer95, _hNormalizer95⟩
  rcases _hSF.1 with ⟨hSFle, _hSFnormal, _hSFnil, _hSFhall⟩
  have hW1Sle : W1S ≤ Smax := hW1Hall95.1
  have hW2Sle : W2S ≤ Smax := (hW2le95.trans inf_le_left).trans hSFle
  have hOmegaSwap :
      Section3.OmegaSystem
        (W1S.subgroupOf Smax) (W2S.subgroupOf Smax) d52.W
        J I j0 i0
        (fun j i => Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    theorem_10_7_omegaSystem_transport_swap_of_conjugating_equiv
      hW1M hW2M hW1Sle hW2Sle hω10 gPair hW1S_eq hW2S_eq e he
  rcases Section8.omegaSystem_reindex_equiv hOmegaSwap hωd52 with
    ⟨eJ, eI, hentry⟩
  have hRowAlignment :
      theorem_10_7_typeP_partner_cyclicTI_selected_column_to_transported_row_reindex_data
        ω d52 e := by
    intro k
    refine ⟨eI.symm k, eJ.symm, ?_⟩
    intro i
    simpa using (hentry (eJ.symm i) (eI.symm k)).symm
  have hTable :
      ∀ i : I, ∀ j : J, ∃ i' : d52.I, ∃ j' : d52.J,
        Section6.theorem_6_8_transportClassFunction e (ω i j) =
          d52.omega i' j' := by
    intro i j
    exact ⟨eJ j, eI i, hentry j i⟩
  have hCompat : ∀ i : I, ∀ j : J,
      σ (ω i j) =
        d52.sigma
          (Section6.theorem_6_8_transportClassFunction e (ω i j)) :=
    theorem_10_7_typeP_partner_cyclicTI_selected_row_sigma_compat_aligned_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
      _h95 _hMs _hT_eq hcasePair hTypeIIPair hTypePPair hTypeIIToIVPair
      hUcommPair hUnormPair hFPair gPair hSmax_eq_Spair hSF_eq hW1S_eq e he
  exact ⟨e, hTable, hCompat, hRowAlignment⟩

public theorem theorem_10_7_typeP_partner_cyclicTI_selected_column_to_row_core_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime Ms : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (d52 : Section8.section8Hypothesis52FullData Smax Ms W1S W2S
      (Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_hMs : Section8.msChoice Smax SF Ms)
    (_hT_eq : T = d52.tau)
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {ν : Section1.ClassFunction Smax}
    {S4 : Finset (Section1.ClassFunction Smax)}
    (lam : Section1.ClassFunction Smax)
    (_hlam_irreducible : Section1.IsIrreducibleCharacterOnGroup lam)
    (hlamS4 : lam ∈ S4)
    (_hPreimage :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      ∃ k j : d52.J,
        k ≠ d52.j0 ∧
          Section4Scratch.piColumn d52.piChar k = ν ∧
            Section1.conjugateCharacter
                (Section4Scratch.piColumn d52.piChar k) =
              Section4Scratch.piColumn d52.piChar j)
    (_hImage :
      theorem_10_7_typeP_partner_selected_column_image_data d52 T4 ν)
    (hcohT4 : Section6.coherentFamily S4 T4)
    (hνS4 : ν ∈ S4) :
    ∃ r : I, ∃ ε : ℤ,
      (ε = 1 ∨ ε = -1) ∧
        T4 ν = (ε : ℂ) • (∑ j : J, σ (ω r j)) := by
  classical
  rcases theorem_10_7_typeP_partner_cyclicTI_selected_row_package_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
      _h95 _hMs _hT_eq with
    ⟨e, _hTable, hCompat, hRowAlignment⟩
  rcases Section8.section8_FTtypeP_coherent_TIred_source_data
      d52 e ω hRowAlignment lam _hlam_irreducible _hPreimage _hImage S4 hcohT4
      hlamS4 hνS4 with
    ⟨r, ε, hε, hT4ν⟩
  refine ⟨r, ε, hε, ?_⟩
  have hrow :
      (∑ j : J,
          d52.sigma (Section6.theorem_6_8_transportClassFunction e (ω r j))) =
        ∑ j : J, σ (ω r j) := by
    exact theorem_10_7_transport_row_sum_eq_source_row d52 e ω σ hCompat r
  rw [hT4ν, hrow]

public theorem theorem_10_7_typeP_partner_row_image_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hSelected :
      theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T)
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (_hT4Iso : Section5.isCFLinearIsometryOnSpan S4 T4)
    (_hT4Virt : Section5.mapsIntegerSpanToVirtualCharacters S4 T4)
    (_hT4Agree : Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet T T4)
    (_h52S4 : Section5.hypothesis_5_2_statement S4 T)
    (χ ν : Section1.ClassFunction Smax)
    (hχS4 : χ ∈ S4)
    (hχbarS4 : Section1.conjugateCharacter χ ∈ S4)
    (_hS4sub : S4 ⊆ S9)
    (_hνS4 : ν ∈ S4)
    (_hν_mem : ν ∈ S9)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν)
    (_hν_degree : Section1.degree ν = Section1.degree χ)
    (_hχ_family : χ ∈ S9)
    (_hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ r : I, ∃ ε : ℤ,
      (ε = 1 ∨ ε = -1) ∧
        T4 ν = (ε : ℂ) • (∑ j : J, σ (ω r j)) := by
  classical
  rcases hSelected with ⟨Ms, hMs, d52, hT_eq⟩
  have hImageClass :
      theorem_10_7_typeP_partner_selected_column_image_classification_data
        d52 S4 T4 ν :=
    theorem_10_7_typeP_partner_selected_column_image_classification_source_data
      T S9 d52 _h95 _h52 hMs hT_eq
      _hT4Iso _hT4Virt _hT4Agree _h52S4 χ ν hχS4 hχbarS4 _hS4sub _hνS4
      _hν_mem _hν_reducible _hν_degree _hχ_family _hχ_irreducible
  have hImage :
      theorem_10_7_typeP_partner_selected_column_image_data d52 T4 ν :=
    theorem_10_7_typeP_partner_selected_column_image_of_classification hImageClass
  have hPreimage :
      letI : Fintype d52.I := d52.instFintypeI
      letI : Fintype d52.J := d52.instFintypeJ
      ∃ k j : d52.J,
        k ≠ d52.j0 ∧
          Section4Scratch.piColumn d52.piChar k = ν ∧
            Section1.conjugateCharacter
                (Section4Scratch.piColumn d52.piChar k) =
              Section4Scratch.piColumn d52.piChar j := by
    rcases hImageClass with
      ⟨k, j, _δSignZ, _hδSignZ, _hδSignZ_sign, hk0, hνeq, hconj, _hAlt⟩
    exact ⟨k, j, hk0, hνeq, hconj⟩
  have hcohT4 : Section6.coherentFamily S4 T4 := by
    rcases _h52S4 with
      ⟨hsetup4, _R4, h52a4, _h52b4, _h52c4, _h52d4, _h52e4⟩
    have hsrc : Section5.sourceVirtualCharacters S4 := by
      intro ψ hψ
      exact Section5.isVirtualCharacter_of_isCharacter (hsetup4.2 ⟨ψ, hψ⟩)
    have hχne :
        χ ≠ Section1.conjugateCharacter χ :=
      (h52a4 ⟨χ, hχS4⟩).2
    have hχchar : Section1.IsCharacter χ :=
      hsetup4.2 ⟨χ, hχS4⟩
    have hnonempty :
        Section5.integerSpanOnNonempty S4 Section5.puncturedSet :=
      Section5.integerSpanOnNonempty_of_conjugate_pair
        hχS4 hχbarS4 hχne hχchar
    refine ⟨hsrc, hnonempty, T4, _hT4Iso, _hT4Virt, ?_⟩
    intro ψ _hψ
    rfl
  exact
    theorem_10_7_typeP_partner_cyclicTI_selected_column_to_row_core_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
      _h95 hMs hT_eq (T4 := T4) (ν := ν) χ _hχ_irreducible hχS4 hPreimage
      hImage (S4 := S4) hcohT4 _hνS4

public theorem theorem_10_7_typeP_partner_cyclicTI_R_package_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hSelected :
      theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T)
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (_hT4Iso : Section5.isCFLinearIsometryOnSpan S4 T4)
    (_hT4Virt : Section5.mapsIntegerSpanToVirtualCharacters S4 T4)
    (_hT4Agree : Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet T T4)
    (χ : Section1.ClassFunction Smax)
    (hχS4 : χ ∈ S4)
    (hχbarS4 : Section1.conjugateCharacter χ ∈ S4)
    (hχ_family : χ ∈ S9)
    (hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ Rχ : Finset (Section1.ClassFunction G),
      Section5.isSubsetSumOf Rχ (T4 χ) ∧
        Section5.orthogonalFinsets Rχ
          (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) := by
  classical
  let : Fintype Smax := Fintype.ofFinite Smax
  rcases hSelected with ⟨Ms, hMs, d52, hT_eq⟩
  let : Fintype d52.I := d52.instFintypeI
  let : Fintype d52.J := d52.instFintypeJ
  let : DecidableEq d52.I := d52.instDecidableEqI
  let : DecidableEq d52.J := d52.instDecidableEqJ
  rcases theorem_10_7_typeP_partner_cyclicTI_selected_row_package_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime Ms T S9 d52
      _h95 hMs hT_eq with
    ⟨e, hTable, hCompat, _hRowAlignment⟩
  have hAlign :
      theorem_10_7_typeP_partner_cyclicTI_table_alignment_data
        (ω := ω) (σ := σ) d52 := by
    intro i j
    rcases hTable i j with ⟨i', j', hentry⟩
    refine ⟨i', j', ?_⟩
    simpa [hentry] using hCompat i j
  have hS9ne : S9.Nonempty := _h52.1.1
  have hS8 : Section8.section8InducedNonkernelFamily Smax Ms S9 :=
    Section9.section8InducedNonkernelFamily_of_kernelInducedFamily_msChoice_nonempty_sec9
      Smax SF U W1S W2S Ms H0 S9 _h95.hypothesis92 hMs
      _h95.kernelInduced hS9ne
  rcases Section8.theorem_8_15_hypothesis_5_2_extra_of_fullData
      (G := G) (M := Smax) (Ms := Ms) (W1 := W1S) (W2 := W2S)
      (A := Section8.section8CentralizerUnion (ambientDerivedSubgroup Smax) Ms)
      (S := S9) (by infer_instance : IsMinCE G) d52 hS8 with
    ⟨R, _hsetup, h52a, _h52b, h52c, h52d0, _h52e, hExtra0⟩
  have h52d :
      Section5.hypothesis_5_2_d_statement S9 T R := by
    intro X
    rcases h52d0 X with ⟨hR, hsum⟩
    refine ⟨hR, ?_⟩
    rw [theorem_10_7_typeP_partner_cyclicTI_R_pairDiff_transform_source_data
      T S9 d52 _h95 _h52 hT_eq X]
    exact hsum
  have hsub :
      (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) ⊆
        (Finset.univ.image fun p : d52.I × d52.J =>
          d52.sigma (d52.omega p.1 p.2)) := by
    intro φ hφ
    rcases Finset.mem_image.mp hφ with ⟨p, _hp, rfl⟩
    rcases hAlign p.1 p.2 with ⟨i', j', hentry⟩
    exact Finset.mem_image.mpr ⟨(i', j'), Finset.mem_univ _, hentry.symm⟩
  have hExtra :
      Section5.theorem_5_3_b_extra_statement S9 R
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
    theorem_10_7_theorem_5_3_b_extra_transport_of_table_subset hExtra0 hsub
  let X : S9 := ⟨χ, hχ_family⟩
  have horth :
      Section5.orthogonalFinsets (R X)
        (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
    hExtra X hχ_irreducible
  have hpairSubset :
      ({(X : Section1.ClassFunction Smax),
        Section1.conjugateCharacter (X : Section1.ClassFunction Smax)} :
        Finset (Section1.ClassFunction Smax)) ⊆ S4 := by
    intro ψ hψ
    simp [X] at hψ
    rcases hψ with rfl | rfl
    · exact hχS4
    · exact hχbarS4
  have hpairIso :
      Section5.isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction Smax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)} :
          Finset (Section1.ClassFunction Smax)) T4 :=
    Section5.isCFLinearIsometryOnSpan_mono hpairSubset _hT4Iso
  have hpairVirt :
      Section5.mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction Smax),
          Section1.conjugateCharacter (X : Section1.ClassFunction Smax)} :
          Finset (Section1.ClassFunction Smax)) T4 :=
    Section5.mapsIntegerSpanToVirtualCharacters_mono hpairSubset _hT4Virt
  have hχchar : Section1.IsCharacter χ :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hχ_irreducible
  have hdiffOn :
      Section5.integerSpanOn S4 Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) := by
    refine ⟨Section5.integerSpan_sub
        (Section5.integerSpan_of_mem S4 hχS4)
        (Section5.integerSpan_of_mem S4 hχbarS4), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (χ - Section1.conjugateCharacter χ)).2
    rw [Section1.degree]
    have hdeg_apply : χ 1 = Section1.conjugateCharacter χ 1 := by
      simpa [Section1.degree] using
        (Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar).symm
    simp [Pi.sub_apply, hdeg_apply]
  have hagree :
      T4 ((X : Section1.ClassFunction Smax) -
            Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) =
        T ((X : Section1.ClassFunction Smax) -
            Section1.conjugateCharacter (X : Section1.ClassFunction Smax)) := by
    simpa [X] using _hT4Agree (χ - Section1.conjugateCharacter χ) hdiffOn
  have hsubset :
      Section5.isSubsetSumOf (R X) (T4 χ) := by
    have hsubsetX :
        Section5.isSubsetSumOf (R X) (T4 (X : Section1.ClassFunction Smax)) :=
      Section5.theorem_5_5_core S9 T R h52a h52c h52d X T4
        hpairIso hpairVirt hagree
    simpa [X] using hsubsetX
  exact ⟨R X, hsubset, by simpa [X] using horth⟩

public theorem theorem_10_7_typeP_partner_cyclicTI_orthogonality_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hSelected :
      theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T)
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (_hT4Iso : Section5.isCFLinearIsometryOnSpan S4 T4)
    (_hT4Virt : Section5.mapsIntegerSpanToVirtualCharacters S4 T4)
    (_hT4Agree : Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet T T4)
    (χ ν : Section1.ClassFunction Smax)
    (hχS4 : χ ∈ S4)
    (hχbarS4 : Section1.conjugateCharacter χ ∈ S4)
    (_hν_mem : ν ∈ S9)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν)
    (_hν_degree : Section1.degree ν = Section1.degree χ)
    (_hχ_family : χ ∈ S9)
    (_hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∀ i j, Section1.scalarProduct G (σ (ω i j)) (T4 χ) = 0 := by
  classical
  rcases theorem_10_7_typeP_partner_cyclicTI_R_package_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52
      hSelected
      _hT4Iso _hT4Virt _hT4Agree χ hχS4 hχbarS4 _hχ_family _hχ_irreducible with
    ⟨Rχ, hsubset, horth⟩
  intro i j
  let Ω : Finset (Section1.ClassFunction G) :=
    Finset.univ.image fun p : I × J => σ (ω p.1 p.2)
  have hmem : σ (ω i j) ∈ Ω := by
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
  have hzero :
      Section1.scalarProduct G (T4 χ) (σ (ω i j)) = 0 :=
    scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets
      hsubset (by simpa [Ω] using horth) hmem
  simpa [Section1.scalarProduct_star_swap] using congrArg star hzero

public theorem theorem_10_7_typeP_partner_tauOne_orthogonality_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (_hT4Iso : Section5.isCFLinearIsometryOnSpan S4 T4)
    (_hT4Virt : Section5.mapsIntegerSpanToVirtualCharacters S4 T4)
    (_hT4Agree : Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet T T4)
    (χ ν : Section1.ClassFunction Smax)
    (hχS4 : χ ∈ S4)
    (hχbarS4 : Section1.conjugateCharacter χ ∈ S4)
    (_hν_mem : ν ∈ S9)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν)
    (_hν_degree : Section1.degree ν = Section1.degree χ)
    (_hχ_family : χ ∈ S9)
    (_hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G (τ₁ ξ) (T4 χ) = 0 := by
  classical
  have h104a := hypothesis_10_4_a_of_hypothesis_10_4_supported_data _h104
  rcases h104a with ⟨h10, _hNotation, hξS, hξIrr, _hξDegree, _hUniform⟩
  rcases hypothesis_5_2_of_hypothesis_10_1_supported_data h10 with
    ⟨hsetupS, _RS, h52aS, h52bS, h52cS, _h52dS, _h52eS⟩
  rcases _h52 with
    ⟨hsetup9, _R9, h52a9, h52b9, h52c9, _h52d9, _h52e9⟩
  let ξS : S := ⟨ξ, hξS⟩
  have hξbarS : Section1.conjugateCharacter ξ ∈ S := (h52aS ξS).1
  have hξ_ne_bar :
      ξ ≠ Section1.conjugateCharacter ξ := (h52aS ξS).2
  have hξbarIrr :
      Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter ξ) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hξIrr
  let χ9 : S9 := ⟨χ, _hχ_family⟩
  have hχbarS9 : Section1.conjugateCharacter χ ∈ S9 := (h52a9 χ9).1
  have hχ_ne_bar :
      χ ≠ Section1.conjugateCharacter χ := (h52a9 χ9).2
  have hχbarIrr :
      Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter χ) :=
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter _hχ_irreducible
  have hExt := extensionInterfaces_of_hypothesis_10_4_supported_data _h104
  have hτξSigned : Section3.IsSignedIrreducibleCharacter (τ₁ ξ) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59
      (tauOne_xi_isVirtualCharacter_of_hypothesis_10_4_supported_data _h104)
      (tauOne_xi_scalarProduct_self_of_hypothesis_10_4_supported_data _h104)
  have hτξbarVirt :
      IsVirtualCharacter (τ₁ (Section1.conjugateCharacter ξ)) :=
    hExt.2.1 (Section1.conjugateCharacter ξ) (Section5.integerSpan_of_mem S hξbarS)
  have hτξbarSelf :
      Section1.scalarProduct G (τ₁ (Section1.conjugateCharacter ξ))
        (τ₁ (Section1.conjugateCharacter ξ)) = 1 := by
    calc
      Section1.scalarProduct G (τ₁ (Section1.conjugateCharacter ξ))
          (τ₁ (Section1.conjugateCharacter ξ)) =
          Section1.scalarProduct M (Section1.conjugateCharacter ξ)
            (Section1.conjugateCharacter ξ) :=
        hExt.1 (Section1.conjugateCharacter ξ) (Section1.conjugateCharacter ξ)
          (Section5.integerSpan_of_mem S hξbarS) (Section5.integerSpan_of_mem S hξbarS)
      _ = 1 := scalarProduct_irreducible_self hξbarIrr
  have hτξbarSigned :
      Section3.IsSignedIrreducibleCharacter (τ₁ (Section1.conjugateCharacter ξ)) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hτξbarVirt hτξbarSelf
  have hTχVirt : IsVirtualCharacter (T4 χ) :=
    _hT4Virt χ (Section5.integerSpan_of_mem S4 hχS4)
  have hTχSelf : Section1.scalarProduct G (T4 χ) (T4 χ) = 1 := by
    calc
      Section1.scalarProduct G (T4 χ) (T4 χ) =
          Section1.scalarProduct Smax χ χ :=
        _hT4Iso χ χ (Section5.integerSpan_of_mem S4 hχS4)
          (Section5.integerSpan_of_mem S4 hχS4)
      _ = 1 := scalarProduct_irreducible_self _hχ_irreducible
  have hTχSigned : Section3.IsSignedIrreducibleCharacter (T4 χ) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hTχVirt hTχSelf
  have hTχbarVirt :
      IsVirtualCharacter (T4 (Section1.conjugateCharacter χ)) :=
    _hT4Virt (Section1.conjugateCharacter χ)
      (Section5.integerSpan_of_mem S4 hχbarS4)
  have hTχbarSelf :
      Section1.scalarProduct G (T4 (Section1.conjugateCharacter χ))
        (T4 (Section1.conjugateCharacter χ)) = 1 := by
    calc
      Section1.scalarProduct G (T4 (Section1.conjugateCharacter χ))
          (T4 (Section1.conjugateCharacter χ)) =
          Section1.scalarProduct Smax (Section1.conjugateCharacter χ)
            (Section1.conjugateCharacter χ) :=
        _hT4Iso (Section1.conjugateCharacter χ) (Section1.conjugateCharacter χ)
          (Section5.integerSpan_of_mem S4 hχbarS4)
          (Section5.integerSpan_of_mem S4 hχbarS4)
      _ = 1 := scalarProduct_irreducible_self hχbarIrr
  have hTχbarSigned :
      Section3.IsSignedIrreducibleCharacter (T4 (Section1.conjugateCharacter χ)) :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 hTχbarVirt hTχbarSelf
  have hτPair :
      Section1.scalarProduct G (τ₁ ξ) (τ₁ (Section1.conjugateCharacter ξ)) = 0 := by
    calc
      Section1.scalarProduct G (τ₁ ξ) (τ₁ (Section1.conjugateCharacter ξ)) =
          Section1.scalarProduct M ξ (Section1.conjugateCharacter ξ) :=
        hExt.1 ξ (Section1.conjugateCharacter ξ)
          (Section5.integerSpan_of_mem S hξS) (Section5.integerSpan_of_mem S hξbarS)
      _ = 0 := h52cS hξS hξbarS hξ_ne_bar
  have hTPair :
      Section1.scalarProduct G (T4 χ) (T4 (Section1.conjugateCharacter χ)) = 0 := by
    calc
      Section1.scalarProduct G (T4 χ) (T4 (Section1.conjugateCharacter χ)) =
          Section1.scalarProduct Smax χ (Section1.conjugateCharacter χ) :=
        _hT4Iso χ (Section1.conjugateCharacter χ)
          (Section5.integerSpan_of_mem S4 hχS4)
          (Section5.integerSpan_of_mem S4 hχbarS4)
      _ = 0 := h52c9 _hχ_family hχbarS9 hχ_ne_bar
  have hξDiffOn :
      Section5.integerSpanOn S Section5.puncturedSet
        (ξ - Section1.conjugateCharacter ξ) :=
    theorem_10_7_pairDiff_integerSpanOn_punctured hsetupS h52aS ξS
  have hχDiffOn9 :
      Section5.integerSpanOn S9 Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) :=
    theorem_10_7_pairDiff_integerSpanOn_punctured hsetup9 h52a9 χ9
  have hχchar : Section1.IsCharacter χ := hsetup9.2 χ9
  have hχ_degree :
      Section1.degree χ = Section1.degree (Section1.conjugateCharacter χ) :=
    (Section5.degree_conjugateCharacter_eq_of_isCharacter hχchar).symm
  have hχDiffOn4 :
      Section5.integerSpanOn S4 Section5.puncturedSet
        (χ - Section1.conjugateCharacter χ) := by
    refine ⟨Section5.integerSpan_sub
        (Section5.integerSpan_of_mem S4 hχS4)
        (Section5.integerSpan_of_mem S4 hχbarS4), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (χ - Section1.conjugateCharacter χ)).2
    exact sub_eq_zero.mpr hχ_degree
  have hDiffZeroSource :
      Section1.scalarProduct G (τ (ξ - Section1.conjugateCharacter ξ))
        (T (χ - Section1.conjugateCharacter χ)) = 0 :=
    theorem_10_7_support_orthogonality_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95
      (ξ - Section1.conjugateCharacter ξ) hξDiffOn
      (χ - Section1.conjugateCharacter χ) hχDiffOn9
  have hτDiffEq :
      τ₁ (ξ - Section1.conjugateCharacter ξ) =
        τ (ξ - Section1.conjugateCharacter ξ) :=
    xi_sub_conjugate_tauOne_eq_tau_of_hypothesis_10_4_supported_data _h104
  have hT4DiffEq :
      T4 (χ - Section1.conjugateCharacter χ) =
        T (χ - Section1.conjugateCharacter χ) :=
    _hT4Agree (χ - Section1.conjugateCharacter χ) hχDiffOn4
  have hDiffZero :
      Section1.scalarProduct G (τ₁ (ξ - Section1.conjugateCharacter ξ))
        (T4 (χ - Section1.conjugateCharacter χ)) = 0 := by
    rw [hτDiffEq, hT4DiffEq]
    exact hDiffZeroSource
  have hcross :
      Section1.scalarProduct G
        (τ₁ ξ - τ₁ (Section1.conjugateCharacter ξ))
        (((1 : ℂ) • T4 χ) -
          ((1 : ℂ) • T4 (Section1.conjugateCharacter χ))) = 0 := by
    simpa [map_sub] using hDiffZero
  have hτDiffSupp :
      Section1.supportedOn (τ (ξ - Section1.conjugateCharacter ξ))
        Section5.puncturedSet :=
    (h52bS.2 (ξ - Section1.conjugateCharacter ξ) hξDiffOn).2
  have hτDiffDegreeSource :
      Section1.degree (τ (ξ - Section1.conjugateCharacter ξ)) = 0 :=
    (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (τ (ξ - Section1.conjugateCharacter ξ))).1 hτDiffSupp
  have hτDiffDegree :
      Section1.degree (τ₁ ξ - τ₁ (Section1.conjugateCharacter ξ)) = 0 := by
    calc
      Section1.degree (τ₁ ξ - τ₁ (Section1.conjugateCharacter ξ)) =
          Section1.degree (τ₁ (ξ - Section1.conjugateCharacter ξ)) := by
        simp
      _ = Section1.degree (τ (ξ - Section1.conjugateCharacter ξ)) := by
        rw [hτDiffEq]
      _ = 0 := hτDiffDegreeSource
  have hTDiffSupp :
      Section1.supportedOn (T (χ - Section1.conjugateCharacter χ))
        Section5.puncturedSet :=
    (h52b9.2 (χ - Section1.conjugateCharacter χ) hχDiffOn9).2
  have hTDiffDegreeSource :
      Section1.degree (T (χ - Section1.conjugateCharacter χ)) = 0 :=
    (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (T (χ - Section1.conjugateCharacter χ))).1 hTDiffSupp
  have hTDiffDegree :
      Section1.degree
        (((1 : ℂ) • T4 χ) -
          ((1 : ℂ) • T4 (Section1.conjugateCharacter χ))) = 0 := by
    calc
      Section1.degree
          (((1 : ℂ) • T4 χ) -
            ((1 : ℂ) • T4 (Section1.conjugateCharacter χ))) =
          Section1.degree (T4 (χ - Section1.conjugateCharacter χ)) := by
        simp
      _ = Section1.degree (T (χ - Section1.conjugateCharacter χ)) := by
        rw [hT4DiffEq]
      _ = 0 := hTDiffDegreeSource
  have hpair :=
    Section4.proposition_4_1
      (α := τ₁ ξ)
      (β := τ₁ (Section1.conjugateCharacter ξ))
      (γ := T4 χ)
      (δ := T4 (Section1.conjugateCharacter χ))
      (u := 1)
      (v := 1)
      hτξSigned hτξbarSigned hTχSigned hTχbarSigned
      (by norm_num) (by norm_num) hτPair hTPair hcross hτDiffDegree hTDiffDegree
  exact hpair.2.1

public theorem theorem_10_7_typeP_partner_image_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hSelected :
      theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T)
    {S4 : Finset (Section1.ClassFunction Smax)}
    {T4 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    (_hT4Iso : Section5.isCFLinearIsometryOnSpan S4 T4)
    (_hT4Virt : Section5.mapsIntegerSpanToVirtualCharacters S4 T4)
    (_hT4Agree : Section5.agreesOnIntegerSpanOn S4 Section5.puncturedSet T T4)
    (_h52S4 : Section5.hypothesis_5_2_statement S4 T)
    (χ ν : Section1.ClassFunction Smax)
    (hχS4 : χ ∈ S4)
    (hχbarS4 : Section1.conjugateCharacter χ ∈ S4)
    (_hS4sub : S4 ⊆ S9)
    (_hνS4 : ν ∈ S4)
    (_hν_mem : ν ∈ S9)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν)
    (_hν_degree : Section1.degree ν = Section1.degree χ)
    (_hχ_family : χ ∈ S9)
    (_hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ r : I, ∃ ε : ℤ,
      (ε = 1 ∨ ε = -1) ∧
        T4 ν = (ε : ℂ) • (∑ j : J, σ (ω r j)) ∧
          (∀ i j, Section1.scalarProduct G (σ (ω i j)) (T4 χ) = 0) ∧
            Section1.scalarProduct G (τ₁ ξ) (T4 χ) = 0 := by
  rcases theorem_10_7_typeP_partner_row_image_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52
      hSelected
      _hT4Iso _hT4Virt _hT4Agree _h52S4 χ ν hχS4 hχbarS4 _hS4sub _hνS4
      _hν_mem _hν_reducible _hν_degree _hχ_family _hχ_irreducible with
    ⟨r, ε, hε, hT4ν⟩
  have hσχ :
      ∀ i j, Section1.scalarProduct G (σ (ω i j)) (T4 χ) = 0 :=
    theorem_10_7_typeP_partner_cyclicTI_orthogonality_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52
      hSelected
      _hT4Iso _hT4Virt _hT4Agree χ ν hχS4 hχbarS4 _hν_mem _hν_reducible _hν_degree
      _hχ_family _hχ_irreducible
  have hτχ : Section1.scalarProduct G (τ₁ ξ) (T4 χ) = 0 :=
    theorem_10_7_typeP_partner_tauOne_orthogonality_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52
      _hT4Iso _hT4Virt _hT4Agree χ ν hχS4 hχbarS4 _hν_mem _hν_reducible _hν_degree
      _hχ_family _hχ_irreducible
  exact ⟨r, ε, hε, hT4ν, hσχ, hτχ⟩

public theorem theorem_10_7_forbidden_character_pair_contradiction_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hSelected :
      theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T)
    (u : ℕ)
    (_hBarU : Section9.quotientBarUCardinality U C u)
    (χ ν : Section1.ClassFunction Smax)
    (_hχ_mem :
      χ ∈
        Section9.kernelInducedSubfamily_sec9 Smax
          (ambientDerivedSubgroup Smax) SF (H0 ⊔ Cprime) S9)
    (_hχ_forbidden :
      Section9.degreeQuIrreducibleFromLinearHC
        Smax SF C (Nat.card W1S) u χ)
    (_hν_mem : ν ∈ S9)
    (_hν_reducible : ¬ Section1.IsIrreducibleCharacterOnGroup ν)
    (_hν_degree : Section1.degree ν = Section1.degree χ)
    (_hχ_family : χ ∈ S9)
    (_hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ)
    (_hβ : Section5.integerSpanOn S9 Section5.puncturedSet (ν - χ)) :
    False := by
  let S4 : Finset (Section1.ClassFunction Smax) :=
    {χ, Section1.conjugateCharacter χ, ν, Section1.conjugateCharacter ν}
  have h52S4 : Section5.hypothesis_5_2_statement S4 T :=
    theorem_10_7_four_character_hypothesis_5_2 _h52 _hχ_family _hν_mem
  have hcohS4 : Section6.coherentFamily S4 T :=
    theorem_10_7_four_character_coherent _h52 _hχ_family _hν_mem _hν_degree
  have hνS4 : ν ∈ S4 := by
    simp [S4]
  have hχS4 : χ ∈ S4 := by
    simp [S4]
  have hχbarS4 : Section1.conjugateCharacter χ ∈ S4 := by
    simp [S4]
  have hS4sub : S4 ⊆ S9 := by
    simpa [S4] using theorem_10_7_four_character_subset _h52 _hχ_family _hν_mem
  have hβS4 : Section5.integerSpanOn S4 Section5.puncturedSet (ν - χ) :=
    theorem_10_7_integerSpanOn_sub_of_equal_degree_mem hνS4 hχS4 _hν_degree
  rcases hcohS4 with ⟨_hsrcS4, _hnonemptyS4, T4, hT4Iso, hT4Virt, hT4Agree⟩
  have hT4β : T4 (ν - χ) = T (ν - χ) :=
    hT4Agree (ν - χ) hβS4
  rcases exists_ne_base_column_of_hypothesis_10_4_supported_data_local _h104 with
    ⟨s, hs⟩
  let α : Section1.ClassFunction M := muColumn μ s - (d : ℂ) • ξ
  have hαS : Section5.integerSpanOn S Section5.puncturedSet α := by
    simpa [α] using
      muColumn_sub_smul_xi_integerSpanOn_of_hypothesis_10_4_supported_data_local
        _h104 hs
  have hOrth :
      ∀ α : Section1.ClassFunction M,
        Section5.integerSpanOn S Section5.puncturedSet α →
          ∀ β : Section1.ClassFunction Smax,
            Section5.integerSpanOn S9 Section5.puncturedSet β →
              Section1.scalarProduct G (τ α) (T β) = 0 :=
    theorem_10_7_support_orthogonality_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95
  have hOrthT : Section1.scalarProduct G (τ α) (T (ν - χ)) = 0 :=
    hOrth α hαS (ν - χ) _hβ
  have hOrthT4 : Section1.scalarProduct G (τ α) (T4 (ν - χ)) = 0 := by
    rw [hT4β]
    exact hOrthT
  have hτAlpha :
      τ α = (δ : ℂ) • (∑ i : I, σ (ω i s)) - (d : ℂ) • τ₁ ξ := by
    simpa [α] using
      theorem_10_7_tau_muColumn_sub_smul_xi_eq_column_sum_supported _h104 hs
  have hOrthExpanded :
      Section1.scalarProduct G
        ((δ : ℂ) • (∑ i : I, σ (ω i s)) - (d : ℂ) • τ₁ ξ)
        (T4 (ν - χ)) = 0 := by
    simpa [hτAlpha] using hOrthT4
  rcases theorem_10_7_typeP_partner_image_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52
      hSelected
      hT4Iso hT4Virt hT4Agree h52S4 χ ν hχS4 hχbarS4 hS4sub hνS4
      _hν_mem _hν_reducible _hν_degree _hχ_family _hχ_irreducible with
    ⟨r, ε, hε, hT4ν, hσχ, hτχ⟩
  exact theorem_10_7_scalar_contradiction_from_partner_image_supported
    _h104 hs hε hT4ν hσχ hτχ hOrthExpanded

public theorem theorem_10_7_no_forbidden_character_pair_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    (U W1S W2S H0 C Cprime : Subgroup G)
    (T : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (S9 : Finset (Section1.ClassFunction Smax))
    (_h95 : Section9.Hypothesis_9_5 Smax SF U W1S W2S H0 C Cprime T S9)
    (_h52 : Section5.hypothesis_5_2_statement S9 T)
    (hSelected :
      theorem_10_7_selectedSection8FullDataForT Smax SF W1S W2S T) :
    ∀ u : ℕ, Section9.quotientBarUCardinality U C u →
      ¬ ∃ χ : Section1.ClassFunction Smax,
        χ ∈
            Section9.kernelInducedSubfamily_sec9 Smax
              (ambientDerivedSubgroup Smax) SF (H0 ⊔ Cprime) S9 ∧
          Section9.degreeQuIrreducibleFromLinearHC
            Smax SF C (Nat.card W1S) u χ := by
  intro u hBarU hbad
  rcases hbad with ⟨χ, hχ_mem, hχ_forbidden⟩
  have hχ_family : χ ∈ S9 :=
    theorem_10_7_kernelInducedSubfamily_mem_family hχ_mem
  have hχ_irreducible : Section1.IsIrreducibleCharacterOnGroup χ :=
    hχ_forbidden.1
  rcases theorem_10_7_forbidden_character_reducible_partner_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52
      u hBarU χ hχ_mem hχ_forbidden with
    ⟨ν, hν_mem, hν_reducible, hν_degree⟩
  have hβ : Section5.integerSpanOn S9 Section5.puncturedSet (ν - χ) :=
    theorem_10_7_integerSpanOn_sub_of_equal_degree_mem hν_mem hχ_family hν_degree
  exact theorem_10_7_forbidden_character_pair_contradiction_supported_source_data
    _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 _h95 _h52 hSelected
    u hBarU χ ν hχ_mem hχ_forbidden hν_mem hν_reducible hν_degree
    hχ_family hχ_irreducible hβ

public theorem theorem_10_7_frobenius_join_of_typeII_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    {U W1S W2S U1 U0 : Subgroup G}
    (_hPData : Section8.typePData Smax SF U W1S W2S)
    (_hTypeP : Section8.typePDefinitionData Smax SF U W1S W2S)
    (_hTypeIIToIV : Section8.typeIIToIVSourceCondition Smax U W1S)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ Smax)
    (_hF : Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0) :
    section12FrobeniusJoinWithKernel SF U := by
  rcases theorem_10_7_hypothesis_9_5_pair_core_supported_source_data
      _h104 _hSmax _hSF _hTypeII _hPData _hTypeP _hTypeIIToIV _hUcomm
      _hUnorm _hF with
    ⟨H0, C, Cprime, T, S9, h95, h52, hSelected⟩
  have hno :
      ∀ u : ℕ, Section9.quotientBarUCardinality U C u →
        ¬ ∃ χ : Section1.ClassFunction Smax,
          χ ∈
              Section9.kernelInducedSubfamily_sec9 Smax
                (ambientDerivedSubgroup Smax) SF (H0 ⊔ Cprime) S9 ∧
            Section9.degreeQuIrreducibleFromLinearHC
              Smax SF C (Nat.card W1S) u χ :=
    theorem_10_7_no_forbidden_character_pair_supported_source_data
      _h104 _hSmax _hSF _hTypeII U W1S W2S H0 C Cprime T S9 h95 h52
      hSelected
  exact
    theorem_10_7_frobenius_bridge_of_hypothesis_9_5_canonical
      Smax SF U W1S W2S H0 C Cprime T S9 h95 hno _hTypeII

public theorem theorem_10_7_frobenius_bridge_of_typeII_supported_source_data
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    {M MF W1 W2 Smax SF : Subgroup G}
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ
      i0 j0 μ δSign ω σ d n δ)
    (_hSmax : Smax ∈ section9MaximalSubgroups G)
    (_hSF : section16MFSubgroup Smax SF)
    (_hTypeII : section16TypeII Smax SF)
    {U W1S W2S U1 U0 : Subgroup G}
    (_hPData : Section8.typePData Smax SF U W1S W2S)
    (_hTypeP : Section8.typePDefinitionData Smax SF U W1S W2S)
    (_hTypeIIToIV : Section8.typeIIToIVSourceCondition Smax U W1S)
    (_hUcomm : IsMulCommutative U)
    (_hUnorm : ¬ Subgroup.normalizer (U : Set G) ≤ Smax)
    (_hF : Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0) :
    Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U ∧
      section12FrobeniusJoinWithKernel SF U := by
  have hTypePFull : Section8.typePDefinitionData Smax SF U W1S W2S := _hTypeP
  rcases hTypePFull with
    ⟨_hSFsource, _hW1cyc, _hW1ne, _hW1hall, _hSsplit, _hU_le,
      _hUnil, _hW1norm, hcomp, _hRest⟩
  exact
    ⟨theorem_10_7_semidirectProduct_of_mf_complement _hSF hcomp,
      theorem_10_7_frobenius_join_of_typeII_supported_source_data
        _h104 _hSmax _hSF _hTypeII _hPData _hTypeP _hTypeIIToIV _hUcomm
        _hUnorm _hF⟩

public theorem theorem_10_8_counting_selectedTypeP_pair_witness_reverse_supported_source
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
    (_h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ Wcase Smax Tmax SF TF U U1 U0 : Subgroup G,
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 Tmax Smax TF SF ∧
        section16TypeII Smax SF ∧
          Section8.typePDefinitionData Smax SF U W2 W1 ∧
            Section8.typeIIToIVSourceCondition Smax U W2 ∧
              IsMulCommutative U ∧
                (¬ Subgroup.normalizer (U : Set G) ≤ Smax) ∧
                  Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0 := by
  -- Source endpoint for the PF `(10.8)` Type-P pair witness: this is the
  -- case-`(8.8)(b)` sides.
  classical
  have h10 := hypothesis_10_1_of_hypothesis_10_4_supported_data _h104
  rcases h10 with
    ⟨hM, hType, _hFamily, _hW1M, _hW2M, _hW12M, hDade, _h46,
      _hNotation10, _h52⟩
  rcases hType with ⟨_hVeq, Usource, hP, hCases⟩
  rcases hDade with ⟨Ms, _Abook, _A0book, _A1book, _H, hNotation, _hA0M, _hτ⟩
  have hPFull : Section8.typePDefinitionData M MF Usource W1 W2 := hP
  rcases hPFull with
    ⟨hMF, _hW1cyc, hW1ne, _hW1hall, hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit, _hFitDer,
      _hW2leInf, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  have hTail :
      Section8.typeIIIDefinitionData M MF ∨
        Section8.typeIVDefinitionData M MF ∨
          Section8.typeVDefinitionData M MF := by
    rcases hCases with hIII | hIV | hV
    · exact Or.inl
        ⟨Usource, W1, W2, hP, hIII.1, hIII.2.1, hIII.2.2⟩
    · exact Or.inr <| Or.inl
        ⟨Usource, W1, W2, hP, hIV.1, hIV.2.1, hIV.2.2⟩
    · exact Or.inr <| Or.inr
        ⟨Usource, W1, W2, hP, hV.1, hV.2⟩
  have hSourceLateM :
      Section8.typeIIDefinitionData M MF ∨
        Section8.typeIIIDefinitionData M MF ∨
          Section8.typeIVDefinitionData M MF ∨
            Section8.typeVDefinitionData M MF :=
    Or.inr hTail
  have hMs : Section8.msChoiceSource M MF Ms := hNotation.2.2.1
  rcases Section8.sourceTypeP_exists_KUData_of_aligned_complement
      (G := G) hM hP with
    ⟨Uc, hKU⟩
  have hCaseP1 : section16CaseP1 W1 Uc :=
    section10_caseP1_of_msChoice_tail
      (G := G) (M := M) (MF := MF) (W1 := W1) (Uc := Uc) (Ms := Ms)
      hM hMF hMs hKU hTail
  have hC : section16TheoremCConclusions M MF W1 Uc :=
    theorem_16_C (G := G) hM hMF hKU hCaseP1.1
  let Kstar : Subgroup G := section16Kstar M W1
  rcases hC with
    ⟨_hUcommM, _hNormM, _hKstarCyclic, hKstarPos, _hKstarMF,
      _hMFnotCyclic, _hDerEq, _hKstarSecond, Mstar, hMstarP, _hUnique,
      hKstarStar, hKstarHall, _hPrimeX, _hPrimeY, hInter, hProd, hZcyc,
      hCase, hCover, hHatTI, _hHatEq, _hHatTISubset, _hKprimeIfUne,
      _hKstarPrimeIfBot⟩
  have hKstar_eq_W2 : Kstar = W2 := by
    dsimp [Kstar]
    exact theorem_10_7_section16Kstar_eq_W2_of_source_typeP hM hP
  have hKstarStar_eq_W1 : section16Kstar Mstar Kstar = W1 := by
    dsimp [Kstar]
    exact hKstarStar.symm
  have hKstarStarW2_eq_W1 : section16Kstar Mstar W2 = W1 := by
    rw [← hKstar_eq_W2]
    exact hKstarStar_eq_W1
  have hMstarP2 : Mstar ∈ section14MFamilyP2 G := by
    rcases hCase with hCaseP2 | hMstarP2
    · exact False.elim (hCaseP2.2 hCaseP1.2)
    · simpa [section16MaximalTypeP2] using hMstarP2
  have hMstarMax : Mstar ∈ section9MaximalSubgroups G := hMstarP.1
  rcases section16_exists_mfSubgroup (G := G) Mstar with ⟨SF, hSF⟩
  rcases section16_exists_KUData_of_kappa_hall
      (G := G) (M := Mstar) (K := Kstar) hMstarP hKstarHall with
    ⟨U, hKUT⟩
  have hTypeIIMstar : section16TypeII Mstar SF :=
    section16_typeII_of_MFamilyP2 (G := G) hSF hKUT hMstarP2
  rcases Section8.theorem_8_8_typeII_to_source_with_KUData_public
      (G := G) (M := Mstar) (MF := SF) (K := Kstar) (U := U)
      hMstarMax hSF hKUT hTypeIIMstar with
    ⟨U1, U0, _hPData, hTypePsrc, hTypeIIToIVsrc, hUcomm, hUnorm, hF⟩
  have hTypePAlign : Section8.typePDefinitionData Mstar SF U W2 W1 := by
    simpa [hKstar_eq_W2, hKstarStarW2_eq_W1] using hTypePsrc
  have hTypeIIToIVAlign : Section8.typeIIToIVSourceCondition Mstar U W2 := by
    simpa [hKstar_eq_W2] using hTypeIIToIVsrc
  have hTypeIIDefMstar : Section8.typeIIDefinitionData Mstar SF :=
    ⟨U, Kstar, section16Kstar Mstar Kstar, U1, U0, hTypePsrc,
      hTypeIIToIVsrc, hUcomm, hUnorm, hF⟩
  have hCompMstar :
      section12ComplementIn Mstar Kstar (ambientDerivedSubgroup Mstar) := by
    simpa [section16KappaPrimes] using
      theorem_14_7_h (G := G) (M := Mstar) (K := Kstar) hMstarP
        (by simpa [section16KappaPrimes] using hKstarHall)
  let Wcase : Subgroup G := section16ZSubgroup W1 W2
  have hZcycW : IsCyclic (W1 ⊔ W2 : Subgroup G) := by
    rw [← hKstar_eq_W2]
    exact hZcyc
  have hProdW : section12InternalDirectProduct W1 W2 Wcase := by
    simpa [Wcase, Kstar, hKstar_eq_W2, section16ZSubgroup] using hProd
  have hCycW : IsCyclic Wcase := by
    change IsCyclic (W1 ⊔ W2 : Subgroup G)
    exact hZcycW
  have hW2ne : W2 ≠ ⊥ := by
    simpa [← hKstar_eq_W2] using (ne_of_gt hKstarPos)
  have hNormalizer :
      ∀ W0 : Set G,
        W0.Nonempty →
          W0 ⊆ (Wcase : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) →
            Subgroup.normalizer W0 = Wcase := by
    intro W0 hW0ne hW0sub
    have hHatWTI :
        section16TISubsetWithNormalizer (section16HatW W1 W2)
          (W1 ⊔ W2 : Subgroup G) := by
      simpa [Kstar, hKstar_eq_W2, section16HatW, section16HatZ,
        section16ZSubgroup] using hHatTI
    have hWcomm : IsMulCommutative (W1 ⊔ W2 : Subgroup G) := by
      have hCyc : IsCyclic (W1 ⊔ W2 : Subgroup G) := by
        exact hZcycW
      let _ : IsCyclic (W1 ⊔ W2 : Subgroup G) := hCyc
      infer_instance
    have hW0subHat : W0 ⊆ section16HatW W1 W2 := by
      simpa [Wcase, section16HatW, section16ZSubgroup] using hW0sub
    simpa [Wcase, section16ZSubgroup] using
      section16_hatW_subset_normalizer_eq_of_ti
        (G := G) hHatWTI hWcomm hW0ne hW0subHat
  have hSeq : M = ambientDerivedSubgroup M ⊔ W1 := hMcomp.2.2.1
  have hSdisj : Disjoint (ambientDerivedSubgroup M) W1 := hMcomp.2.2.2
  have hTeq : Mstar = ambientDerivedSubgroup Mstar ⊔ W2 := by
    calc
      Mstar = Kstar ⊔ ambientDerivedSubgroup Mstar := hCompMstar.2.2.1
      _ = ambientDerivedSubgroup Mstar ⊔ Kstar :=
        sup_comm Kstar (ambientDerivedSubgroup Mstar)
      _ = ambientDerivedSubgroup Mstar ⊔ W2 := by rw [hKstar_eq_W2]
  have hTdisj : Disjoint (ambientDerivedSubgroup Mstar) W2 := by
    rw [← hKstar_eq_W2]
    exact hCompMstar.2.2.2.symm
  have hST : M ⊓ Mstar = Wcase := by
    simpa [Wcase, Kstar, hKstar_eq_W2, section16ZSubgroup] using hInter
  have hCoverSource :
      ∀ N : Subgroup G, N ∈ section9MaximalSubgroups G →
        (∃ g : G, N = M.conjBy g) ∨
          (∃ g : G, N = Mstar.conjBy g) ∨
            ∃ NF : Subgroup G, section16MFSubgroup N NF ∧
              Section8.typeIDefinitionData N NF := by
    intro N hN
    by_cases hNP : N ∈ section14MFamilyP G
    · rcases hCover N (by simpa [section16MaximalTypeP] using hNP) with hNM | hNMstar
      · exact Or.inl hNM
      · exact Or.inr <| Or.inl hNMstar
    · rcases section16_exists_mfSubgroup (G := G) N with ⟨NF, hNF⟩
      exact Or.inr <| Or.inr <|
        ⟨NF, hNF,
          Section8.theorem_8_8_typeI_to_source_public
            (G := G) hN hNF (section16_typeI_of_not_MFamilyP (G := G) hN hNF hNP)⟩
  have hcase :
      Section8.theorem_8_8_source_case_b_data Wcase W1 W2 M Mstar MF SF := by
    exact ⟨hProdW, hCycW, hW1ne, hW2ne, hNormalizer, hM, hMstarMax,
      hMF, hSF, hSeq, hTeq, hSdisj, hTdisj, hST, Or.inr hTypeIIDefMstar,
      hSourceLateM, Or.inl hTypeIIDefMstar, hCoverSource⟩
  exact ⟨Wcase, Mstar, M, SF, MF, U, U1, U0, hcase, hTypeIIMstar,
    hTypePAlign, hTypeIIToIVAlign, hUcomm, hUnorm, hF⟩

public theorem theorem_10_8_counting_selectedTypeP_pair_witness_supported_source
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
    (h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ Wcase Smax Tmax SF TF U U1 U0 : Subgroup G,
      Section8.theorem_8_8_source_case_b_data Wcase W2 W1 Smax Tmax SF TF ∧
        section16TypeII Smax SF ∧
          Section8.typePDefinitionData Smax SF U W2 W1 ∧
            Section8.typeIIToIVSourceCondition Smax U W2 ∧
              IsMulCommutative U ∧
                (¬ Subgroup.normalizer (U : Set G) ≤ Smax) ∧
                  Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0 := by
  rcases theorem_10_8_counting_selectedTypeP_pair_witness_reverse_supported_source h104 with
    ⟨Wcase, Smax, Tmax, SF, TF, U, U1, U0, hcase, hTypeII,
      hTypeP, hTypeIIToIV, hUcomm, hUnorm, hF⟩
  exact ⟨Wcase, Smax, Tmax, SF, TF, U, U1, U0,
    Section8.theorem_8_8_source_case_b_data_swap hcase, hTypeII, hTypeP,
    hTypeIIToIV, hUcomm, hUnorm, hF⟩

public theorem theorem_10_8_counting_selectedTypeP_fields_supported_source
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
    (h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ Smax SF U U1 U0 : Subgroup G,
      Smax ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup Smax SF ∧
          section16TypeII Smax SF ∧
            Section8.typePDefinitionData Smax SF U W2 W1 ∧
              Section8.typeIIToIVSourceCondition Smax U W2 ∧
                IsMulCommutative U ∧
                  (¬ Subgroup.normalizer (U : Set G) ≤ Smax) ∧
                    Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0 := by
  rcases theorem_10_8_counting_selectedTypeP_pair_witness_supported_source h104 with
    ⟨Wcase, Smax, Tmax, SF, TF, U, U1, U0, hcase, hTypeII,
      hTypeP, hTypeIIToIV, hUcomm, hUnorm, hF⟩
  rcases hcase with
    ⟨_hprod, _hcyc, _hW2ne, _hW1ne, _hnorm, hSmax, _hTmax, hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeIIone, _hSType, _hTType,
      _hCover⟩
  exact ⟨Smax, SF, U, U1, U0, hSmax, hSF, hTypeII, hTypeP,
    hTypeIIToIV, hUcomm, hUnorm, hF⟩

public theorem theorem_10_8_counting_selectedTypeP_alignment_supported_source
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
    (h104 : hypothesis_10_4_supported_data M MF W1 W2 V W A A0 S τ τ₁ ξ i0 j0 μ δSign ω σ d n δ) :
    ∃ Smax SF U U1 U0 : Subgroup G,
      Smax ∈ section9MaximalSubgroups G ∧
        section16TypeII Smax SF ∧
          Section8.typePDefinitionData Smax SF U W2 W1 ∧
            Section8.typeIIToIVSourceCondition Smax U W2 ∧
              IsMulCommutative U ∧
                (¬ Subgroup.normalizer (U : Set G) ≤ Smax) ∧
                  Section8.typeFData (ambientDerivedSubgroup Smax) SF U U1 U0 := by
  rcases theorem_10_8_counting_selectedTypeP_fields_supported_source h104 with
    ⟨Smax, SF, U, U1, U0, hSmax, _hSF, hTypeII, hTypeP,
      hTypeIIToIV, hUcomm, hUnorm, hF⟩
  exact ⟨Smax, SF, U, U1, U0, hSmax, hTypeII, hTypeP,
    hTypeIIToIV, hUcomm, hUnorm, hF⟩


public theorem theorem_10_8_counting_selectedTypeP_frobeniusPackage_supported_source
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
        μ δSign ω σ d n δ) :
    ∃ Smax SF U : Subgroup G,
      Smax ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup Smax SF ∧
          section16TypeII Smax SF ∧
            Section2.IsInternalSemidirectProduct (ambientDerivedSubgroup Smax) SF U ∧
              section12FrobeniusJoinWithKernel SF U ∧
                Section8.typePDefinitionData Smax SF U W2 W1 := by
  rcases theorem_10_8_counting_selectedTypeP_alignment_supported_source _h104 with
    ⟨Smax, SF, U, U1, U0, hSmax, hTypeII, hTypeP,
      hTypeIIToIV, hUcomm, hUnorm, hF⟩
  have hSF : section16MFSubgroup Smax SF := hTypeP.1
  have hPData : Section8.typePData Smax SF U W2 W1 :=
    typePData_of_typePDefinitionData hSmax hSF hTypeP
  rcases theorem_10_7_frobenius_bridge_of_typeII_supported_source_data
      _h104 hSmax hSF hTypeII hPData hTypeP hTypeIIToIV hUcomm hUnorm hF with
    ⟨hsemi, hfrob⟩
  exact ⟨Smax, SF, U, hSmax, hSF, hTypeII, hsemi, hfrob, hTypeP⟩

public theorem theorem_10_8_counting_contradiction_supported_source
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
        μ δSign ω σ d n δ) :
    False := by
  rcases theorem_10_8_counting_selectedTypeP_frobeniusPackage_supported_source
      _h104 with
    ⟨Smax, SF, U, hSmax, hSF, hTypeII, hsemi, hfrob, hPAlign⟩
  rcases theorem_10_8_counting_cardinality_bounds_supported_source
      _h104 hSmax hSF hTypeII hsemi hfrob hPAlign with
    ⟨q, r, hm, hq, hr, hlt⟩
  exact theorem_10_8_counting_cardinality_contradiction
    (w1 := Nat.card W1) (w2 := Nat.card W2)
    (m := Nat.card (ambientDerivedSubgroup M)) (q := q) (r := r)
    (Nat.card_pos (α := W2)) hm hq hr hlt

public theorem theorem_10_8_coherence_contradiction_of_hypothesis_10_4_a_supported_data
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
    False := by
  rcases theorem_10_8_hypothesis_10_4_supported_of_coherence h104a hcoh with
    ⟨τ₁, h104⟩
  exact theorem_10_8_counting_contradiction_supported_source h104

public theorem theorem_10_8_supported
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (M MF W1 W2 : Subgroup G)
    (V : Set G)
    (S : Finset (Section1.ClassFunction M))
    (τ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    : hypothesis_10_1_supported_data M MF W1 W2 V S τ →
      ¬ Section6.coherentFamily S τ := by
  intro h10 hcoh
  rcases theorem_10_8_exists_hypothesis_10_4_a_supported_data h10 with
    ⟨I, instI, decI, J, instJ, decJ, W, A, A0, i0, j0, μ, δSign, ω, σ,
      ξ, d, n, δ, h104a⟩
  let : Fintype I := instI
  let : DecidableEq I := decI
  let : Fintype J := instJ
  let : DecidableEq J := decJ
  exact theorem_10_8_coherence_contradiction_of_hypothesis_10_4_a_supported_data
    (M := M) (MF := MF) (W1 := W1) (W2 := W2) (V := V) (W := W)
    (A := A) (A0 := A0) (S := S) (τ := τ) (ξ := ξ) (i0 := i0)
    (j0 := j0) (μ := μ) (δSign := δSign) (ω := ω) (σ := σ)
    (d := d) (n := n) (δ := δ) h104a hcoh


end Section10
