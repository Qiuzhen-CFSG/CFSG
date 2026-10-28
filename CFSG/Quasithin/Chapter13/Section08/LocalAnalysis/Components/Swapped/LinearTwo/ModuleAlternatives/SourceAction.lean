module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Projection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Quotient

/-!
# The literal binary conjugation action in 13.8.16

The module is the additive group of U_H/V₁, with U_H the H-conjugate
span of V₃. Abelianity of this span and exponent two of the seed make it
elementary abelian. Conjugation normalizes the span; normalization of V₁
constructs the action on its literal quotient. The earlier source bound
[U_H,O₂(H)] ≤ V₁ descends that action to H*. The reverse centralizer
bound makes the descended action faithful.

The seed and its generation theorem are the existing literal source
constructions, reused from ChiefFactors.SourceChiefFactors. No component-module
classification or maximality-to-irreducibility assertion is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
standing notation on printed pp.946–947, F.9.2(3), and proof of 13.8.16(1),
printed p.952 (PDF p.969).
-/

@[expose] public noncomputable section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
open ComponentSieve.AlternatingAndLinear.FourStructure

variable {G : Type*} [Group G]

/-- The exponent of the conjugate span comes from the actual elementary seed. -/
theorem elementary_UH (H V₃ : Subgroup G)
    [IsElementaryAbelian 2 V₃] [IsMulCommutative (Source.UH H V₃)] :
    IsElementaryAbelian 2 (Source.UH H V₃) := by
  unfold Source.UH conjugateSpanBy at *
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨h, _, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]

variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]

/-- The chosen automorphism action on the literal quotient. Its formula,
not the choice of witness, identifies it with the source conjugation action. -/
def quotientAction (hV₁ : H ≤ normalizer (V₁ : Set G)) :
    H →* MulAut (Source.Utilde H V₃ V₁) :=
  Classical.choose (exists_quotient_conjugation_action H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) hV₁ inferInstance)

theorem quotientAction_apply (hV₁ : H ≤ normalizer (V₁ : Set G))
    (h : H) (u : Source.UH H V₃) :
    quotientAction H V₃ V₁ hV₁ h (ChiefFactors.sourceProjection H V₃ V₁ u) =
      ChiefFactors.sourceProjection H V₃ V₁ (ChiefFactors.sourceConjugate H V₃ h u) :=
  Classical.choose_spec (exists_quotient_conjugation_action H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) hV₁ inferInstance) h u

theorem core_le_quotientAction_ker (hV₁ : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    pCore 2 H ≤ (quotientAction H V₃ V₁ hV₁).ker := by
  have hk := quotient_conjugation_action_kills_commutator_layer H (Source.UH H V₃)
    V₁ (Source.QH H) inferInstance (le_normalizer_conjugateSpanBy V₃ H) hcore
    (quotientAction H V₃ V₁ hV₁) (quotientAction_apply H V₃ V₁ hV₁)
  intro h hh
  exact hk (mem_map_of_mem H.subtype hh)

/-- Factorization through the actual two-core quotient, not an arbitrary actor. -/
def starAction (hV₁ : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    Source.Hstar H →* MulAut (Source.Utilde H V₃ V₁) :=
  QuotientGroup.lift (pCore 2 H) (quotientAction H V₃ V₁ hV₁)
    (core_le_quotientAction_ker H V₃ V₁ hV₁ hcore)

@[simp] theorem starAction_mk (hV₁ : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) (h : H) :
    starAction H V₃ V₁ hV₁ hcore (QuotientGroup.mk' (pCore 2 H) h) =
      quotientAction H V₃ V₁ hV₁ h := rfl

variable [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The binary representation of H* on Additive(U_H/V₁). -/
def representation (hV₁ : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁) where
  toFun a := (starAction H V₃ V₁ hV₁ hcore a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change Additive.ofMul ((starAction H V₃ V₁ hV₁ hcore 1) v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change Additive.ofMul ((starAction H V₃ V₁ hV₁ hcore (a * b)) v.toMul) = _
    rw [map_mul]
    rfl

/-- The action satisfies the existing source specification on every representative. -/
theorem representation_isSourceAction (hV₁ : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) :
    ChiefFactors.IsSourceAction H V₃ V₁ (representation H V₃ V₁ hV₁ hcore) := by
  intro h u
  exact congrArg Additive.ofMul (quotientAction_apply H V₃ V₁ hV₁ h u)

/-- The reverse half of C_H(Ũ_H)=O₂(H) proves faithfulness. The premise
is stated on actual group commutators, before constructing the representation. -/
theorem representation_faithful (hV₁ : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hcentralizer : ∀ h : H, (∀ u : Source.UH H V₃,
      ⁅(h : G), (u : G)⁆ ∈ V₁) → h ∈ pCore 2 H) :
    Function.Injective (representation H V₃ V₁ hV₁ hcore) := by
  apply (representation H V₃ V₁ hV₁ hcore).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro a ha
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
  apply (QuotientGroup.eq_one_iff h).mpr
  apply hcentralizer h
  intro u
  have he := congrArg (fun f => f (Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u))) ha
  change representation H V₃ V₁ hV₁ hcore (QuotientGroup.mk' (pCore 2 H) h)
    (Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u)) =
      Additive.ofMul (ChiefFactors.sourceProjection H V₃ V₁ u) at he
  rw [representation_isSourceAction H V₃ V₁ hV₁ hcore h u] at he
  have heq := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective he)
  change (h : G) * (u : G) * (h : G)⁻¹ / (u : G) ∈ V₁ at heq
  simpa only [commutatorElement_def, div_eq_mul_inv] using heq

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
