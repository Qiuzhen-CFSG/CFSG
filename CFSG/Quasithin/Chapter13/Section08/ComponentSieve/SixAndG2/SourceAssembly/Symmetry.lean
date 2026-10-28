module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Dichotomy

/-!
# Case-one symmetry from the actual surviving modules

Identify the range of the actual center-quotient action with H* using its
literal conjugation formula and faithfulness. Transfer its transvection
back to the same binary representation. The A₆ and L₄ whole-module models
then discharge every model premise of the proved denominator-symmetry
argument, including the augmentation cover coordinates.
The conclusions retain the original critical pair and its conjugator.
Source: Aschbacher–Smith, 13.8.27(3), printed p.963.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open CriticalGeometry CriticalGeometry.AsymmetricPair SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem quotient_action_agrees
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (h : H) (v : Additive (Source.Utilde H V₃ V₁)) :
    ρ (QuotientGroup.mk' (pCore 2 H) h) v = Additive.ofMul (Q.action h v.toMul) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  exact (hρ h x).trans (congrArg Additive.ofMul (Q.apply_mk h x)).symm

omit [Finite G] in
private theorem action_image_model
    {B E : Type*} [Group B] [AddCommGroup E] [Module (ZMod 2) E]
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hf : Function.Injective ρ)
    (σ : Representation (ZMod 2) B E) (hm : HasActionModel ρ σ) :
    Nonempty (Q.Model σ) := by
  obtain ⟨eB, eU, he⟩ := hm
  have hk : Q.action.ker = pCore 2 H := by
    ext h
    change Q.action h = 1 ↔ h ∈ pCore 2 H
    rw [← QuotientGroup.eq_one_iff h, ← hf.eq_iff, map_one]
    constructor
    · intro hh
      apply LinearMap.ext
      intro v
      change ρ (QuotientGroup.mk' (pCore 2 H) h) v = v
      rw [quotient_action_agrees Q ρ hρ h v, hh]
      rfl
    · intro hh
      apply MulEquiv.ext
      intro v
      have hv := LinearMap.congr_fun hh (Additive.ofMul v)
      change ρ (QuotientGroup.mk' (pCore 2 H) h) (Additive.ofMul v) = Additive.ofMul v at hv
      exact congrArg Additive.toMul
        ((quotient_action_agrees Q ρ hρ h (Additive.ofMul v)).symm.trans hv)
  let e : Source.Hstar H ≃* Q.action.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange Q.action)
  have emk (h : H) : e (QuotientGroup.mk' (pCore 2 H) h) = Q.action.rangeRestrict h := rfl
  refine ⟨{ groupEquiv := e.symm.trans eB, moduleEquiv := eU, intertwines := ?_ }⟩
  intro a v
  obtain ⟨h, hh⟩ := a.property
  have ha : a = Q.action.rangeRestrict h := Subtype.ext hh.symm
  subst a
  change eU (Additive.ofMul (Q.action h v)) = σ (eB (e.symm (Q.action.rangeRestrict h))) _
  rw [← emk, e.symm_apply_apply]
  exact (congrArg eU (quotient_action_agrees Q ρ hρ h (Additive.ofMul v))).symm.trans (he _ _)

omit [Finite G] in
private theorem transvection_of_action_image
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (h : H) (hn : Q.action h ≠ 1)
    (ht : binaryLinear (Q.action h) ∈ LinearEquiv.transvections (ZMod 2)
      (Additive (Source.Utilde H V₃ V₁))) :
    IsTransvection ρ (QuotientGroup.mk' (pCore 2 H) h) := by
  obtain ⟨f, v, hfv, he⟩ := ht
  have hact (w : Additive (Source.Utilde H V₃ V₁)) :
      ρ (QuotientGroup.mk' (pCore 2 H) h) w = w + f w • v := by
    rw [quotient_action_agrees Q ρ hρ]
    exact congrArg (fun e : _ ≃ₗ[ZMod 2] _ => e w) he
  have hf : f ≠ 0 := by
    intro hz
    apply hn
    ext w
    have hw := hact (Additive.ofMul w)
    rw [quotient_action_agrees Q ρ hρ] at hw
    simpa [hz] using hw
  have hv : v ≠ 0 := by
    intro hz
    apply hn
    ext w
    have hw := hact (Additive.ofMul w)
    rw [quotient_action_agrees Q ρ hρ] at hw
    simpa [hz] using hw
  exact ⟨f, v, hf, hv, hfv, hact⟩

/-- The module alternatives supply the exact model premise of the proved
case-one denominator symmetry. The natural and cover maps retain the
original action; the rejected seven-letter row is never introduced. -/
theorem symmetry_models_of_survivors
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (models : (∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) ∨
      HasActionModel ρ projectiveFourRepresentation)
    (Q : CenterQuotientAction H (Source.UH H V₃) V₁)
    (ht : ∃ t : H, Q.action t ≠ 1 ∧ binaryLinear (Q.action t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (Source.Utilde H V₃ V₁))) :
    (Nonempty (Q.Model linearFourRepresentation) ∨
      Nonempty (Q.Model (BinaryPermutation.naturalRepresentation (Fin 6)))) ∨
      Nonempty (CoverHyperplanes.CoverCoordinates H V₃ V₁) := by
  have hk : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H :=
    (f9_commutatorPreimage_eq _ hF9 H le_rfl).le.trans inf_le_right
  have hf := faithful_of_centralizer_le_core ρ hρ hk
  obtain ⟨t, hn, ht⟩ := ht
  have htρ := transvection_of_action_image Q ρ hρ t hn ht
  rcases models with ⟨eK, hs⟩ | ⟨eH, eU, he⟩
  · rcases alternatingSix_full_module_of_section hKH hK hN ρ hρ hk hUK eK hs _ htρ with
      ⟨eH, eU, _, he⟩ | ⟨eH, eU, _, he⟩
    · exact Or.inl (Or.inr (action_image_model Q ρ hρ hf _ ⟨eH, eU, he⟩))
    · refine Or.inr ⟨{
        groupEquiv := eH
        linearEquiv := eU
        normalizes := le_normalizer_conjugateSpanBy V₃ H
        intertwines := ?_ }⟩
      intro h v
      exact (he (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ v)).symm.trans
        (congrArg eU (hρ h v))
  · exact Or.inl (Or.inl (action_image_model Q ρ hρ hf _
      ⟨eH.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)), eU, he⟩))


/-- Clause (3) on the unchanged critical pair. Its geometric model input is
constructed from the recognized survivor action, rather than retained as a
callback to the desired denominator symmetry. -/
theorem source_case_one_of_survivor_models
    (embeddings : AlternatingAndLinear.LinearReduction.Overgroup.EarlierEmbeddings.{u}
      KnownSimple.IsKnownSimple)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (facts : AlternatingAndLinear.LinearReduction.Overgroup.UniformComponentFacts
      L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (models : (∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) ∨
      HasActionModel ρ projectiveFourRepresentation)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hcase : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) :
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∧
      ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧ ¬ c.Vgamma ≤ Source.QH H ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃))) := by
  have hh := Overgroup.source_case_one_known embeddings d facts hKH hK hHz hF9 c hcentral
    (fun Q _ _ _ ht => by
      rcases symmetry_models_of_survivors hF9 hKH hK (facts.normal hHz hKH hK)
        hUK ρ hρ models Q ht with (h4 | h6) | hc
      · exact Or.inl (Or.inl h4)
      · exact Or.inl (Or.inr (Or.inl h6))
      · exact Or.inr hc) hcase
  exact hh.2.2.2.2.2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
