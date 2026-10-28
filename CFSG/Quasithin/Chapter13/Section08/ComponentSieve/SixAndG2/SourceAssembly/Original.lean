module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.Terminal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.OriginalG2
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.OriginalOvergroup

/-!
# Original 13.8.27 after the completed preceding reductions

The component, field and linear producers now supply all local sieve inputs.
The actual quadratic critical pair constructs the G₂ orbit data, and the
source containing-component argument proves G₁=H=KT. Both A₆ critical cases
and the covered L₄ case retain the whole action, intrinsic component marking,
central attachments and original pair. These models give case-one symmetry.

The terminal applications construct the ordinary syntheme-edge/module-plane
markings and covered endpoint module of order 32. The last application also
selects the actual component and constructs the literal quotient action.
No embedding, orbit, field/linear model or terminal-marking callback remains.

The original LocalSetup, maximal-local, F.9 applicability, centralizer and
noncentrality hypotheses, and the genuine earlier 13.7.6 inputs remain
explicit. Their producers qt-d-135-preparation-source and qt-d-1378-source
and final assembly qt-d-1381-source retain discharge. This is not an
unconditional proof of 13.8.1 or either subsequent terminal exclusion.
Source: Aschbacher–Smith, 13.8.26–34, printed pp.962–969.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open CriticalGeometry SourceCompletion
open FieldComponents.HigherFieldReduction.ExternalModules
open AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

open CriticalGeometry.AsymmetricPair

/-- Original 13.8.27(1–2) with component, field, linear and orbit inputs discharged. -/
theorem original_dichotomy
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      ((∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
          HasSectionModel H V₃ V₁ ρ K hKH
            (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SourceSix.MarkedFullAction hKH eK ρ ∧
          Reorientation.TwoNoncentralChiefFactors
            (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
              (le_sup_left.trans hHz.1.2) ρ)) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          HasActionModel ρ projectiveFourRepresentation)) := by
  have hF9 := hF9all H hHz
  have facts := original_uniform_component_facts d earlier localEarlier hmax hF9all hcentral hcomm
  have hN := facts.normal hHz hKH hK
  obtain ⟨hfit, hUK, P, hP⟩ := original_component_structure d hmax hF9all hcentral hcomm
    hHz hKH hK
  have hcon := FieldComponents.HigherFieldReduction.OriginalSource.original_component_consequences
    d hmax hF9all hcentral hcomm hHz hKH hK
  obtain ⟨hc, hn, hGH, hKT⟩ := original_overgroup_equalities d earlier localEarlier facts
    hHz hF9 hKH hK hfit hUK hcentral hcomm ρ hρ
  refine ⟨hc, hn, hGH, hKT, hcon.2.2.1, ?_⟩
  rcases Overgroup.surviving_quotient facts hHz hKH hK with h6 | h4 | hg2
  · obtain ⟨eK⟩ := h6
    obtain ⟨eK', hs, _, hL, hm, hchief⟩ := six_source_alternative d earlier localEarlier
      hHz hF9 hKH hK hN hKT hfit hUK hcentral hcomm eK ρ hρ
    exact Or.inl ⟨eK', hs, hL, hm, hchief⟩
  · exact Or.inr (original_linear_models d earlier localEarlier hmax hF9all hcentral hcomm
      hHz hKH hK ρ hρ h4)
  · obtain ⟨eK⟩ := hg2
    have hjoin : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) := by
      rw [← sup_assoc, sup_eq_left.mpr (facts.base_le hHz hKH hK)]
      exact hKT
    have orbit := g2_orbit_inputs_from_quadratic_actor d hHz hF9 hKH hK hN hjoin
      hfit hUK hcentral hcomm ρ hρ P hP eK
    exact (g2_exclusion d hHz hF9 hGH.symm hKH hK hN hjoin hfit hUK hcentral hcomm
      ρ hρ P hP orbit eK).elim

/-- All three clauses on the unchanged original critical pair and quotient action. -/
theorem original_dichotomy_and_symmetry
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    ((K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      ((∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
          HasSectionModel H V₃ V₁ ρ K hKH
            (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SourceSix.MarkedFullAction hKH eK ρ ∧
          Reorientation.TwoNoncentralChiefFactors
            (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
              (le_sup_left.trans hHz.1.2) ρ)) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          HasActionModel ρ projectiveFourRepresentation))) ∧
    (∀ c : CriticalPair L (T : Subgroup G) H V,
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∨
        Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃) →
    let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
    Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃ ∧
      Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃ ∧
      ⁅V, c.Ugamma V₃⁆ = V₁ ∧ V₁ ≤ c.Ugamma V₃ ∧ ¬ c.Vgamma ≤ Source.QH H ∧
      ∃ action : V →* MulAut (c.Ugamma V₃),
        (∀ v : V, ∀ u : c.Ugamma V₃,
          (action v u : G) = (v : G) * (u : G) * (v : G)⁻¹) ∧
        (∃ v : V, action v ≠ 1) ∧
        (∀ v : V, binaryLinear (action v) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (c.Ugamma V₃)))) := by
  have result := original_dichotomy d earlier localEarlier hmax hF9all hcentral hcomm
    hHz hKH hK ρ hρ
  refine ⟨result, ?_⟩
  have models : (∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK) ∨
      HasActionModel ρ projectiveFourRepresentation := by
    rcases result.2.2.2.2.2 with hs | hl
    · obtain ⟨eK, hs, _⟩ := hs
      exact Or.inl ⟨eK, hs⟩
    · exact Or.inr hl.2
  have hN : (K.subgroupOf H).Normal := result.2.2.1 ▸ result.2.1
  have hUK := (FieldComponents.HigherFieldReduction.OriginalSource.original_component_consequences
    d hmax hF9all hcentral hcomm hHz hKH hK).2.2.2
  obtain ⟨Q⟩ := exists_centerQuotientAction (U := Source.UH H V₃) (Z := V₁)
    (le_normalizer_conjugateSpanBy V₃ H) (hHz.2.1.trans d.first_normalizer.le)
  have hnot : ¬ V₂ ≤ V₁ := by
    intro hh
    have hc := card_le_of_le hh
    rw [d.plane_card, d.line_card] at hc
    omega
  obtain ⟨b, hb, hbZ⟩ := SetLike.not_le_iff_exists.mp hnot
  let b' : Source.UH H V₃ := ⟨b, (d.plane_le_seed.trans (le_conjugateSpanBy V₃ H)) hb⟩
  intro c hcase
  exact Overgroup.Symmetry.case_one d hHz (hF9all H hHz) c result.2.2.1.symm
    hcentral Q b' hb hbZ (fun ht => by
      rcases symmetry_models_of_survivors (hF9all H hHz) hKH hK hN hUK ρ hρ models Q ht with
        (h4 | h6) | hc
      · exact Or.inl (Or.inl h4)
      · exact Or.inl (Or.inr (Or.inl h6))
      · exact Or.inr hc) hcase


/-- Apply the source dichotomy to both literal ordinary and covered terminal setups. -/
theorem original_terminal_setups
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (earlierFlags : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (sourceOne L T V₁) (T : Subgroup G) G₁ M V₂ V₃ V₁)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁) :
    let ρ := A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a
    G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      ((∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
          HasSectionModel H V₃ V₁ ρ K hKH
            (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SourceSix.MarkedFullAction hKH eK ρ ∧
          Reorientation.TwoNoncentralChiefFactors
            (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
              (le_sup_left.trans hHz.1.2) ρ) ∧
          TerminalRanks.MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) ∧
          HasActionModel ρ linearFourRepresentation ∧
          Nat.card (Source.UH H V₃) = 32 ∧ rank (Source.UH H V₃) = 5 ∧
          ∀ c : CriticalPair L (T : Subgroup G) H V, Nat.card (c.Ugamma V₃) = 32)) := by
  let ρ := A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a
  have hd := original_dichotomy d earlier localEarlier hmax hF9all hcentral hcomm
    hHz hKH hK ρ (TerminalPoint.starAction_isConjugation a)
  refine ⟨hd.2.2.1, hd.2.2.2.1, ?_⟩
  rcases hd.2.2.2.2.2 with h6 | h4
  · obtain ⟨eK, hs, hL, hm, hchief⟩ := h6
    exact Or.inl ⟨eK, hs, hL, hm, hchief,
      TerminalModels.ordinary_terminal_models d earlierFlags hHz (hF9all H hHz) hcomm hKH hK
        (Components.original_component_normal d hmax hF9all hcentral hcomm hHz hKH hK)
        hd.2.2.2.1 a eK hs⟩
  · exact Or.inr ⟨h4.1, covered_terminal_setup d h4.1 ρ h4.2⟩


omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- Select the original component and construct its quotient action before the terminal application. -/
theorem original_selected_terminal_setups
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (earlierFlags : TransvectionParabolic.Marking.NaturalSection.Earlier1376 L
      (sourceOne L T V₁) (T : Subgroup G) G₁ M V₂ V₃ V₁) :
    let := d.uh_elementary hHz
    ∃ (K : Subgroup G) (hKH : K ≤ H) (_hK : (K.subgroupOf H).IsCComponent)
      (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁),
    let ρ := A6Endgame.IntersectionBalance.tildeRepresentation H _ V₁ a
    G₁ = H ∧ H = K ⊔ (T : Subgroup G) ∧
      ((∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
          HasSectionModel H V₃ V₁ ρ K hKH
            (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) eK ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SourceSix.MarkedFullAction hKH eK ρ ∧
          Reorientation.TwoNoncentralChiefFactors
            (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
              (le_sup_left.trans hHz.1.2) ρ) ∧
          TerminalRanks.MarkedModels H ((L ⊔ (T : Subgroup G)) ⊓ H) V₃ V₁) ∨
        (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) ∧
          HasActionModel ρ linearFourRepresentation ∧
          Nat.card (Source.UH H V₃) = 32 ∧ rank (Source.UH H V₃) = 5 ∧
          ∀ c : CriticalPair L (T : Subgroup G) H V, Nat.card (c.Ugamma V₃) = 32)) := by
  let := d.uh_elementary hHz
  obtain ⟨K, hKH, hK, _⟩ := Components.original_exists_normal_component
    d hmax hF9all hcentral hcomm hHz
  have hF9 := hF9all H hHz
  obtain ⟨a⟩ := SolvableExclusion.Five.exists_starAction H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H)
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  exact ⟨K, hKH, hK, a, original_terminal_setups d earlier localEarlier hmax hF9all
    hcentral hcomm hHz hKH hK earlierFlags a⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
