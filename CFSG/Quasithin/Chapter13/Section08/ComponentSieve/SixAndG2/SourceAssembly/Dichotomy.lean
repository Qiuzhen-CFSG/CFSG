module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.FullSix

/-!
# The marked 13.8.27 dichotomy from the preceding source reductions

The uniform component/field/linear quotient sieve and the constrained
overgroup argument give G₁=H=KT. The literal derived-G₂ section is impossible.
The A₆ branch is recognized here in both critical cases, with its component
marking, full actor and module action, and the two L₁ chief factors. In the
L₄ branch the independent preceding 13.8.25 module conclusion is retained
explicitly; the original local quotient dichotomy constructs the actual
hexacode-cover equivalence from its nontrivial center.

The genuine earlier component, field and linear inputs remain the outputs
of qt-d-138-components-source, qt-d-138-fields-source and qt-d-138-linear-source.
The assembly of these with the original setup stays with qt-d-1381-source.
This conditional statement does not discharge those preceding source stages.
Source: Aschbacher–Smith, 13.8.26–27, printed pp.962–963.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open CriticalGeometry SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

private theorem concrete_cover_of_local_alternative
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hc : Chapter1.Section02.LocalModels.IsAlternatingCover (L ⧸ pCore 2 L) 6) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases local_quotient_alternatives d with ⟨e, _⟩ | ⟨e, _⟩
  · obtain ⟨z⟩ := hc.2.1
    have hz : Nat.card (center (L ⧸ pCore 2 L)) = 3 :=
      (Nat.card_congr z.toEquiv).trans (Nat.card_zmod 3)
    have he := Nat.card_congr (centerCongr e).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), card_bot, hz] at he
    contradiction
  · exact ⟨e⟩

/-- The literal group-and-module alternatives of 13.8.27(1–2), conditional
only on the preceding source stages. No recognized A₆ section, G₂ exclusion,
selected geometry, or overgroup equality is an input. -/
theorem source_dichotomy
    (embeddings : EarlierEmbeddings.{u} KnownSimple.IsKnownSimple)
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (facts : UniformComponentFacts L (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (P : Sylow 2 (Source.Hstar H))
    (hP : Source.starImage H K ⊔ (P : Subgroup _) = ⊤)
    (orbit : letI : (Source.starImage H K).Normal := hfit ▸ inferInstance
      OrbitInputs ρ (Source.starImage H K) P hP)
    (linear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 →
      HasActionModel ρ projectiveFourRepresentation) :
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
  obtain ⟨hc, hn, hGH, hKT, hprod, hquot⟩ := surviving_source_quotients embeddings d facts
    hHz hF9 hKH hK hfit hUK hcentral hcomm ρ hρ P hP orbit
  refine ⟨hc, hn, hGH, hKT, hprod, ?_⟩
  rcases hquot with h6 | ⟨h4, hcov, _⟩
  · obtain ⟨eK⟩ := h6
    obtain ⟨eK', hs, _, hL, hm, hchief⟩ := six_source_alternative d earlier localEarlier
      hHz hF9 hKH hK (facts.normal hHz hKH hK) hKT hfit hUK hcentral hcomm eK ρ hρ
    exact Or.inl ⟨eK', hs, hL, hm, hchief⟩
  · exact Or.inr ⟨concrete_cover_of_local_alternative d hcov, linear h4⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
