module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseAssembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySourceEscape
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer

/-!
# Terminal assembly at the maximal ordinary A₆ source choice

Start with the actual maximal counterexample and its natural module and
flag. Choose H = G₁ using the original escape theorem. The completed
ordinary 13.7.8 argument supplies the abelian full span, and 13.5.7 supplies
F.9 on these same groups. Plane noncentrality supplies both the ambient
seed-centralizer bound and the seed-core noncentrality used at the endpoint.

The ordinary quotient L/O₂(L) rules out the covered alternative of 13.8.27:
its center is trivial, whereas the concrete triple cover has center of
order three. Thus this selected ordinary branch does not need the L₄(2)
exclusion in 13.8.28. The two denominator cases are then assembled using
the genuine filtration maps and the marked point-normalizer image.

This is conditional on the surviving earlier classification, escape and
plane inputs, the component supplement, and the 13.8.27/33 model producers.
It does not prove 13.8.1 for the covered local quotient or discharge those
source premises. The full theorem remains with the source assembly owner.
Source: Aschbacher--Smith, 13.8.1--2, 13.8.8, 13.8.27 and 13.8.33--34,
printed pp.946--949,963,966--969; maximal selection in Theorem D, p.1079.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
open CriticalGeometry
open TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Chapter14.Section08.LieTypeBranch

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

omit [Finite G] in
/-- The covered local alternative in 13.8.27 cannot occur at an ordinary
selected A₆ quotient. This compares actual centers, not family labels. -/
theorem not_covered_local_quotient
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr (centerCongr (e.symm.trans eL)).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp), card_bot] at hc
  omega

/-- The final ordinary branch on the actual maximal source data. The
preceding stage assumptions expose their concrete outputs and are still
to be proved by their source owners. Neither F.9, abelianness, an Hz choice,
H = G₁, the ambient centralizer bound nor a critical pair is assumed. -/
theorem contradiction_of_original_source_stages
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2, V₂⁆ ≠ ⊥)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (escape : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (component : ∃ K : Subgroup G,
      G₁ = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)) ∧
      (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      IsQuasisimple (Source.starImage G₁ K))
    (alternatives : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
      ∃ hU : IsElementaryAbelian 2 (Source.UH G₁ V₃), letI := hU
        TerminalRanks.MarkedModels G₁ ((L ⊔ (T : Subgroup G)) ⊓ G₁) V₃ V₁)
    (case_one : ∀ c : CriticalPair L (T : Subgroup G) G₁ V,
      (Source.DH (Source.UH G₁ V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH G₁ V₃ ∨
        Source.Dgamma (c.Ugamma V₃) (Source.UH G₁ V₃) V₁ = c.Ugamma V₃) →
      CaseAssembly.CaseOneModels T L G₁ V₃ V V₁)
    (point_models : ∀ c : CriticalPair L (T : Subgroup G) G₁ V,
      Source.DH (Source.UH G₁ V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH G₁ V₃ →
      Source.Dgamma (c.Ugamma V₃) (Source.UH G₁ V₃) V₁ < c.Ugamma V₃ →
      c.Aone V₁ ≤ Source.UH G₁ V₃ →
      Nonempty (Source.starImage G₁ (normalizer (c.Aone V₁ : Set G)) ≃* a6DuadStabilizer) ∨
        Nonempty (Source.starImage G₁ (normalizer (c.Aone V₁ : Set G)) ≃* duadStabilizer)) :
    False := by
  have hHz := original_six_point_normalizer_mem_Hz d hmax eL escape
  have hspan := original_six_full_span_abelian d hmax eL hm h1332 modules
  let dl := d.toLocalSetup hspan
  have hF9 := original_six_f9_of_source d hmax eL hm hHz
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer d eL
    (hypothesis1221_of_maximal_natural_six d hmax eL)
    (by rwa [← d.first_normalizer])
  have hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  obtain ⟨K, hgen, hK, hN, hqs⟩ := component
  rcases alternatives with hcover | ⟨hU, hmodels⟩
  · exact not_covered_local_quotient eL hcover
  · exact CaseAssembly.contradiction_of_source_cases dl hHz hF9 rfl
      hgen hK hN hqs hcentral hcomm hmodels case_one point_models

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OrdinaryAssembly
