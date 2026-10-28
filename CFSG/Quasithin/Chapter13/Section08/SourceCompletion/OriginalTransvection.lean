module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalEarlierInputs
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.OriginalNormalClosure

/-!
# Source 13.8.5 for the original ordinary A₆ configuration

The original plane movement supplies the seed centralizer bound and seed-core
movement. The actual local geometry excludes a solvable transvection normal
closure. The constructed component clauses and the proved known-simple G.6.4
then give the full source conclusion on the same H/O₂(H) and U_H/V₁.

No earlier-component family, universal local-input family, transvection
recognition or full-module conclusion is assumed. The natural setup, original
F.9 applicability and plane noncentrality retain their preceding source duties.
Source: Aschbacher--Smith, 13.8.5, printed pp.947--948.
-/

public section
open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The complete original ordinary transvection conclusion, with the actual
component and whole module constructed from the original source geometry. -/
theorem original_transvection_recognition_of_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ J ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      (∃ t : Source.Hstar H, IsTransvection ρ t) →
      (∃ K : Subgroup H, K.IsCComponent ∧
        (H : Set G) = (K.map H.subtype : Set G) * (T : Set G)) ∧
      FullAlternatives H L (sourceOne L T V₁) V₃ V₁
        (le_sup_left.trans hH.1.2) ρ := by
  let := d.uh_elementary hH
  let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
  dsimp only
  rintro ρ hρ ⟨t,ht⟩
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer
    (localNaturalSetup d) eL hmax hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  exact complete_conclusions_of_nonsolvable_closure T d
    (original_earlier_inputs_of_ordinary_plane_noncentral d eL hmax hF9all hm)
    ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.g64_source_knownSimple hH
    ρ hρ t ht (SolvableSource.original_normalClosure_not_solvable
      d hmax hH (hF9all H hH) hcentral hcomm ρ hρ t ht)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
