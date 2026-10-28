module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.Complete
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.ContainedRows
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels

/-!
# Earlier component clauses at the original ordinary A₆ source

The actual plane movement gives the ambient centralizer bound and its
three-rank bound. The completed component sieve then places the original
point residual in every relative component. The contained 13.7.6 proofs
apply to each prescribed natural section and retain its quotient marking.
In degree three they give the full binary actor, which the original C₃
argument excludes. Degree four gives the covered local quotient and the
whole natural action. The alternating cases retain the unquotiented chief
count required by the earlier-component interface.

All subgroup parameters are fixed before the universal local-setup argument
of that interface. Thus its extra setup argument needs no new coordinate
choice. No component catalogue, containment, section recognition, or earlier
component clause is assumed. The original F.9 applicability and plane
noncentrality remain genuine preceding source hypotheses.

Source: Aschbacher–Smith, 13.5.4, 13.7.6 and 13.8.19–21,
printed pp.916,938–940,953–957.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}

/-- The exact earlier component interface on the original ordinary source,
with its containment and all natural-section conclusions constructed. -/
theorem original_earlier_inputs_of_ordinary_plane_noncentral
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9all : ∀ H ∈ Source.Hz (sourceOne L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hm : ⁅G₁.pCoreIn 2,V₂⁆ ≠ ⊥) :
    EarlierInputs T L V V₁ V₂ V₃ M G₁ := by
  let dn := localNaturalSetup d
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hcentral := Section05.AmbientSource.source_parabolic_centralizer dn eL hmax hm'
  have hrank := Section07.OrdinarySource.plane_centralizer_rank_of_noncentral dn eL hm'
  have hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥ := by
    intro he
    apply hm
    apply bot_unique
    rw [commutator_comm] at he
    exact (commutator_mono le_rfl d.plane_le_seed).trans_eq he
  have components :=
    ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.original_component_conclusions
      d hmax hF9all hcentral hcomm
  refine { centralizer := ?_, linear := ?_, alternating := ?_ }
  · intro _ H hH
    exact (OddReduction.source_kernel (hF9all H hH)).symm
  · intro _ H hH hnormal hmodule ρ hρ K hKH hK n hn eK hs
    have hLK := components.base_le hH hKH hK
    let c := BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n)
    have hs' : HasSectionModel H V₃ V₁ ρ K hKH
        (linearRepresentation n) (eK.trans c) := by
      obtain ⟨hst,e,he⟩ := hs
      exact ⟨hst,e,he⟩
    have hle := Section07.ModelExclusions.natural_dimension_le_four_of_one_le
      dn hH hKH hLK ρ hρ hrank (eK.trans c) hs'
    have hcases : n = 3 ∨ n = 4 := by omega
    rcases hcases with rfl | rfl
    · obtain ⟨_,_,eH,_,_,_⟩ :=
        Section07.ModelExclusions.projective_three_source_setup_of_one_le
          dn hH (hF9all H hH) hKH hK hLK ρ hρ eK hs
      exact (ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.original_binary_exclusion
        d hmax hF9all hcentral hcomm hH ⟨eH⟩).elim
    · obtain ⟨_,hcover,eH,eV,_,heV⟩ :=
        Section07.ModelExclusions.projective_four_source_case_of_one_le
          dn hmax hH (hF9all H hH) hcentral hKH hK hLK ρ hρ eK hs
      exact ⟨rfl,⟨eH,eV,heV⟩,hcover⟩
  · intro _ H hH hU hnormal hmodule ρ hρ K hKH hK n hn eK hs
    have hLK := components.base_le hH hKH hK
    obtain ⟨hgen,hprod,hcases⟩ := Section07.ModelExclusions.alternating_source_of_one_le
      dn hmax hH (hF9all H hH) hcentral hKH hK hLK ρ hρ hrank hn eK hs
    exact ⟨hgen,hLK,hprod,hcases⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
