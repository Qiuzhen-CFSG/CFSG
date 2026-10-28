module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinaryBaumannSource

/-!
# Original ordinary A₆ selection for the component and field consumers

The maximal natural-six choice and the original earlier plane and catalogue
inputs make the full span abelian and give F.9. The original plane
noncentrality also supplies the seed centralizer and seed noncentrality.
Thus the selected component geometry has no extra closure, F.9, centralizer,
path, codimension or rank premise. Its representation is the given literal
conjugation action; elementary abelianness is derived before quantifying over
that representation.

The normal C-component and its supplement belong to 13.8.15–16, and the
no-transvection premise is the model alternative used by 13.8.18(4). The
assembly owner still supplies the original plane and catalogue inputs.
Source: Aschbacher–Smith 13.5.4,13.7.8,13.8.8(2),13.8.18(4), printed
pp.916,940–946,949,953, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.HigherFieldReduction
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open Chapter14.Section08.LieTypeBranch
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Original ordinary-source application of 13.8.8(2) and 13.8.18(4).
Every extra geometric hypothesis is discharged; the earlier plane/catalogue
and the actual component inputs keep their original producers. -/
theorem original_six_selected_witness
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Maximal (Counterexample T) L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅G₁.pCoreIn 2, V₂⁆ ≠ ⊥)
    (h1332 : Chapter13.Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hgen : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hK : (K.subgroupOf H).IsCComponent) (hN : (K.subgroupOf H).Normal)
    (hqs : IsQuasisimple (Source.starImage H K)) :
    let d₀ := d.toLocalSetup (original_six_full_span_abelian d hmax eL hm h1332 modules)
    letI := d₀.uh_elementary hH
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁)),
      SeedAction.IsConjugation H V₃ V₁ ρ →
      (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
      Nonempty (CriticalInputs.SelectedWitness L (T : Subgroup G) H V
        (sourceOne L T V₁) V₃ V₁ ρ) := by
  let d₀ := d.toLocalSetup (original_six_full_span_abelian d hmax eL hm h1332 modules)
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d₀.uh_elementary hH
  change ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁)),
    SeedAction.IsConjugation H V₃ V₁ ρ →
    (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
    Nonempty (CriticalInputs.SelectedWitness L (T : Subgroup G) H V
      (sourceOne L T V₁) V₃ V₁ ρ)
  intro ρ hρ hno
  have hm' : ⁅(normalizer (V₁ : Set G)).pCoreIn 2, V₂⁆ ≠ ⊥ := by
    rwa [← d.first_normalizer]
  have hc := Chapter13.Section05.AmbientSource.source_parabolic_centralizer d eL
    (hypothesis1221_of_maximal_natural_six d hmax eL) hm'
  have hn := Chapter13.Section05.AmbientSource.source_seed_noncentral_of_plane_noncentral d hm'
  have hF9 := original_six_f9_of_source d hmax eL hm hH
  exact exists_selected_witness d₀ hH hF9 hgen hK hN hqs hc hn ρ hρ hno

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource
