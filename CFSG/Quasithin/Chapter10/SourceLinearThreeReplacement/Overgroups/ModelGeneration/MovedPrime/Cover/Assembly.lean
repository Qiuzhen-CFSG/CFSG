module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.SeedLift
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.TopRow
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentOrbitAutomizer

/-!
# Assembly of the moved prime cover from two structural inputs

The original full Sylow meets the component normalizer in a Sylow subgroup.
Its image is Sylow in the literal normalizer/centralizer quotient, and
together with the faithful component image it generates that quotient.
The component image is self-centralizing and has the original PSL₂ model.

The model dichotomy therefore has the exact hypotheses it needs. Solvable
seeds lift by the component-orbit construction. In the minimal branch the
separate unique-maximal transport supplies ambient minimality, and the
whole group is a genuine prime row. Both structural inputs remain explicit
until their independent proofs are supplied; this is not the unconditional
source theorem.

Source: Aschbacher--Smith E.1.11--14, E.2.2 and 10.3.3,
printed pp.212--216 and 756--757.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The Sylow used in the model calculation is exactly the image of the
original Sylow intersection with the component normalizer. -/
theorem exists_component_automizer_sylow (hH : IsStronglyQuasithin H)
    (S : Sylow 2 H) {K : Subgroup H} (hK : IsComponent H K)
    (hgen : K ⊔ (S : Subgroup H) = ⊤) :
    ∃ R : Sylow 2 (NormalizerAction.Star K),
      (R : Subgroup (NormalizerAction.Star K)) = NormalizerAction.sylowImage K S ∧
      NormalizerAction.componentImage K ⊔ (R : Subgroup (NormalizerAction.Star K)) = ⊤ := by
  have ho := ChapterE.Structure.generating_component_orbit_eq_residual hH S hK hgen
  obtain ⟨R₀, hR₀⟩ := component_normalizer_sylow S hK ho
  let R := R₀.mapSurjective (f := NormalizerAction.quotient K)
    (QuotientGroup.mk'_surjective (NormalizerAction.C K))
  have hR : (R : Subgroup (NormalizerAction.Star K)) = NormalizerAction.sylowImage K S := by
    change (R₀ : Subgroup (normalizer (K : Set H))).map _ = _
    rw [hR₀]
    rfl
  refine ⟨R, hR, ?_⟩
  rw [hR]
  exact component_automizer_sylow_supplement S hK ho

/-- The selected cover in the original source configuration, conditional
only on the two independently owned structural inputs. -/
theorem coreFreeMovedPrimeCover_of_automizer_inputs
    (hmodels : PrimeAutomizerCoverDichotomy.{u})
    (hlift : MovedAutomizerMinimalLift.{u}) : CoreFreeMovedPrimeCover.{u} := by
  intro H _ _ hH hO S K hK hsK hn hgen p hp hodd hp7 hm
  let := hsK
  have hz := simple_component_center_eq_bot hK
  obtain ⟨R, hR, hsup⟩ := exists_component_automizer_sylow hH.stronglyQuasithin S hK hgen
  let e : K ≃* NormalizerAction.componentImage K :=
    NormalizerAction.componentEquivOfCenterEqBot K hz
  have hmodel : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 p :=
    hm.of_mulEquiv e.symm
  rcases hmodels (NormalizerAction.Star K) (NormalizerAction.componentImage K)
    inferInstance (NormalizerAction.centralizer_componentImage_eq_bot K hz)
    R hsup p hp hodd hp7 hmodel with hmin | hseeds
  · exact prime_cover_of_minimal S (hlift H hH hO S K hK hsK hn hgen R hR hmin)
      K hK hgen hp hodd hp7 hm
  · rw [hR] at hseeds
    exact cover_of_automizer_seeds S hK hz hgen hseeds

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
