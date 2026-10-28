module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors

/-!
# The SL₄ endpoint-pair displacement estimate

The endpoint highest-vector relations identify the irreducible module with
the literal trace-zero adjoint quotient. The concrete actor calculation bounds
common fixed spaces of all nontrivial elementary cubic actors on that quotient.
The normalizer transport retains inner and outer actors, their ranks and
fixed codimensions. The model's faithfulness and irreducibility are inherited
from the original action through the comparison.

`endpoint_displacement` discharges both obligations, with no dimension cutoff,
absolute-irreducibility assumption or module-catalogue premise. Its application
to the multiple-support reduction leaves only the two adjacent estimates.
The conditional comparison APIs remain available separately. No assembly
umbrella is imported, so the final multiple-support assembly can use this leaf.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle author manuscript, Lemma 4.5 and Proposition 4.8 step 3A.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual module comparison and concrete adjoint actor calculation imply
exactly the published endpoint contract. Model faithfulness and irreducibility
are derived from the supplied source representation. -/
theorem endpoint_displacement_of_adjoint
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hrecognition : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 2} v →
      Nonempty (σ.Equiv Endpoint.adjoint))
    (hactors : Function.Injective Endpoint.adjoint → IsIrreducible Endpoint.adjoint →
      ∀ A : Subgroup (linearNormalizer Endpoint.adjoint),
      IsElementaryTwo A → IsCubic (normalizerRepresentation Endpoint.adjoint) A →
      rank A ≤ 4 → 2 * rank A < fixedCodim (normalizerRepresentation Endpoint.adjoint) A) :
    EndpointDisplacement σ := by
  intro v hv hJ A hA hc hr
  obtain ⟨e⟩ := hrecognition v hv hJ
  exact Endpoint.actor_gap_of_equiv e
    (hactors (Endpoint.injective_of_equiv e hf) (Endpoint.irreducible_of_equiv e hi))
    A hA hc hr

/-- Every faithful irreducible binary SL₄ endpoint module satisfies the strict
common-fixed-space bound for all nontrivial elementary cubic actors of rank at
most four in its full linear normalizer, including outer actors. -/
theorem endpoint_displacement
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ) :
    EndpointDisplacement σ :=
  endpoint_displacement_of_adjoint σ hf hi
    (Endpoint.recognition σ hi) Endpoint.adjoint_actor_gap

/-- Apply the endpoint comparison to the existing multiple-support consumer.
The two adjacent estimates remain with their separate source owner. -/
theorem multiple_support_displacement_of_adjoint
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hleft : InitialAdjacentDisplacement σ)
    (hright : InitialAdjacentDisplacement (diagramTwist σ))
    (hrecognition : ∀ v : V, v ≠ 0 → LocalHighestVector σ {0, 2} v →
      Nonempty (σ.Equiv Endpoint.adjoint))
    (hactors : Function.Injective Endpoint.adjoint → IsIrreducible Endpoint.adjoint →
      ∀ A : Subgroup (linearNormalizer Endpoint.adjoint),
      IsElementaryTwo A → IsCubic (normalizerRepresentation Endpoint.adjoint) A →
      rank A ≤ 4 → 2 * rank A < fixedCodim (normalizerRepresentation Endpoint.adjoint) A) :
    FourMultipleSupportDisplacement σ :=
  multiple_support_displacement_of_root_estimates σ hleft hright
    (endpoint_displacement_of_adjoint σ hf hi hrecognition hactors)

/-- The endpoint estimate discharges the separated-support branch of the
existing reduction. Only the independently owned adjacent estimates remain. -/
theorem multiple_support_displacement_of_adjacent_estimates
    (σ : Representation (ZMod 2) Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hleft : InitialAdjacentDisplacement σ)
    (hright : InitialAdjacentDisplacement (diagramTwist σ)) :
    FourMultipleSupportDisplacement σ :=
  multiple_support_displacement_of_root_estimates σ hleft hright
    (endpoint_displacement σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
