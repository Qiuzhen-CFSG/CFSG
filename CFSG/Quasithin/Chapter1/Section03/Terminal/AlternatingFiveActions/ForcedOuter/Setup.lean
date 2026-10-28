module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.QuotientTransport

/-!
# Source hypotheses for the forced outer action on an A₅ component

This record packages the local hypotheses of the swapped branch in the
last paragraph of Aschbacher–Smith 1.3.9(1), printed p.514. In particular,
T is Sylow in H, B is a relative C-component, the complement and its two
specified conjugate factors are the genuine local ones, and B/O₂(B) is
identified with the actual alternating group on five letters.

No actor, normalizer index, centralization, or action-table conclusion is
included. The action obligations must be proved from this setup by the
source-theorem assembly.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
open XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- Exactly the supplied local source data for the swapped A₅ branch. -/
structure SourceInput (𝒦 : GroupClass.{u}) (p : ℕ) (T X P H B : Subgroup G)
    extends LocalInput p T X P H where
  sqtk : IsSQTK 𝒦 H
  characteristic_two : HasCharacteristicTwo H
  generated : H = B ⊔ T
  sylow_two : IsSylowIn 2 T H
  component : B ∈ cComponentsIn H
  xi : X ∈ Xi G T
  in_orbit : X ≤ componentOrbit B T
  swapped : SwappedFactors T P B
  alternating_five : Nonempty (XiQuotient B ≃* alternatingGroup (Fin 5))

end CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
