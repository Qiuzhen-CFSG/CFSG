module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import Theory.GroupTheory.NormalizedRootCentralizers

/-!
# Model transport for the literal normalized root center

An injective model map sends the full model Sylow subgroup to the actual
intersection Tᵥ* ∩ K*. It therefore sends its full center onto rootCenter.
The centralizer calculation then transports inside the specified Borel,
without asserting control of extra automorphisms in the ambient X*.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
variable {G : Type*} [Group G]

/-- The source root center transports from the whole model Sylow center,
not from an unconnected root-group label. -/
theorem rootCenter_eq_model_center {M : Type*} [Group M]
    (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (f : M →* XStar K) (hf : Function.Injective f) (U : Subgroup M)
    (hU : U.map f = NormalizerAction.sylowImage K (localT T v) ⊓
      NormalizerAction.componentImage K) :
    rootCenter T K = ((center U).map U.subtype).map f := by
  change (center (_ ⊓ _ : Subgroup (XStar K))).map _ = _
  rw [← hU, map_embeddedCenter U f hf]

/-- Transport through the actual Borel and Sylow maps. Model owners supply
the coordinate calculation on U; this theorem supplies its quotient use. -/
theorem root_centralizers_of_model {M : Type*} [Group M]
    (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (f : M →* XStar K) (hf : Function.Injective f) (U B₀ : Subgroup M)
    (hU : U.map f = NormalizerAction.sylowImage K (localT T v) ⊓
      NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hB : B ≤ B₀.map f)
    (hroot : ∀ r ∈ (center U).map U.subtype, r ≠ 1 →
      B₀ ⊓ centralizer ({r} : Set M) =
        B₀ ⊓ centralizer (((center U).map U.subtype : Subgroup M) : Set M))
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) :=
  Subgroup.NormalizedRootCentralizers.transport f hf B₀ _ B _ hB
    (rootCenter_eq_model_center T K f hf U hU) hroot r hr hne


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
