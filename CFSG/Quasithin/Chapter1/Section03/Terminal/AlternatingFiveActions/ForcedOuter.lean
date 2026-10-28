module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter.InnerStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter.SquareNormalization

/-!
# The forced-outer-action proof for the terminal A₅ branch

The actual inner component-stabilizing actors in N_T(P) centralize P ∩ B.
This follows from the solvable Sylow-overgroup calculation in A₅, together
with the faithful quotient map on the odd intersection. The Frattini
argument then forces an outer actor: squares in N_T(P) normalize B because
three distinct conjugate A₅ components in H/O₂(H) would contradict the
three-rank bound supplied by strong quasithinness.

The final theorem discharges both action premises from the genuine local
source hypotheses, retaining the actual complement, component normalizer,
and intrinsic quotient. No restriction p = 3 is needed for this argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 1.3.9(1), printed p.514, PDF p.531.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {p : ℕ} {T X P H B : Subgroup G}

/-- The genuine source input forces outer action when square normalization is supplied.
The unconditional theorem below derives that assertion from the same source input. -/
theorem SourceInput.not_le_inner_of_squares (h : SourceInput 𝒦 p T X P H B)
    (hsquares : ∀ s ∈ T ⊓ normalizer P, s ^ 2 ∈ normalizer B) :
    ¬ T ⊓ normalizer B ≤ innerTwoQuotientNormalizer B :=
  not_le_inner_of_squares_of_inner_stabilizer h.toLocalInput h.swapped hsquares
    h.inner_stabilizer_centralizes

/-- Some element of the actual component normalizer in T acts outerly on B/O₂(B).
Both square normalization and inner-stabilizer centralization follow from the source input. -/
theorem SourceInput.not_le_inner (h : SourceInput 𝒦 p T X P H B) :
    ¬ T ⊓ normalizer B ≤ innerTwoQuotientNormalizer B :=
  h.not_le_inner_of_squares h.squares_normalize

/-- The forced-action assertion in the A₅ branch of 1.3.9(1), with the genuine
local source hypotheses explicit and no additional action premise. -/
theorem forced_outer_of_swapped_alternatingFive
    (hSQTK : IsSQTK 𝒦 H) (hchar : HasCharacteristicTwo H) (hH : H = B ⊔ T)
    (hT : IsSylowIn 2 T H) (hB : B ∈ cComponentsIn H) (hX : X ∈ Xi G T)
    (hXB : X ≤ componentOrbit B T) (h : XiEmbedding.LocalInput p T X P H)
    (hswap : XiEmbedding.SwappedFactors T P B)
    (hA : Nonempty (XiQuotient B ≃* alternatingGroup (Fin 5))) :
    ¬ T ⊓ normalizer B ≤ innerTwoQuotientNormalizer B :=
  SourceInput.not_le_inner
    { toLocalInput := h
      sqtk := hSQTK
      characteristic_two := hchar
      generated := hH
      sylow_two := hT
      component := hB
      xi := hX
      in_orbit := hXB
      swapped := hswap
      alternating_five := hA }

end CFSG.Quasithin.Chapter1.Terminal.ForcedOuter
