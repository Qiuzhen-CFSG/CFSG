module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Inputs

/-!
# Remaining representation obligations for the A₇ degree bound

The group-theoretic reduction in `Degree.Reduction` bounds the original binary
degree by eighteen. Two independent representation facts finish K.1.2: the
small-degree spectrum of A₇, and exclusion of degree fourteen for the actual
ambient cubic actor. Neither fact is asserted here, and neither is a premise
of the requested unconditional `Seven.DegreeBound`.

The spectrum input concerns only the component and needs no module recognition
in degrees four or six. The exclusion input keeps the original ambient cubic
ratio and irreducibility on the component, including all proper extensions.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463), citing
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section

open Subgroup Representation Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Seven.Degree

universe u v

/-- Only the faithful irreducible degrees in the established window are needed.
This is a proof obligation, not an assumed representation catalogue. -/
def SmallSpectrum : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V),
    Function.Injective τ → IsIrreducible τ → Module.finrank (ZMod 2) V ≤ 18 →
      Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 6 ∨
        Module.finrank (ZMod 2) V = 14

/-- The remaining degree fourteen must be excluded at the actual ambient
cubic bound two, without assuming a catalogue or a model intertwiner. -/
def NoFourteen : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 7)) →
      Module.finrank (ZMod 2) V ≠ 14

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Seven.Degree
