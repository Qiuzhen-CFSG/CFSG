module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches

/-!
# Independent representation inputs for K.1.2

Separate the degree bound from recognition in each of the two remaining
dimensions. The six-dimensional input identifies only the restricted module;
the natural normalizer calculation supplies its marked ambient extension.
The four-dimensional input also excludes a proper ambient extension of that
module. Both inputs retain the original action and an actual model intertwiner.

These are outstanding proof obligations, not a proved representation catalogue.
Their assembly is `sevenRecognition_of_dimension_branches` in `Seven.lean`.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463), invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Seven
open ChapterB.QuasisimpleSource

universe u v

/-- The source degree assertion, with irreducibility on the component retained.
In particular the reducible restriction of the symmetric eight-space is excluded. -/
def DegreeBound : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 7)) →
      Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 6

/-- Recognition in dimension four, including the absence of a proper extension.
The dimension hypothesis does not assert an equivalence with the model. -/
def FourSpace : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 7)) →
      Module.finrank (ZMod 2) V = 4 →
        L = ⊤ ∧ Nonempty
          (ActionEquiv (ρ.comp L.subtype) AlternatingSevenConjugatePair.Model.natural)

/-- Recognition of the restricted six-space. Its ambient extension is proved
separately, using the original linear coordinates and component marking. -/
def SixSpace : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 7)) →
      Module.finrank (ZMod 2) V = 6 →
        Nonempty (ActionEquiv (ρ.comp L.subtype) (alternatingNatural 7))

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Seven
