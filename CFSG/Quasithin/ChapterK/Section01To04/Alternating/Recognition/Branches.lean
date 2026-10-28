module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Covers

/-!
# The remaining representation inputs for K.1

The cover reduction has four genuine outcomes. The ordinary covers require
module recognition with the permitted marked ambient extensions. For the
triple six cover only the binary degree remains to be established: the checked
hexacode embedding and normalizer calculations supply the representation once
that degree is six. The triple seven cover must be excluded at cubic ratio
two, including ambient extensions.

These are independent proof obligations, not an asserted representation
catalogue. `recognition_of_branches` combines their proofs with the actual
cover reduction; unconditional recognition still requires their producers.

Source: Aschbacher–Smith, K.1–K.1.3, printed pp.452–453, invoking
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs
open ChapterB.QuasisimpleSource GLS3.Chapter5.OddCentralCovers

universe u v

/-- The two A₆ modules form one quasiequivalence class; the only proper
ambient extension is the marked natural S₆ action. -/
def SixRecognition : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 6)) → Nonempty (NaturalAction ρ L 6)

/-- A₇ has its natural six-space, with at most the natural S₇ extension,
or the actual four-space, whose ambient actor equals the component. -/
def SevenRecognition : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 7)) →
      Nonempty (NaturalAction ρ L 7) ∨
        (L = ⊤ ∧ Nonempty
          (ActionEquiv (ρ.comp L.subtype) AlternatingSevenConjugatePair.Model.natural))

/-- The degree-six assertion needed before intrinsic hexacode recognition.
No action equivalence or extension hypothesis is included. -/
def TripleSixDegree : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* Atlas.Codes.HexEvenAutomorphisms) →
      Module.finrank (ZMod 2) V = 6

/-- Exclusion at the full source threshold, rather than only for FF-modules. -/
def TripleSevenExclusion : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* TripleSeven) → False

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs
