module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Branches
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Coordinates

/-!
# Independent mathematical inputs to the A₆ branch

The source uses a degree bound, recognition of faithful irreducible binary
four-spaces up to an automorphism of A₆, and the linear normalizer of the
literal natural module. The latter two are intrinsic model questions and
do not depend on the cubic degree calculation. The extension argument and
the source application are proved separately from these explicit obligations.

Source: Aschbacher–Smith, K.1–K.1.1, printed p.452 (PDF p.463), citing
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
open ChapterB.QuasisimpleSource Representation.Hexacode.SixDimensional
universe u v

/-- The GM02 degree conclusion, retaining the original ambient cubic bound. -/
def Degree : Prop :=
  ∀ {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (K : GroupClass.{u}) (L : Subgroup G),
    Input ρ K L → (L ≃* alternatingGroup (Fin 6)) → Module.finrank (ZMod 2) V = 4

/-- Intrinsic four-space recognition includes the automorphism twist in its
actual group equivalence and the intertwiner on the original vector space. -/
def FourSpace : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V),
    Function.Injective σ → IsIrreducible σ → Module.finrank (ZMod 2) V = 4 →
      Nonempty (ActionEquiv σ (alternatingNatural 6))

/-- The literal symmetric natural action in the group of binary linear equivalences. -/
noncomputable def naturalLinearAction : Equiv.Perm (Fin 6) →*
    (BinaryPermutation.natural (Fin 6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6)) :=
  coordinateAction (BinaryPermutation.naturalRepresentation (Fin 6)) (LinearEquiv.refl _ _)

/-- The actual A₆ image, with the original alternating inclusion. -/
noncomputable def alternatingLinearImage :=
  (naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype).range

/-- The model normalizer calculation required by the ambient extension proof. -/
def Normalizer : Prop :=
  normalizer (alternatingLinearImage : Set _) = naturalLinearAction.range

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
