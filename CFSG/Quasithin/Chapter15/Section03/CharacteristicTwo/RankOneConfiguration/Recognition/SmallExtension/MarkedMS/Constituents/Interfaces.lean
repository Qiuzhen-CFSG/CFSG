module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Doubled

/-!
# The two remaining mathematical comparisons

SmallActionAlternative is an output specification for specializing the full
B.5.6 action list to the three small marked component models. Its single
branch retains the literal central quotient; its doubled branch identifies
the entire original module, not just a composition factor or quotient.
The order of the actual parabolic is the only group geometry needed by the
binary doubled-plane argument.

BinaryDoubledLine is the output of that separate linear geometry argument.
It specifies a natural copy containing the given plane, the actual embedding
and plane image, and the same stabilizer on the natural model. Neither
record asserts that its output exists. These boundaries allow the FF
comparison and the finite model calculation to proceed independently.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
B.5.6 and 15.3.31, printed pp.99–105 and 1132.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- The precise binary natural model used in the doubled branch. -/
noncomputable abbrev binaryNatural := linearNatural BinaryField.two 3

/-- Reduced full-module alternatives, before selecting or marking a constituent. -/
inductive SmallActionAlternative {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) (P : Subgroup L) : Prop
  | single (whole : IsIrrPlus ρ L ⊤)
  | double (coordinates : ActionEquiv (ρ.comp L.subtype) (repeated binaryNatural 2))
      (parabolic_card : Nat.card P = 24)

/-- A concrete model output: one natural copy contains the given moving plane.
Its line stabilizer uses the original model actor, without an independent twist. -/
structure BinaryDoubledLine
    (E : Submodule (ZMod 2) (Fin 2 → Fin 3 → ZMod 2))
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) where
  plane : Submodule (ZMod 2) (Fin 3 → ZMod 2)
  plane_card : Nat.card plane = 4
  embedding : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 2 → Fin 3 → ZMod 2)
  injective : Function.Injective embedding
  equivariant : ∀ g v, embedding (binaryNatural g v) =
    repeated binaryNatural 2 g (embedding v)
  image : plane.map embedding = E
  constituent : IsIrrPlus (repeated binaryNatural 2) ⊤ embedding.range
  stabilizer : subspaceStabilizer binaryNatural plane = P

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents
