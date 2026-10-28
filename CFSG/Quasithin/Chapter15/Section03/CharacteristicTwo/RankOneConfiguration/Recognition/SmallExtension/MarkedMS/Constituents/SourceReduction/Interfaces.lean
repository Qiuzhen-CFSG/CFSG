module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.Interfaces
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives

/-!+# Small alternatives on the source commutator space

This output keeps the actual subspace [V,L] of the representation to which
B.5.6 is applied. Its doubled branch identifies that entire subspace with
two binary natural copies. In particular it says nothing about a splitting
of an arbitrary central quotient. The separate transfer module identifies
this space in U_I with the original component module U_L.

Existence is a remaining specialization of the complete B.5.1 conclusion,
after the other B.5.6 alternatives have been excluded at the actual actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1),
printed p.99, B.5.6, p.105, and 15.3.31, p.1132.
-/

@[expose] public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- Full moved-space alternatives, before transferring from U_I to U_L. -/
inductive MovedSmallAlternative {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop
  | single (whole : IsIrrPlus ρ L (moved ρ L))
  | double (space : Subrepresentation ρ) (space_eq : space.toSubmodule = moved ρ L)
      (coordinates : ActionEquiv (space.toRepresentation.comp L.subtype)
        (repeated binaryNatural 2))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
