module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Binary
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.BinaryExtension.NineEscape
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Rank-one generation for every binary symplectic extension

The explicit binary polar equivalence and PSL₂(9) comparison give the
marked simple socle. The actual field-of-nine escape theorem supplies all
large-family E-members, while the simple-socle whole-group theorem handles
rank-one actors. Thus every Sylow two-extension is E-generated at one,
including the non-natural outer actions.

The projective endpoint takes the commutator after the central quotient,
as in the source catalogue. The two actual polar equivalences compare it
with the ordinary derived symplectic carrier.

Source: Aschbacher–Smith E.1.14(1),(6), printed p.214 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The full binary upper bound, with every outer-action case discharged. -/
theorem isEGenerated_binary_extension [IsSimpleGroup (generalizedFitting G)]
    (hF : Nat.card F = 2) (e : generalizedFitting G ≃* commutator (Sp F))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    IsEGenerated 1 G := by
  apply isEGenerated_binary_of_square_calculation hF e T hgen
  intro hm hC _ _
  exact ValuesOdd.PSLTwoGeneration.largeFamilyEscape_of_psl_nine _ hm hC

/-- The literal derived projective binary source model. -/
theorem isEGenerated_binary_projective [IsSimpleGroup (generalizedFitting G)]
    (e : generalizedFitting G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤) :
    IsEGenerated 1 G := by
  let e' : generalizedFitting G ≃* commutator (Sp (ZMod 2)) :=
    (e.trans Binary.projectiveDerivedEquivAlternatingSix).trans
      (Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)).symm
  exact isEGenerated_binary_extension (by simp : Nat.card (ZMod 2) = 2) e' T hgen

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour
