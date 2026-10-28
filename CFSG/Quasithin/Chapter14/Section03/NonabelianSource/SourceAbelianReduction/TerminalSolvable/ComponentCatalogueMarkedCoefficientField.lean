module

public import CFSG.Quasithin.ChapterG.Section10.CoefficientField
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeNatural

/-!
# Coefficient constraints in the original marked source

The original small-actor equality makes the full transvection space exactly
half-dimensional. Above binary degree four, the coefficient-field theorem for
G.10 therefore applies to the literal original actor and whole action. These
bounds use every source marking rather than an arbitrary irreducible action.

Source: Aschbacher--Smith, G.11.7 and 14.3.15.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- A coefficient field over which the original actor is linear is binary
when the original module has dimension at least six. -/
theorem coefficient_card_le_two_of_actor_linear
    {k : Type*} [Field k] [Algebra (ZMod 2) k] [Module k (Additive F.Uhat)]
    [IsScalarTower (ZMod 2) k (Additive F.Uhat)]
    (hd : 6 ≤ Module.finrank (ZMod 2) (Additive F.Uhat))
    (hlinear : ∀ (x : F.terminalDot (F.X g)) (c : k) w,
      F.terminalRepresentation x (c • w) = c • F.terminalRepresentation x w) :
    Nat.card k ≤ 2 := by
  apply s.hypothesis.coefficient_card_le_two hlinear
  have he := s.markedSpace_dimension
  omega

/-- A coefficient field for the original elementary semilinear actor has
order at most four, with the actual coefficient homomorphism retained. -/
theorem coefficient_card_le_four_of_actor_semilinear
    {k : Type*} [Field k] [Finite k] [Algebra (ZMod 2) k] [Module k (Additive F.Uhat)]
    [IsScalarTower (ZMod 2) k (Additive F.Uhat)]
    (hd : 6 ≤ Module.finrank (ZMod 2) (Additive F.Uhat))
    (φ : F.terminalDot (F.X g) →* (k ≃+* k))
    (hsemi : ∀ (x : F.terminalDot (F.X g)) (c : k) w,
      F.terminalRepresentation x (c • w) = φ x c • F.terminalRepresentation x w) :
    Nat.card k ≤ 4 := by
  apply s.hypothesis.coefficient_card_le_four_of_semilinear φ hsemi
  have he := s.markedSpace_dimension
  omega

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
