module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRankOne
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLowRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.FixedLine
public import Theory.SpecificGroups.SymplecticFour.Binary

/-!
# The complete symplectic row in the marked two-copy branch

The genuine sharp G.9 component geometry identifies the original component
with its normal orbit. Nonbinary Sp₄ is recognized on its actual natural
module, and its maximum-rank actor cannot have the original binary fixed
line. The binary derived endpoint is A₆. If the fixed space is larger, the
already checked low-displacement recognition gives the small image instead.
The resulting literal image cases feed the original intrinsic local lift.

Source: Aschbacher–Smith G.11.8 and 14.3.15, printed pp.368–369,994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
  {k : Type*} [Field k] [Finite k] [CharP k 2]
include s

/-- The original fixed marked line excludes every nonbinary symplectic row. -/
theorem not_double_dimension_nonbinary_symplectic_fixed_line
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        commutator (Matrix.symplecticGroup (Fin 2) k))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2 ^ n)
    (hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v}) : False := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have hc := s.componentHypothesis_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  dsimp only at hc
  rw [he] at hc
  apply ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.FixedLine.not_natural_sharp_fixed_line
    hc (by have hi := s.dimension_gt_two; omega) e hn hcard ⟨v,s.point_mem⟩
    (fun hz => s.hypothesis.point_ne_zero (congrArg Subtype.val hz))
  exact MarkedAction.fixedSpace_image_eq_line _ _ _ _ _ _ ⟨v,s.point_mem⟩ hfix

/-- All positive field exponents of the actual derived symplectic row give
the required original marked image cases. -/
theorem imageCases_of_double_dimension_symplectic
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        commutator (Matrix.symplecticGroup (Fin 2) k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2 ^ n) : s.ImageCases := by
  by_cases hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v}
  · by_cases hn1 : n = 1
    · have hk2 : Nat.card k = 2 := by simpa [hn1] using hcard
      exact Or.inr (Or.inl (Or.inr ⟨e.trans
        (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hk2)⟩))
    · exact (s.not_double_dimension_nonbinary_symplectic_fixed_line hk hd e n
        (by omega) hcard hfix).elim
  · exact s.imageCases_of_smallComponentImage
      (s.smallComponentImage_of_not_actorFaithful_of_fixedSpace_ne_point hk hfix)

/-- The actual component lift with its intrinsic two-core quotient closes
the symplectic row. -/
theorem local_lift_of_double_dimension_symplectic
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        commutator (Matrix.symplecticGroup (Fin 2) k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2 ^ n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_double_dimension_symplectic hk hd e n hn hcard)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
