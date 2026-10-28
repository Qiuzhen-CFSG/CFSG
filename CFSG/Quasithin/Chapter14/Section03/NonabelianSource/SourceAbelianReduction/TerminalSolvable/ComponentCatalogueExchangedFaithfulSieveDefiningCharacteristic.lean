module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveRankOne
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveSymplecticFour
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveG2
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieve
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelComplete

/-!
# Defining-characteristic exclusions on the original exchanged source

The original central-kernel construction produces the exact faithful
constituent record. The complete rank-one, symplectic-four and G₂ exclusions
therefore apply to that literal H image without an extra module-recognition
premise. Earlier Mathieu, linear and tensor/orthogonal exclusions are re-exported.

This is an enlarged model sieve. Exhaustive G.9 recognition and the
noncentral-kernel paired-A₅ branch are still required for ComponentImageCases
and the final local lift; no classification callback is asserted as proved.

Source: Aschbacher--Smith G.10.15 and G.11.6, pp.361–363,366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)
  {K : Type*} [Field K] [Finite K] [CharP K 2]


include s

/-- The original central-kernel branch excludes these entire defining-
characteristic families on its literal faithful constituent image. The
central-kernel construction supplies all properness and action hypotheses. -/
theorem image_not_rank_one_symplectic_four_or_g2 {n : ℕ} (hn : 0 < n)
    (hK : Nat.card K = 2 ^ n) :
    ¬ ((2 ≤ n ∧ Nonempty (s.faithful_source.image (componentOrbit L ⊤) ≃* SL(2,K))) ∨
      Nonempty (s.faithful_source.image (componentOrbit L ⊤) ≃*
        commutator (Matrix.symplecticGroup (Fin 2) K)) ∨
      Nonempty (s.faithful_source.image (componentOrbit L ⊤) ≃*
        commutator (Atlas.G2.Model K))) := by
  intro h
  rcases h with h | h | h
  · exact s.faithful_source.image_not_binary_rank_one h.1 hK (Classical.choice h.2)
  · exact s.faithful_source.image_not_symplectic_four hn hK (Classical.choice h)
  · exact s.faithful_source.image_not_g2 hn hK (Classical.choice h)

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
