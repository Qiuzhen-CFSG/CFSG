module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeGeometry
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover
public import Theory.Representation.SmallSymplecticNormalThree

/-!
# Excluding the whole marked triple cover of A₆

The genuine central cover has binary degree six in the original G.9 window.
Its central cubic acts on the original nondegenerate alternating space.
The small symplectic normal-cubic theorem makes the component solvable,
contrary to its quasisimplicity. Both the actual central quotient and the
original invariant form are retained throughout.

Source: Aschbacher–Smith G.9.3(5), G.11.7 and 14.3.15,
printed pp.354,366–368,994.
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
/-- A whole triple-A₆ component cannot preserve the original symplectic form. -/
theorem not_whole_triple_alternating_six
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center L) = 3) : False := by
  have h9 := s.componentHypothesis_of_whole hi
  rw [hHL] at h9
  let : IsQuasisimple L := s.component.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  have hf := s.hypothesis.faithful.comp L.subtype_injective
  have hd := ChapterG.Section09.DefiningCharacteristic.AlternatingSixCover.small_degree_eq_six
    e hz (F.terminalRepresentation.comp L.subtype) hf h9.single_component_degree_bound
  have hsol := Representation.SmallSymplecticNormalThree.isSolvable_of_normal_cubic
    (F.terminalRepresentation.comp L.subtype) hf B s.hypothesis.alternating
    s.hypothesis.nondegenerate (fun l => s.hypothesis.preserves l) hd.le (center L) hz
  exact Group.IsPerfect.not_isSolvable L hsol

/-- The impossible genuine triple cover closes the original local-lift consumer. -/
theorem local_lift_of_whole_triple_alternating_six
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    (e : (L ⧸ center L) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center L) = 3) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_triple_alternating_six hi hHL e hz).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
