module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpGeometry
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.SharpDegree

/-!
# The complete G₂ row in the marked two-copy branch

The original sharp constituent geometry makes the component equal its orbit.
Nonbinary G₂ is excluded by its module degree and actor rank. The binary
endpoint gives exactly the allowed native derived G₂ image with the required
orbit equality, and hence the original intrinsic local component lift.

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

/-- Every positive field exponent gives the actual marked image cases. -/
theorem imageCases_of_double_dimension_g2
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        commutator (Atlas.G2.Model k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2 ^ n) : s.ImageCases := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  by_cases hn1 : n = 1
  · have hk2 : Nat.card k = 2 := by simpa [hn1] using hcard
    let a := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv hk2)
    let f : commutator (Atlas.G2.Model k) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
      (a.subgroupMap _).trans (MulEquiv.subgroupCongr (by
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.surjective, commutator_def]))
    exact Or.inl ⟨he,Or.inl ⟨e.trans f⟩⟩
  · have hc := s.componentHypothesis_of_double_dimension hk hd
    dsimp only at hc
    rw [he] at hc
    exact (ChapterG.Section09.DefiningCharacteristic.G2Recognition.not_nonbinary_of_sharp_degree
      hc (by have hi := s.dimension_gt_two; omega) e (by omega) hcard).elim

/-- The actual local lift closes the derived G₂ model row. -/
theorem local_lift_of_double_dimension_g2
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        commutator (Atlas.G2.Model k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2 ^ n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_double_dimension_g2 hk hd e n hn hcard)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
