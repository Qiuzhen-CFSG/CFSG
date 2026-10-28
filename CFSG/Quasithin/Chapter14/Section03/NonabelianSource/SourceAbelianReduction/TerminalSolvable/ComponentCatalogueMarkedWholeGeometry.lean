module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedGeometry

/-!
# G.9 on the original whole marked action

Whole-constituent coordinates identify the selected action with the original
terminal representation. The existing one-or-two-component geometry supplies
G.9.3 on this very action, including its full known-simple cover and its
literal component orbit. The whole symplectic recognition uses this input.

Source: Aschbacher–Smith G.11.7 and 14.3.15, printed pp.366–368,994.
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
/-- When the selected constituent is the whole space, the original terminal
representation itself satisfies G.9.3. The actual component orbit and both
component actions are retained, without passing to a different ambient action. -/
theorem componentHypothesis_of_whole (hi : I = ⊤) :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
      (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  subst I
  refine {
    faithful := s.hypothesis.faithful
    elementary := inferInstance
    card_actor := ?_
    degree_le := s.actor_dimension.le
    quotient := ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩
    component := s.component
    noncentral := s.moved
    normal_H := componentOrbit_top_normal L
    irreducible := component_irreducible_of_top_isIrrPlus F.terminalRepresentation
      (componentOrbit L ⊤) s.selected.isIrrPlus s.fixedSpace_eq_bot
    components := ?_ }
  · exact (Nat.card_congr Additive.toMul).symm.trans (by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := Additive (F.terminalDot (F.X g)))))
  · rcases s.constituent_components with he | ⟨L₂,_,h₂,he,α,c,hc⟩
    · exact Or.inl he
    · refine Or.inr ⟨L₂,h₂,he,Or.inl ?_⟩
      let t : (⊤ : Submodule (ZMod 2) (Additive F.Uhat)) ≃ₗ[ZMod 2] _ :=
        Submodule.topEquiv
      refine ⟨α,t.symm.trans (c.trans t),?_⟩
      intro l w
      exact congrArg Subtype.val (hc l ⟨w,Submodule.mem_top⟩)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
