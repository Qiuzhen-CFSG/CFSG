module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticReduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateAssembly
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# Excluding the concrete natural SL₂(4) constituent

The original small-actor equality gives an elementary automorphism subgroup
of order eight when the constituent has degree four. The actual SL₂(4)
isomorphism makes the image centerless, removing its central kernel, and
identifies its automorphism group with S₅. Its elementary two-subgroups
have order at most four, a contradiction. The equivariant module witness
supplies the exact dimension. The final consumer removes the natural-row
premise from the existing nondegenerate assembly.

Source: Aschbacher--Smith G.10.15, printed p.363, using the stronger
original 14.3.12--15 actor-rank equality, printed pp.993--994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)


include s

/-- The source actor is too large for the automorphism group of A₅. -/
theorem false_of_constituentImage_alternatingFive
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hd : 4 ≤ finrank (ZMod 2) I)
    (e : s.constituentLinearAction.range ≃* alternatingGroup (Fin 5)) : False := by
  have hc : center s.constituentLinearAction.range = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5))]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
  obtain ⟨E,hE,hcard,_⟩ := s.exists_constituent_actor_obstruction hproper hc
  let a := MulAut.congr e
  let D := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 E := hE
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map a.toMonoidHom
  have hb := Theory.SpecificGroups.Alternating.FiveExtensionAction.elementary_card_le_four D
  have he := Nat.card_congr (E.equivMapOfInjective a.toMonoidHom a.injective).toEquiv
  rw [← he, hcard] at hb
  have hl : 2 ^ 3 ≤ 2 ^ (finrank (ZMod 2) I - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The concrete natural SL₂(4) identification contradicts the source actor rank. -/
theorem false_of_naturalSL2Four
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (_hnd : (B.restrict I).Nondegenerate)
    (hmodel : ChapterG.Section12.NaturalSL2Four s.constituentLinearAction.range) : False := by
  obtain ⟨e,f,_⟩ := hmodel
  have hd : finrank (ZMod 2) I = 4 :=
    f.finrank_eq.trans Representation.SL2FourNatural.finrank_vector
  exact s.false_of_constituentImage_alternatingFive hproper hd.ge
    (e.trans Representation.SL2FourNatural.alternatingFiveEquiv)

/-- The actual nondegenerate assembly no longer needs a natural-row callback.
Recognition and the two independent classical rows retain their own premises. -/
theorem not_nondegenerate_of_classical_model_inputs
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hrecognition : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I))
    (hsymplectic : (B.restrict I).Nondegenerate →
      s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
        (ChapterG.Section12.formStabilizer (B.restrict I)) → False)
    (horthogonal : (B.restrict I).Nondegenerate →
      ∀ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I →
        s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
          q.isometrySubgroup → False) :
    ¬ (B.restrict I).Nondegenerate :=
  s.not_nondegenerate_of_model_inputs hproper hrecognition hsymplectic horthogonal
    (s.false_of_naturalSL2Four hproper)


end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
