module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticHigherModel
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticReduction
public import Theory.Representation.SymmetricSixResidualActors
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The degree-four symplectic residual and its original actor

A symplectic basis and the concrete polar Sp4(2)-S6 equivalence identify the
full form stabilizer. Its literal embedded solvable residual is A6. Every
elementary two-subgroup of its automorphism group of order at least eight
is induced by that S6, so the original linear action gives explicit
intertwiners. Centerlessness removes the original central kernel. The source
actor has order eight and contains an automorphism that does not preserve
the constituent, giving the contradiction.

Source: Aschbacher--Smith G.10.15, printed p.363, with the original
14.3.12--15 small-actor equality, printed pp.993--994. No assertion of
invariance under every A6 automorphism is used.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual degree-four symplectic residual is centerless, and its large
elementary automorphism actors preserve the given linear module. -/
theorem symplecticResidual_four_model
    (B : LinearMap.BilinForm (ZMod 2) V) (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hd : Module.finrank (ZMod 2) V = 4) :
    let K := embeddedResidual (formStabilizer B)
    Subgroup.center K = ⊥ ∧ ∀ E : Subgroup (MulAut K),
      IsElementaryAbelian 2 E → 8 ≤ Nat.card E →
      ∀ α ∈ E, ∃ c : V ≃ₗ[ZMod 2] V,
        ∀ k : K, ∀ v : V, c (k.val v) = (α k).val (c v) := by
  obtain ⟨f⟩ := Matrix.PSp4Three.exists_isometry 2 B halt hnd hd
  let e : formStabilizer B ≃* Equiv.Perm (Fin 6) :=
    (formStabilizerEquivSp B f).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  exact Representation.SymmetricSixResidualActors.center_and_elementary_intertwiners
    (formStabilizer B) e

end CFSG.Quasithin.ChapterG.Section12
end

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

/-- The marked degree-four symplectic residual contradicts the original
order-eight elementary actor. -/
theorem false_of_symplectic_four
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnd : (B.restrict I).Nondegenerate)
    (heq : s.constituentLinearAction.range = ChapterG.Section12.embeddedResidual
      (ChapterG.Section12.formStabilizer (B.restrict I)))
    (hd : finrank (ZMod 2) I = 4) : False := by
  have hm := ChapterG.Section12.symplecticResidual_four_model
    (B.restrict I) (fun w => s.hypothesis.alternating w) hnd hd
  dsimp only at hm
  rw [← heq] at hm
  obtain ⟨E,hE,hcard,α,hα,hno⟩ := s.exists_constituent_actor_obstruction hproper hm.1
  exact hno (hm.2 E hE (by rw [hcard,hd]; decide) α hα)

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
