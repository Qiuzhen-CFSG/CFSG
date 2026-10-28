module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveBounds

/-!
# Self-duality transport for the exchanged sieve

A group equivalence and an intertwining linear equivalence transport an
actual self-dual representation to the same source H-action. This is the
form-preservation step in G.11.6, not a classification of group labels.

Source: Aschbacher--Smith G.11.6, printed p.366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups MonoidAlgebra
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace ExchangedAction
/-- Quasiequivalence transports an actual self-dual pairing along both the
group equivalence and the intertwining linear equivalence. -/
theorem selfDual_of_quasiequivalent
    {D E U V : Type*} [Group D] [Group E] [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D U} {σ : Representation (ZMod 2) E V}
    (hq : ChapterG.Section09.Quasiequivalent ρ σ) (j : σ.Equiv σ.dual) :
    Nonempty (ρ.Equiv ρ.dual) := by
  obtain ⟨e,f,hf⟩ := hq
  refine ⟨.mk ((f.trans j.toLinearEquiv).trans f.dualMap) ?_⟩
  intro g
  ext u w
  change j (f (ρ g u)) (f w) = j (f u) (f (ρ g⁻¹ w))
  have hj := LinearMap.congr_fun (LinearMap.congr_fun (j.toIntertwiningMap.isIntertwining' (e g)) (f u)) (f w)
  change j (σ (e g) (f u)) (f w) = j (f u) (σ (e g)⁻¹ (f w)) at hj
  rw [hf, hf, map_inv]
  exact hj

end ExchangedAction
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
