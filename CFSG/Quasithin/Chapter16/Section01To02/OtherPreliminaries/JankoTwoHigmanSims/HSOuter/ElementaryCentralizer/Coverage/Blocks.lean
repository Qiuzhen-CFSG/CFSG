module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage.Pruning
import Mathlib.Tactic.FinCases

/-!
# Partitioning the finite coverage checks

Every index below 32t lies in exactly the block given by its quotient and
remainder on division by 32. This lets the larger permutation checks use
separate, bounded kernel computations without changing their exhaustive scope.
Source: the concrete certificate for Aschbacher–Smith 16.1.5(10), p.1172.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage

/-- Assemble a block number and its offset into the original finite index. -/
def blockIndex {t : Nat} (b : Fin t) (i : Fin 32) : Fin (32 * t) :=
  ⟨32 * b.val + i.val, by omega⟩

/-- Checking all offsets of all blocks checks every original index. -/
theorem allFin_blocks {t : Nat} (P : Fin (32 * t) → Prop)
    (h : ∀ b : Fin t, ∀ i : Fin 32, P (blockIndex b i)) : ∀ x, P x := by
  intro x
  have hd : x.val / 32 < t := by omega
  have hx := h ⟨x.val / 32, hd⟩ ⟨x.val % 32, Nat.mod_lt _ (by decide)⟩
  have he : blockIndex ⟨x.val / 32, hd⟩ ⟨x.val % 32, Nat.mod_lt _ (by decide)⟩ = x := by
    apply Fin.ext
    dsimp [blockIndex]
    omega
  rwa [he] at hx

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.ElementaryCentralizer.Coverage
