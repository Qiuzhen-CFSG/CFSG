module
public import CFSG.Quasithin.ChapterG.Section10.Reducible.SourceFour
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Complement
public import CFSG.Quasithin.ChapterG.Section10.Reducible.LineExclusion
public import CFSG.Quasithin.ChapterG.Section10.TerminalSource
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.DoubleNaturalSplitting

/-!
# The degree conclusion in G.10.4 for the original group

Every nonzero proper irreducible G-submodule has dimension two, and the
original symplectic space has dimension four. In larger dimension the
constructed quadratic root four-group invokes the proved B.4.9 splitting
theorem, whose invariant complement contradicts the two common-axis actions.
The final application retains Chapter12's actual terminal quotient and action.
Source: Aschbacher--Smith G.10.4, printed pp.358--359, case H=G.
-/

public section
open Module Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The original H=G branch: every proper irreducible submodule is a plane
in the actual four-dimensional symplectic space. -/
theorem proper_irreducible_submodule_degree (U : Subrepresentation ρ)
    [IsIrreducible U.toRepresentation] (hU0 : U.toSubmodule ≠ ⊥)
    (hUt : U.toSubmodule ≠ ⊤) :
    finrank (ZMod 2) U.toSubmodule = 2 ∧ finrank (ZMod 2) V = 4 := by
  have hd0 : finrank (ZMod 2) U.toSubmodule ≠ 0 := fun he => hU0 (Submodule.finrank_eq_zero.mp he)
  have hd1 := h.finrank_ne_one_of_proper_submodule U hU0 hUt
  have hd2 : finrank (ZMod 2) U.toSubmodule = 2 := by
    by_contra hn
    have hn3 : 3 ≤ finrank (ZMod 2) U.toSubmodule := by omega
    obtain ⟨C,hC⟩ := ChapterB.QuasisimpleSource.SourceCompletion.doubleNatural_splits
      (h.largeDoubleNatural U hU0 hUt hn3) (h.largeDoubleNatural_source U hU0 hUt hn3)
    exact h.false_of_large_submodule_complement U C hU0 hUt hn3 hC
  exact ⟨hd2,h.degree_four_of_plane_submodule U hU0 hUt hd2⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The original Chapter12/14 consumer of G.10.4, after `terminal_g10_hypothesis`.
The acting group, central quotient, source space and smaller actor are literal. -/
theorem terminal_proper_irreducible_submodule_degree (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (U : Subrepresentation F.terminalRepresentation) [IsIrreducible U.toRepresentation]
    (hU0 : U.toSubmodule ≠ ⊥) (hUt : U.toSubmodule ≠ ⊤) :
    finrank (ZMod 2) U.toSubmodule = 2 ∧ finrank (ZMod 2) (Additive F.Uhat) = 4 :=
  h.proper_irreducible_submodule_degree U hU0 hUt

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
