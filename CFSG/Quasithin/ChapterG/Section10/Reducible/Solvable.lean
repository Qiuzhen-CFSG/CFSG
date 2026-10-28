module
public import CFSG.Quasithin.ChapterG.Section10.Reducible
public import Theory.Representation.BinaryPlaneSolvable
public import Theory.Representation.SubrepresentationLattice

/-!
# The reducible solvable branch of the original G.10 hypothesis

A minimal nonzero submodule is proper when the representation is reducible.
G.10.4 makes this a plane in dimension four; the faithful action embeds in
the actual solvable 2+2 parabolic. The final application preserves the literal
Chapter12 dotted actor, hat quotient, symplectic form and marked subgroups.

Source: Aschbacher--Smith G.10.5, printed p.359. The finer order-nine and
orthogonal recognition alternatives are not asserted here.
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

/-- The reducible branch is four-dimensional with solvable original actor. -/
theorem reducible_degree_and_solvable (hred : ¬ IsIrreducible ρ) :
    finrank (ZMod 2) V = 4 ∧ Group.IsSolvable G := by
  let : Nontrivial V := ⟨⟨v, 0, h.point_ne_zero⟩⟩
  obtain ⟨U, hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
  let : IsIrreducible U.toRepresentation := hU
  have hA := (Subrepresentation.irreducible_iff_isAtom U).mp hU
  have hU0 : U.toSubmodule ≠ ⊥ := by
    intro he
    exact hA.ne_bot (Subrepresentation.toSubmodule_injective he)
  have hUt : U.toSubmodule ≠ ⊤ := by
    intro he
    have he' : U = ⊤ := Subrepresentation.toSubmodule_injective he
    exact hred (isSimpleOrder_iff_isAtom_top.mpr (he' ▸ hA))
  obtain ⟨hplane, hfour⟩ := h.proper_irreducible_submodule_degree U hU0 hUt
  have hquot : finrank (ZMod 2) (V ⧸ U.toSubmodule) = 2 := by
    have he := U.toSubmodule.finrank_quotient_add_finrank
    omega
  exact ⟨hfour, ρ.isSolvable_of_faithful_plane_and_quotient_plane h.faithful U hplane hquot⟩

/-- A nonsolvable actor satisfying the original source hypothesis is irreducible. -/
theorem irreducible_of_not_solvable (hn : ¬ Group.IsSolvable G) : IsIrreducible ρ := by
  by_contra hred
  exact hn (h.reducible_degree_and_solvable hred).2

end CFSG.Quasithin.ChapterG.Section10.Hypothesis

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- G.10.5 on the original terminal action supplied by `terminal_g10_hypothesis`. -/
theorem terminal_reducible_degree_and_solvable (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hred : ¬ IsIrreducible F.terminalRepresentation) :
    finrank (ZMod 2) (Additive F.Uhat) = 4 ∧ Group.IsSolvable F.TerminalHdot :=
  h.reducible_degree_and_solvable hred

/-- The original nonsolvable dotted actor enters the irreducible G.11 branch. -/
theorem terminal_irreducible_of_not_solvable (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (h : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hn : ¬ Group.IsSolvable F.TerminalHdot) : IsIrreducible F.terminalRepresentation :=
  h.irreducible_of_not_solvable hn

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
