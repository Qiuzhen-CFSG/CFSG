module

public import Theory.Representation.GoldschmidtONan.OddTerminal.AbelianKernel
public import Theory.Representation.GoldschmidtONan.OddTerminal.Endgame
public import Theory.Representation.GoldschmidtONan.OddTerminal.FixedLine
public import Mathlib.GroupTheory.Solvable

/-!
# The solvable terminal argument for Goldschmidt–O'Nan pairs

After the fixed space has been reduced to a line, a nontrivial abelian normal
subgroup supplies the Frobenius kernel. The last nontrivial derived subgroup
supplies such a subgroup when X is solvable. The Frobenius degree bound forces
dimension three, and the order and noncommutativity calculations complete all
four exceptional clauses.

Source: GLS, Number 2, Chapter C, Proposition 14.2, terminal argument after
Step 4 (`refs/KGroup/GLS2/ChapterC.tex`). The local transcription stops while
introducing the Frobenius kernel; the argument here reconstructs that step
and the remaining deductions.

The Step 4 orbital argument supplies the fixed line from the odd transitive
geometry. `Input.exceptionalCase_of_solvable` combines it with the terminal
argument, retaining solvability as an explicit assumption. The source implication
without that extra assumption is assembled in
`CFSG.Quasithin.GoldschmidtONan.OddTerminal` using the Odd Order Theorem.
This Theory module has only downward dependencies; promotion of the Odd Order
Theorem and its dependency closure into Theory is a separate task.
-/

public section

open scoped IsMulCommutative
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure

variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

private theorem exists_normal_abelian_of_solvable
    {G : Type*} [Group G] [Nontrivial G] [Group.IsSolvable G] :
    ∃ R : Subgroup G, R.Normal ∧ IsMulCommutative R ∧ R ≠ ⊥ := by
  classical
  have hex := Group.IsSolvable.solvable (G := G)
  let n := Nat.find hex
  have hn : derivedSeries G n = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro he
    rw [he, derivedSeries_zero] at hn
    exact top_ne_bot hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨derivedSeries G k, derivedSeries_normal G k, ?_, ?_⟩
  · apply Subgroup.commutator_self_eq_bot_iff.mp
    simpa only [hk, derivedSeries_succ] using hn
  · exact Nat.find_min hex (by omega)

/-- The terminal argument needs only an abelian normal subgroup, rather than
its minimality or an elementary abelian structure. -/
theorem Input.exceptionalCase_of_normal_abelian_of_fixed_finrank_one
    [Finite X] [Finite V] (h : Input ρ Y)
    (ht : NonzeroTransitive ρ) (ho : Odd (Nat.card X))
    (hf : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (R : Subgroup X) [R.Normal] [IsMulCommutative R] (hR : R ≠ ⊥) :
    ExceptionalCase ρ Y :=
  h.exceptionalCase_of_abelian_kernel ht ho hf R hR
    (h.fixedPointFree_on_normal_abelian ht hf R hR)

/-- The complete solvable terminal argument, with the Step 4 fixed-line
conclusion still explicit. The odd-order source theorem must discharge both
extra premises before using this as its exceptional branch. -/
theorem Input.exceptionalCase_of_solvable_of_fixed_finrank_one
    [Finite X] [Finite V] [Group.IsSolvable X] (h : Input ρ Y)
    (ht : NonzeroTransitive ρ) (ho : Odd (Nat.card X))
    (hf : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1) :
    ExceptionalCase ρ Y := by
  have : Nontrivial X := by
    have : Nontrivial Y := Y.nontrivial_iff_ne_bot.mpr h.nontrivial
    obtain ⟨y, _, hy⟩ := Y.exists_ne_one_of_nontrivial
    exact ⟨⟨y, 1, hy⟩⟩
  obtain ⟨R, hRn, hRa, hR⟩ := exists_normal_abelian_of_solvable (G := X)
  let : R.Normal := hRn
  let : IsMulCommutative R := hRa
  exact h.exceptionalCase_of_normal_abelian_of_fixed_finrank_one ht ho hf R hR

/-- The solvable odd transitive case, with the fixed-line conclusion supplied
by the Step 4 orbital argument. The source assembly must still supply solvability. -/
theorem Input.exceptionalCase_of_solvable
    [Finite X] [Finite V] [Group.IsSolvable X] (h : Input ρ Y)
    (hsub : SuborbitGeometry ρ Y) (hgeom : TransitiveGeometry ρ Y)
    (hodd : Odd (Nat.card X)) : ExceptionalCase ρ Y := by
  have hf := h.fixed_finrank_one_of_odd_transitiveGeometry hsub hgeom hodd
  exact h.exceptionalCase_of_solvable_of_fixed_finrank_one hgeom.1 hodd hf

end Representation.GoldschmidtONan
