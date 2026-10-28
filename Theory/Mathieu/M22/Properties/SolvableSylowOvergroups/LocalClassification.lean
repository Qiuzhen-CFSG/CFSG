module

public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.NativeOrders
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.HexadConjugacy
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups.LocalClassification.PairPlacement

/-!
# Native parabolic classification under geometric placement in M₂₂

A subgroup containing an ambient Sylow two-subgroup, with a relatively normal
solvable seed whose order is divisible by three, has order 384 whenever it lies
in a pair or hexad stabilizer. Each branch is proved through its actual
permutation quotient with kernel of order sixteen. The index of the ambient
Sylow subgroup is then three, which also proves that the whole overgroup is
solvable. In the pair branch, the order-24 image on the five incident hexads
fixes one of them. Both branches therefore lie in a hexad stabilizer, where
the two maximal overgroups of a Sylow subgroup in the genuine A₆ quotient
lift to the two distinct native parabolic types. The conclusion retains an
actual M₂₂ conjugating element and subgroup equalities.

Source: the local subgroup step of Aschbacher–Smith 13.8.21(2), printed p.956
(PDF p.973). Geometric placement is an explicit hypothesis of this conditional
classification; its proof for arbitrary source inputs belongs to the assembly
owner.
-/

public section

open Subgroup MulAction
open scoped Pointwise

namespace Sporadic.Mathieu.M22SolvableSylow.LocalClassification

/-- The order consequence of either allowed geometric placement. -/
theorem order_of_geometric_placement (X D : Subgroup M22) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X)
    (hplace : (∃ B ∈ m22Blocks, X ≤ stabilizer M22 B) ∨
      (∃ S : Finset (Fin 22), S.card = 2 ∧ X ≤ stabilizer M22 S)) :
    Nat.card X = 384 := by
  rcases hplace with ⟨B, hB, hXB⟩ | ⟨S, hS, hXS⟩
  · exact hexad_order hB X D hXB hDX hN hsol h3 hU
  · exact pair_order hS X D hXS hDX hN hsol h3 hU

/-- Under either placement the whole Sylow overgroup is solvable. -/
theorem solvable_of_geometric_placement (X D : Subgroup M22) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X)
    (hplace : (∃ B ∈ m22Blocks, X ≤ stabilizer M22 B) ∨
      (∃ S : Finset (Fin 22), S.card = 2 ∧ X ≤ stabilizer M22 S)) :
    Group.IsSolvable X :=
  solvable_of_card_384 X (order_of_geometric_placement X D hDX hN hsol h3 hU hplace) hU

/-- Either permitted geometric placement yields an actual invariant hexad. -/
theorem hexad_of_geometric_placement (X D : Subgroup M22) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X)
    (hplace : (∃ B ∈ m22Blocks, X ≤ stabilizer M22 B) ∨
      (∃ S : Finset (Fin 22), S.card = 2 ∧ X ≤ stabilizer M22 S)) :
    ∃ B ∈ m22Blocks, X ≤ stabilizer M22 B := by
  rcases hplace with hB | ⟨S, hS, hXS⟩
  · exact hB
  · exact pair_hexad_of_order hS X hXS
      (pair_order hS X D hXS hDX hN hsol h3 hU) hU

/-- With the given geometric placement, every ambient Sylow overgroup having
a relatively normal solvable seed divisible by three is an actual conjugate
of one of the two distinct native hexad parabolics. -/
theorem conjugacy_of_geometric_placement (X D : Subgroup M22) (hDX : D ≤ X)
    (hN : (D.subgroupOf X).Normal) (hsol : Group.IsSolvable D) (h3 : 3 ∣ Nat.card D)
    (hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ X)
    (hplace : (∃ B ∈ m22Blocks, X ≤ stabilizer M22 B) ∨
      (∃ S : Finset (Fin 22), S.card = 2 ∧ X ≤ stabilizer M22 S)) :
    ∃ g : M22, X = pairHexad.map (MulAut.conj g).toMonoidHom ∨
      X = M22ValueBound.Concrete.second.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨B, hB, hXB⟩ := hexad_of_geometric_placement X D hDX hN hsol h3 hU hplace
  exact hexad_conjugacy hB X hXB
    (order_of_geometric_placement X D hDX hN hsol h3 hU hplace) hU

end Sporadic.Mathieu.M22SolvableSylow.LocalClassification
