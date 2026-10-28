module

public import Theory.GroupTheory.Hall.TwoClosedTransport
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

/-!
# The literal derived symplectic Borel

Restrict the determinant characters to the intersection of the flag Borel
with the commutator subgroup. Their kernel still embeds in the unipotent
two-group and their target has odd order. This proves two-closure and the
abelian quotient without replacing the derived carrier by the full group,
including over the binary field.

Source application: Aschbacher--Smith, E.2.2(2b), printed pp.215--216,
and the Borel calculation in 4.4.13, pp.623--624.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F]

/-- The marked derived Borel has a normal Sylow two-subgroup and abelian odd quotient. -/
theorem derivedBorel_twoClosed {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    OddHall.TwoClosedAbelianQuotient
      ((borel (F := F)).subgroupOf (commutator (Sp F))) := by
  let B := (borel (F := F)).subgroupOf (commutator (Sp F))
  let i : B →* borel (F := F) :=
    ((commutator (Sp F)).subtype.comp B.subtype).codRestrict _ (fun b => b.property)
  let f := borelCharacters.comp i
  apply OddHall.twoClosedAbelianQuotient_of_characters f _
    (Nat.coprime_two_left.mp (torus_odd hF))
  let j : f.ker →* unipotent (F := F) :=
    ((commutator (Sp F)).subtype.comp (B.subtype.comp f.ker.subtype)).codRestrict _ (by
      intro b
      exact (borelCharacters_eq_one (i b.val)).mp b.property)
  exact (isPGroup_unipotent hF).of_injective j (by
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : unipotent (F := F) => z.val) hab))))
end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
