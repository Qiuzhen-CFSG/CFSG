module

public import Stellmacher.Recognition.FongWreathedCharacterData
public import Stellmacher.Recognition.FongWreathedBorel

/-!
# Fong's Borel construction from the original group hypotheses

The completed character calculation supplies the eight-character input and
the ambient order to the Borel construction. Thus the faithful doubly
transitive action of degree 28, with its regular subgroup of order 27 away
from the base point, requires no additional character or order hypothesis.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed p.75.
-/

namespace Stellmacher.Recognition.FongWreathed
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The actual degree-28 Borel action, with every character and order input
discharged under Fong's original hypotheses. -/
public theorem exists_borelAction
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G)
    (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ (P : ABG.Wreathed.Presentation S 2) (c : CharacterData P),
      Nonempty (BorelAction P c) ∧ Nat.card G = 6048 := by
  obtain ⟨P, ⟨c⟩, hG⟩ := exists_characterData_and_card_eq_6048 S hS x hx
  exact ⟨P, c, nonempty_borelAction P hS x hx hG c, hG⟩

end Stellmacher.Recognition.FongWreathed
