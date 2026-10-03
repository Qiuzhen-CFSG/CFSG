module

public import Theory.GroupTheory.CentralCommutatorCorrectedLifts
public import Theory.GroupTheory.CentralCommutatorEightAssembly

/-!
# An elementary-eight supplement from a central commutator line

Let D be a normal elementary abelian subgroup of order eight in a group of
order thirty-two. If the derived subgroup lies in D and in the center, and
D intersects the center in order two, then there is another elementary
abelian subgroup of order eight generating the group together with D.
The full center has order two; this is a conclusion, not an assumption.

The conjugation action first identifies D as its own centralizer and places
the entire center in D. Independent quotient representatives can then be
corrected by elements of D to become commuting involutions. Adjoining the
center to these two lifts constructs the required elementary eight.

This source-neutral algebra supplies the second-eight step in Stellmacher
(8.6)(a2), Journal of Algebra 190 (1997), pp.41--42, without assuming an
extraspecial classification or an already-existing elementary pair.
-/

universe u

namespace Subgroup

public theorem exists_elementary_eight_supplement_of_central_commutator
    {G : Type u} [Group G] [Finite G] (D : Subgroup G) [D.Normal]
    (hD : IsElementaryAbelian 2 D) (hDcard : Nat.card D = 8)
    (hGcard : Nat.card G = 32)
    (hderived : _root_.commutator G ≤ D ⊓ Subgroup.center G)
    (hfixed : Nat.card (D ⊓ Subgroup.center G : Subgroup G) = 2) :
    ∃ C : Subgroup G, IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
      C ⊔ D = ⊤ ∧ Nat.card (Subgroup.center G) = 2 := by
  obtain ⟨hcentralizer, hcenter⟩ :=
    centralizer_eq_and_center_card_two_of_central_commutator
      D hD hDcard hGcard hderived hfixed
  obtain ⟨first, second, hfirst, hsecond, hcommute, hgen⟩ :=
    exists_commuting_involutions_mod_elementary_eight
      D hD hDcard hGcard hderived hcentralizer hcenter
  have hcenterD : center G ≤ D := by
    rw [← hcentralizer]
    exact center_le_centralizer _
  obtain ⟨C, hC, hCcard, hCD⟩ := exists_elementary_eight_of_commuting_involutions
    D hD hDcard hGcard hcenterD hcenter first second hfirst hsecond hcommute hgen
  exact ⟨C, hC, hCcard, hCD, hcenter⟩

end Subgroup

