module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.Cases

/-!
# The four positions in the dihedral quotient

`Position` spells out the subgroup geometry in source calculations (I)–(IV):
a complement to the center in the even four-group, an involution outside it,
the other elementary four-group, or the center. Its numerical consequence uses
the actual subgroup order. With a fixed even four-group the four positions are
mutually exclusive, giving the comparison needed once conjugation preserves
that group. The permutation and semidihedral calculations must establish these
positions and the behavior of the marked four-group before source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.25, printed pp.1133–1134 (PDF pp.1150–1151).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

variable {Q : Type*} [Group Q]

/-- The four source positions, in an actual group with a marked even four-group. -/
def Position (c : EightCase) (E A : Subgroup Q) : Prop :=
  match c with
  | .regular => Nat.card A = 2 ∧ Disjoint A (Subgroup.center Q) ∧ A ⊔ Subgroup.center Q = E
  | .transposition => Nat.card A = 2 ∧ ¬ A ≤ E
  | .disjoint => Nat.card A = 4 ∧ IsElementaryAbelian 2 A ∧ A ≠ E
  | .even => A = Subgroup.center Q

def quotientRank : EightCase → ℕ
  | .disjoint => 2
  | _ => 1

def kernelRank (c : EightCase) : ℕ := c.actorRank - quotientRank c

namespace Position

theorem card {c : EightCase} {E A : Subgroup Q} (h : Position c E A)
    (hZ : Nat.card (Subgroup.center Q) = 2) : Nat.card A = 2 ^ quotientRank c := by
  cases c with
  | regular => exact h.1
  | transposition => exact h.1
  | disjoint => exact h.1
  | even => rw [Position] at h; rw [h]; exact hZ

theorem rank {c : EightCase} {E A : Subgroup Q} (h : Position c E A)
    (hZ : Nat.card (Subgroup.center Q) = 2) :
    Representation.BinaryOffender.rank A = quotientRank c := by
  rw [Representation.BinaryOffender.rank, h.card hZ, Nat.log_pow Nat.one_lt_two]

private theorem regular_ne_center {E A : Subgroup Q} (h : Position .regular E A) :
    A ≠ Subgroup.center Q := by
  intro he
  have hd : Disjoint A A := he ▸ h.2.1
  have hb : A = ⊥ := disjoint_self.mp hd
  have hc := h.1
  rw [hb, Subgroup.card_bot] at hc
  omega

/-- Equal marked four-groups force the cases to agree. No case rank is assumed. -/
theorem unique {c d : EightCase} {E A : Subgroup Q}
    (hc : Position c E A) (hd : Position d E A)
    (hZ : Nat.card (Subgroup.center Q) = 2) (hZE : Subgroup.center Q ≤ E) : c = d := by
  have hcc := hc.card hZ
  have hdc := hd.card hZ
  have hrc : c = .regular → A ≠ Subgroup.center Q := by
    rintro rfl
    exact regular_ne_center hc
  have hrd : d = .regular → A ≠ Subgroup.center Q := by
    rintro rfl
    exact regular_ne_center hd
  cases c <;> cases d <;> try rfl
  all_goals simp only [quotientRank, pow_one, Nat.reducePow] at hcc hdc
  all_goals try omega
  all_goals simp only [Position] at hc hd
  · exact False.elim (hd.2 (hc.2.2 ▸ le_sup_left))
  · exact False.elim (hrc rfl hd)
  · exact False.elim (hc.2 (hd.2.2 ▸ le_sup_left))
  · exact False.elim (hc.2 (hd.symm ▸ hZE))
  · exact False.elim (hrd rfl hc)
  · exact False.elim (hd.2 (hc.symm ▸ hZE))

end Position

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
