module

public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.Models
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The small odd PSL₂ endpoints of G.7.3(1)

For an odd field order at most nine, perfection excludes the three-element
field. The three remaining orders give actual isomorphisms to PSL₂(4),
PSL₃(2), and PSp₄(2)'. The last comparison composes PSL₂(9) ≃ A₆ with
the proved polar-action comparison for the commutator of PSp₄(2).

Source: Aschbacher--Smith, G.7.3(1), printed p.348. The preceding degree
bounds must still establish that the field order is at most nine.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section07.OddCharacteristic

open Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups

/-- The three genuine small-parameter endpoints. Quasisimplicity supplies
the weaker perfection hypothesis used here. -/
theorem psl2_small_odd_identification {G : Type*} [Group G] [Group.IsPerfect G]
    {q : ℕ} (ho : Odd q) (hq : q ≤ 9) (hmodel : ClassicalGroup.IsPSL G 2 q) :
    ClassicalGroup.IsPSL G 2 4 ∨ ClassicalGroup.IsPSL G 3 2 ∨
      Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  have hlarge : 1 < q := hcard ▸ (Finite.one_lt_card (α := F))
  have hthree : q ≠ 3 := by
    intro hq3
    exact not_perfect_of_card_three (hcard.trans hq3)
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
  have hcases : q = 5 ∨ q = 7 ∨ q = 9 := by
    obtain ⟨k, hk⟩ := ho
    omega
  rcases hcases with h | h | h
  · exact Or.inl ⟨GaloisField 2 2, inferInstance, inferInstance,
      by rw [GaloisField.card 2 2 (by decide)]; norm_num,
      ⟨e.trans (cardFiveEquivFour (hcard.trans h))⟩⟩
  · exact Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
      ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two (hcard.trans h))⟩⟩)
  · exact Or.inr (Or.inr ⟨(e.trans
      (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 (hcard.trans h))).trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩)

end CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
