module

public import ABG.ChapterII.Section2.SemidihedralCentralizerSylow
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# Odd involution-class size in semidihedral QD-groups

The Sylow subgroup of an involution centralizer has the same order as an
ambient Sylow subgroup. The two subgroup index formulas therefore show that
the centralizer index divides the odd ambient Sylow index. Equivalently,
the involution conjugacy class has odd cardinality.
Source: ABG II.1 Proposition 1 and II.2 Proposition 1.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

/-- Involutions have odd conjugacy-class size in a semidihedral QD-group. -/
public theorem IsQDGroup.odd_involution_class_card
    (hQD : IsQDGroup G) (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) : Odd (Nat.card (ConjClasses.mk x).carrier) := by
  obtain ⟨T, _, ⟨e⟩⟩ := hQD.exists_semidihedral_sylow_in_centralizer S hS x hx
  let C := Subgroup.centralizer ({x} : Set G)
  have hcard : Nat.card S = Nat.card T := Nat.card_congr e.toEquiv
  have heq : Nat.card S * (T.index * C.index) = Nat.card S * S.index := by
    rw [← Nat.mul_assoc, hcard, T.card_mul_index, C.card_mul_index,
      ← hcard, S.card_mul_index]
  have hind : T.index * C.index = S.index :=
    Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S)) heq
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
  have hodd : Odd S.index := by
    have hnot := S.not_dvd_index
    exact Nat.odd_iff.mpr (by omega : S.index % 2 = 1)
  exact hodd.of_dvd_nat ⟨T.index, by simpa [Nat.mul_comm] using hind.symm⟩

end ABG
