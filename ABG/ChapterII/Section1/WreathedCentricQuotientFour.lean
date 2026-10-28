module
public import ABG.ChapterII.Section1.WreathedCentricQuotient
public import ABG.ChapterII.Section1.WreathedDihedralSubgroups
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.CyclicTwoAut

/-!
# The central quotient of an exceptional nonabelian centric subgroup

A nonabelian centric subgroup X of the chosen wreathed group has cyclic center
of order 2^n. If its automorphism group is not a two-group, its central quotient
is a Klein four group. This is the central reduction in ABG Chapter II §1
Lemma 3(i), article p.10.

Restriction to the characteristic center and the action on the central
quotient have a two-group kernel. The center's automorphism group is already
a two-group, so the quotient's automorphism group cannot be one. The actual
quotient embeds in the dihedral central quotient of the ambient group. Among
subgroups of that dihedral two-group only a Klein four subgroup can have an
automorphism group which is not a two-group. Transport gives the assertion.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

include P in
public theorem centric_quotient_isFourGroup (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X)
    (hna : ¬ IsMulCommutative X) (hAut : ¬ IsPGroup 2 (MulAut X)) :
    IsKleinFour (X ⧸ Subgroup.center X) := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  have hp : IsPGroup 2 X := (IsPGroup.of_card P.card).to_subgroup X
  have hcp : IsPGroup 2 (Subgroup.center X) := hp.to_subgroup _
  let : IsCyclic (Subgroup.center X) := (P.centric_center_structure X hc hna).1
  have hq : ¬ IsPGroup 2 (MulAut (X ⧸ Subgroup.center X)) := by
    intro h
    exact hAut (Subgroup.isPGroup_mulAut_of_characteristic_subgroup_quotient
      (Subgroup.center X) hcp hcp.mulAut_of_isCyclic_two h)
  obtain ⟨D, ⟨e⟩⟩ := P.centric_quotient_embedding X hc hna
  have hD : ¬ IsPGroup 2 (MulAut D) := by
    intro h
    exact hq (h.of_equiv (MulAut.congr e).symm)
  let hfour : IsKleinFour D := ABG.Wreathed.dihedral_subgroup_automorphisms D hD
  exact ⟨(Nat.card_congr e.toEquiv).trans hfour.card_four,
    (Monoid.exponent_eq_of_mulEquiv e).trans hfour.exponent_two⟩

end ABG.Wreathed.Presentation
