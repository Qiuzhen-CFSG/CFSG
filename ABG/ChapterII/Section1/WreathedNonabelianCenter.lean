module
public import ABG.ChapterII.Section1.WreathedCentralizers

/-!
# Centers of nonabelian wreathed subgroups

ABG Chapter II §1 Lemma 2(xii), article p.10: the center of a nonabelian
subgroup lies in the center of the wreathed ambient group. The conclusion
maps the subgroup center into the ambient group through its actual subtype
homomorphism.

Every noncentral ambient element has abelian centralizer, as proved in
`WreathedCentralizers`. A noncentral element in the subgroup center would
therefore make all elements of that subgroup commute, contradicting the
nonabelian hypothesis.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

include P in
public theorem nonabelian_center_le (X : Subgroup S) (hX : ¬ IsMulCommutative X) :
    (Subgroup.center X).map X.subtype ≤ Subgroup.center S := by
  rintro a ⟨b,hb,rfl⟩
  by_contra ha
  apply hX
  apply IsMulCommutative.of_comm
  intro c d
  apply Subtype.ext
  have hbc : Commute (b : S) c := by
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hb c).symm)
  have hbd : Commute (b : S) d := by
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hb d).symm)
  exact (P.commute_of_commute_noncentral ha hbc hbd).eq
end ABG.Wreathed.Presentation
