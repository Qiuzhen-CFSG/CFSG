module

public import ABG.ChapterII.Section2.Defs
public import Theory.GroupTheory.SemidihedralFourSubgroup

/-!
# Four-groups through prescribed involutions in semidihedral QD-groups

The canonical four-group in the supplied semidihedral Sylow contains its
involutory generator. QD fusion conjugates that generator to any prescribed
involution, so the same conjugation transports the four-group.

Source: Alperin--Brauer--Gorenstein, II.1 Lemma 1 and Proposition 1.
-/

namespace ABG

/-- Every involution of a semidihedral QD-group lies in an elementary four-group. -/
public theorem IsQDGroup.exists_four_containing_involution
    {G : Type*} [Group G] [Finite G]
    (hQD : IsQDGroup G) (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (x : G) (hx : orderOf x = 2) :
    ∃ T : Subgroup G, IsElementaryAbelian 2 T ∧ Nat.card T = 4 ∧ x ∈ T := by
  obtain ⟨n, hn, _, a, b, ha, hb, hab, hgen⟩ := hS
  let E := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set S)
  obtain ⟨hEe, hE⟩ := Semidihedral.canonical_four hn a b ha hb hab hgen
  let : IsElementaryAbelian 2 E := hEe
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hbi⟩ := hcov b ((Subgroup.orderOf_coe b).trans hb)
  obtain ⟨j, hxj⟩ := hcov x hx
  have hbx : IsConj (b : G) x := hbi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hbx
  let f := (MulAut.conj g).toMonoidHom.comp (S : Subgroup G).subtype
  refine ⟨E.map f, IsElementaryAbelian.map f, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective
      ((MulAut.conj g).injective.comp (S : Subgroup G).subtype_injective)]
    exact hE
  · exact ⟨b, Subgroup.subset_closure (by simp), hg⟩

end ABG
