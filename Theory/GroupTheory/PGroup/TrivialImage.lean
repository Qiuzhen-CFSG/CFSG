module

public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# Trivial finite p-group images

A group with no normal subgroup of prime index `p` has only trivial
homomorphisms into finite `p`-groups. The source group need not be finite.

If the image were nontrivial, choose a maximal proper subgroup of the finite
image. Nilpotence makes it normal, and the maximal-index theorem for
`p`-groups gives index `p`. Pullback along the surjective range restriction
preserves normality and index, contradicting the source hypothesis.

This is the group-image reduction implicit in the characteristic-lift
argument in Alperin--Brauer--Gorenstein II.3, Proposition 2 (article p.22).
It is stated here independently of that application.
-/

namespace MonoidHom

/-- A group with no normal subgroup of index `p` maps trivially to every
finite `p`-group, for prime `p`. -/
public theorem eq_one_of_no_normal_index_prime
    {G P : Type*} [Group G] [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ p)
    (hP : IsPGroup p P) (f : G →* P) (g : G) : f g = 1 := by
  classical
  by_cases htriv : Subsingleton f.range
  · have := Subsingleton.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1
    exact congrArg Subtype.val this
  · let : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp htriv
    have hR : IsPGroup p f.range := hP.to_subgroup f.range
    obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (α := Subgroup f.range)
    let : Group.IsNilpotent f.range := hR.isNilpotent
    have hMn : M.Normal := Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent) hM
    let : M.Normal := hMn
    have hindex : (M.comap f.rangeRestrict).index = p := by
      rw [Subgroup.index_comap_of_surjective M f.rangeRestrict_surjective]
      exact hR.index_of_isCoatom M hM
    exact False.elim (hno (M.comap f.rangeRestrict) inferInstance hindex)

end MonoidHom
