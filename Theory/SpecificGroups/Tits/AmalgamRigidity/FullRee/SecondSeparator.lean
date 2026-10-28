module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.FirstObstruction
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Reduction

/-!
# A full Ree second restriction outside the first restriction group

The short Sylow involution extends to the literal full second endpoint by the
verified Weyl relations and graph construction. A concrete conjugacy obstruction
excludes extension to the full first endpoint. Combining these gives a second
restriction outside the first restriction group without additional premises.
The application to twist factorization retains only the independent index bound,
whose producers are the Sylow automorphism upper bound and first restriction
count. The earlier generator-based conditional interfaces are preserved.

Source: Parrott (1972), p.683; Aschbacher–Smith F.1.11–12, printed pp.262–263.
The full Ree alternative is (I)(5) at q = 2. Both literal overlap inclusions
are retained; this helper does not by itself establish all of F.1.12.
-/

public section
noncomputable section
open ReeTwo
namespace Tits.AmalgamRigidity.FullRee.SecondSeparator
open Theory.GroupTheory RankTwoAmalgam

private theorem sylow_hom_ext {H : Type*} [Group H]
    {f g : SylowModel →* H}
    (hone : f SylowModel.rootOne = g SylowModel.rootOne)
    (hroot : ∀ i, f (SylowModel.root i) = g (SylowModel.root i)) : f = g := by
  apply SemidirectProduct.hom_ext
  · exact Core.hom_ext hroot
  · apply FiveFour.cyclicHom_ext
    have h := congrArg Inv.inv hone
    simpa only [SylowModel.rootOne, map_inv, inv_inv, MonoidHom.comp_apply] using h

/-- Generator compatibility proves extension along the literal right inclusion. -/
theorem separator_mem_secondRestrictions_of_generators
    (a : MulAut ExceptionalParabolics.FullRee.second)
    (hone : a (coordinateAmalgam.right SylowModel.rootOne) =
      coordinateAmalgam.right (separator SylowModel.rootOne))
    (hroot : ∀ i : CoreRoot, a (coordinateAmalgam.right (SylowModel.root i)) =
      coordinateAmalgam.right (separator (SylowModel.root i))) :
    separator ∈ secondRestrictions := by
  refine ⟨a, ?_⟩
  have he := sylow_hom_ext
    (f := a.toMonoidHom.comp coordinateAmalgam.right)
    (g := coordinateAmalgam.right.comp separator.toMonoidHom) hone hroot
  exact fun x => DFunLike.congr_fun he x

/-- Generator compatibility for a given extension supplies a separator. -/
theorem exists_separator_of_extension
    (a : MulAut ExceptionalParabolics.FullRee.second)
    (hone : a (coordinateAmalgam.right SylowModel.rootOne) =
      coordinateAmalgam.right (separator SylowModel.rootOne))
    (hroot : ∀ i : CoreRoot, a (coordinateAmalgam.right (SylowModel.root i)) =
      coordinateAmalgam.right (separator (SylowModel.root i))) :
    ∃ r : MulAut SylowModel, r ∈ secondRestrictions ∧ r ∉ firstRestrictions :=
  ⟨separator, separator_mem_secondRestrictions_of_generators a hone hroot,
    separator_not_mem_firstRestrictions⟩

/-- Application to the actual full Ree amalgam from an index bound and a given
compatible endpoint automorphism. -/
theorem factorsThrough_of_index_and_extension
    (hindex : firstRestrictions.index ≤ 2)
    (a : MulAut ExceptionalParabolics.FullRee.second)
    (hone : a (coordinateAmalgam.right SylowModel.rootOne) =
      coordinateAmalgam.right (separator SylowModel.rootOne))
    (hroot : ∀ i : CoreRoot, a (coordinateAmalgam.right (SylowModel.root i)) =
      coordinateAmalgam.right (separator (SylowModel.root i)))
    (d : MulAut ExceptionalParabolics.FullRee.B) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough_of_restriction_index hindex (exists_separator_of_extension a hone hroot) d

/-- The constructed full second-endpoint automorphism restricts to the short
involution along the literal marked inclusion. -/
theorem separator_mem_secondRestrictions : separator ∈ secondRestrictions :=
  separator_extends

/-- The full Ree second restriction group contains an automorphism outside
the first restriction group, with no additional hypotheses. -/
theorem exists_separator :
    ∃ r : MulAut SylowModel, r ∈ secondRestrictions ∧ r ∉ firstRestrictions :=
  ⟨separator, separator_mem_secondRestrictions, separator_not_mem_firstRestrictions⟩

/-- Every twist of the actual full Ree amalgam factors once the independent
first restriction index bound is supplied. The separating restriction premise
is discharged by the constructed endpoint automorphism and fusion obstruction. -/
theorem factorsThrough_of_index
    (hindex : firstRestrictions.index ≤ 2)
    (d : MulAut ExceptionalParabolics.FullRee.B) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough_of_restriction_index hindex exists_separator d

end Tits.AmalgamRigidity.FullRee.SecondSeparator
