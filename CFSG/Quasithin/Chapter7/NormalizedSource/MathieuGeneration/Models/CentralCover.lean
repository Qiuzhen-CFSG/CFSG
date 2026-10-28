module

public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Inputs
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Reducing the Cartan restriction to the four simple Mathieu models

For a perfect central cover, descent embeds its entire automorphism group
in the automorphism group of the simple quotient. An intermediate subgroup
containing all inner automorphisms descends to another such subgroup.
The complete Cartan witness, including the intrinsic Sylow, transfers
through the resulting isomorphism onto its image. Consequently only the
four concrete simple-model calculations are required; separate enumeration
of covers and their outer extensions is unnecessary.

Source application: the Mathieu rows of Aschbacher--Smith, Table 7.2.1
and 7.3.4, printed pp.698--699.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open ChapterE.Section06.FixedPointBounds
universe u v

/-- A Cartan bound for every inner-containing automorphism subgroup descends
from the actual simple quotient to a perfect central cover. -/
theorem cartan_restriction_of_centralQuotient
    {X : Type u} [Group X] [Finite X] [Group.IsPerfect X]
    {Y : Type v} [Group Y] [Finite Y] (e : (X ⧸ center X) ≃* Y)
    (hY : ∀ B : Subgroup (MulAut Y), MulAut.innerSubgroup Y ≤ B → nPrime B ≤ 2)
    (A : Subgroup (MulAut X)) (hA : MulAut.innerSubgroup X ≤ A) : nPrime A ≤ 2 := by
  let f := MulAut.centralQuotientAction e
  have hf : Function.Injective f := MulAut.centralQuotientAction_injective e
  have hinner : MulAut.innerSubgroup Y ≤ A.map f := by
    rintro b ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) z
    exact ⟨MulAut.conj x, hA ⟨x, rfl⟩, MulAut.centralQuotientAction_conj e x⟩
  have hmap : Function.Injective (f.subgroupMap A) := by
    intro a b hab
    exact Subtype.ext (hf (congrArg Subtype.val hab))
  obtain ⟨w⟩ := nPrime_spec (X := A)
  exact (w.map (f.subgroupMap A) (f.subgroupMap_surjective A)
    (hmap.comp w.cyclicGroup.subtype_injective)).le_nPrime.trans (hY _ hinner)

/-- Assembly from just the four model restrictions actually consumed by the
source. Covers and every intermediate outer extension are discharged here. -/
theorem mathieuCartanRestriction_of_models
    (h12 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M12),
      MulAut.innerSubgroup Sporadic.Mathieu.M12 ≤ A → nPrime A ≤ 2)
    (h22 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M22),
      MulAut.innerSubgroup Sporadic.Mathieu.M22 ≤ A → nPrime A ≤ 2)
    (h23 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M23),
      MulAut.innerSubgroup Sporadic.Mathieu.M23 ≤ A → nPrime A ≤ 2)
    (h24 : ∀ A : Subgroup (MulAut Sporadic.Mathieu.M24),
      MulAut.innerSubgroup Sporadic.Mathieu.M24 ≤ A → nPrime A ≤ 2) :
    MathieuCartanRestriction.{u} := by
  intro X _ _ hq hm A hA
  let := hq
  rcases hm with ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · exact cartan_restriction_of_centralQuotient e.some h12 A hA
  · exact cartan_restriction_of_centralQuotient e.some h22 A hA
  · exact cartan_restriction_of_centralQuotient e.some h23 A hA
  · exact cartan_restriction_of_centralQuotient e.some h24 A hA

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
