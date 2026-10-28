module
public import Theory.GroupTheory.Amalgam.RestrictionProduct
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Geometry

/-!
# A two-count reduction for rigidity of the marked Tits amalgam

The existing two-generator exhaustion bounds the full Sylow automorphism
group by 8192. The existing fusion-elimination certificate bounds the
intersection of the endpoint restriction groups by 2048. We identify this
intersection with the previously defined compatible restrictions, using the
literal inclusions of the certified Sylow subgroup into the two parabolics.

Consequently, lower bounds of 4096 for each endpoint restriction group
suffice to remove every twist. The final theorem transports this calculation
from the certified Sylow carrier to the actual whole overlap, preserving
both inclusion maps. The two lower bounds remain explicit premises; neither
this module nor the earlier compatible-restriction bound proves them.

Source context: Fan, *Amalgams of prime index*, J. Algebra 98 (1986),
375--421; Aschbacher--Smith F.1.11--12, printed pp.262--263. The argument
here is a direct finite-group reduction, not an appeal to an unverified
form of Fan's theorem. It uses the corrected concrete Parrott parabolics,
including the first core of order 512 and quotient Sz(2).
-/

@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity
open Theory.GroupTheory RankTwoAmalgam ExceptionalParabolics
open SharpOuterBound SharpOuterBound.LocalImageBound

/-- Restrictions from the actual first parabolic, with the fixed inclusion. -/
abbrev firstRestrictions : Subgroup (MulAut S) := extensionSubgroup sylowAmalgam.left
/-- Restrictions from the actual second parabolic, with the fixed inclusion. -/
abbrev secondRestrictions : Subgroup (MulAut S) := extensionSubgroup sylowAmalgam.right

/-- The certified candidate-pair exhaustion bounds all overlap automorphisms. -/
theorem sylowAut_card_le : Nat.card (MulAut S) ≤ 8192 := by
  let code (f : MulAut S) : Fin 8192 := (generatorPair_exhaustive f).choose
  have hcode (f : MulAut S) : candidatePair (code f) = generatorPair f :=
    (generatorPair_exhaustive f).choose_spec
  have hinj : Function.Injective code := by
    intro f g h
    apply generatorPair_injective
    rw [← hcode f, ← hcode g, h]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective code hinj

/-- Simultaneous extension is the intersection of the two restriction groups. -/
def restrictionIntersectionEquiv :
    (firstRestrictions ⊓ secondRestrictions : Subgroup (MulAut S)) ≃
      CompatibleSylowRestrictions where
  toFun f := ⟨f.val, by
    obtain ⟨a, ha⟩ := f.property.1
    obtain ⟨b, hb⟩ := f.property.2
    exact ⟨a, b, fun s => congrArg Subtype.val (ha s),
      fun s => congrArg Subtype.val (hb s)⟩⟩
  invFun f := ⟨f.val, by
    obtain ⟨a, b, ha, hb⟩ := f.property
    exact ⟨⟨a, fun s => Subtype.ext (ha s)⟩, ⟨b, fun s => Subtype.ext (hb s)⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The existing fusion certificate bounds the intersection, not the product. -/
theorem restriction_intersection_card_le :
    Nat.card (firstRestrictions ⊓ secondRestrictions : Subgroup (MulAut S)) ≤ 2048 := by
  rw [Nat.card_congr restrictionIntersectionEquiv]
  exact compatibleSylowRestrictions_card_le

/-- The two outstanding lower bounds suffice for every twist on the Sylow carrier. -/
theorem sylow_factorsThrough_of_counts
    (hleft : 4096 ≤ Nat.card firstRestrictions)
    (hright : 4096 ≤ Nat.card secondRestrictions) (d : MulAut S) :
    FactorsThrough sylowAmalgam d :=
  RankTwoAmalgam.factorsThrough_of_counts sylowAmalgam 2048 (by decide)
    sylowAut_card_le hleft hright restriction_intersection_card_le d

/-- The same factorization on the actual overlap, with both original inclusion maps. -/
theorem factorsThrough_of_counts
    (hleft : 4096 ≤ Nat.card firstRestrictions)
    (hright : 4096 ≤ Nat.card secondRestrictions) (d : MulAut overlap) :
    FactorsThrough amalgam d := by
  obtain ⟨f, rfl⟩ := (MulAut.congr sylowAmalgamIso.middle).surjective d
  exact (sylowAmalgamIso.factorsThrough_iff f).mp
    (sylow_factorsThrough_of_counts hleft hright f)

end Tits.AmalgamRigidity
