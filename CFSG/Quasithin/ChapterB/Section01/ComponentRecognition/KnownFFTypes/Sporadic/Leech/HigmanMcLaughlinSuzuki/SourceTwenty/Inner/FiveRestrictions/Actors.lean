module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.Inputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup.RationalFusion
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup.RationalFusion

/-!
# Five-elements inverted by the two marked HS involutions

Conjugating the existing noncentral five-element x by a b⁻¹ gives an element
inverted by the literal core involution e0. Conjugating the central commutator z
by a b⁻³ a gives one inverted by the literal product involution ClassCoverage.t.
The latter cyclic subgroup is a conjugate of the center of the certified
order-125 subgroup, as required for the fixed-point-free module calculation.

Here a and b are the original degree-100 HS generators with Lean's left-action
convention. The identities are checked by the kernel on all 100 letters.
The two internal `import all` edges deliberately continue the existing packed
permutation certificates; their private implementation remains private.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, author preprint pp.16--17; ATLAS HSG1-p100B0, whose original data
and attribution are retained with the carrier. The reproducible witness search
is in the adjacent `source/` directory.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner.FiveActors
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
open Subgroup Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.FiveSubgroup
private def coreConjugator : Carrier := a * b⁻¹
private def productConjugator : Carrier := a * b⁻¹ ^ 3 * a

/-- A conjugate of the noncentral certified five-generator. -/
def coreFive : Carrier := coreConjugator * x * coreConjugator⁻¹
/-- A conjugate of the central certified five-generator. -/
def productFive : Carrier := productConjugator * z * productConjugator⁻¹

private theorem x_order : orderOf x = 5 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Equiv.ext
    apply allFin
    decide +kernel
  · intro he
    have hh := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 0) he
    have hn : (x : Equiv.Perm (Fin 100)) 0 ≠ 0 := by decide +kernel
    exact hn hh

private theorem z_order : orderOf z = 5 :=
  orderOf_eq_prime RationalFusion.z_pow_five RationalFusion.z_ne_one

/-- The core inverter has order five in the actual HS carrier. -/
theorem coreFive_order : orderOf coreFive = 5 := by
  exact ((MulAut.conj coreConjugator).orderOf_eq x).trans x_order

/-- The product inverter has order five in the actual HS carrier. -/
theorem productFive_order : orderOf productFive = 5 := by
  exact ((MulAut.conj productConjugator).orderOf_eq z).trans z_order

/-- The exact representative e0 inverts the selected five-element. -/
theorem core_inverts : EvenLocalCandidates.e0 * coreFive * EvenLocalCandidates.e0⁻¹ = coreFive⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- The exact representative ClassCoverage.t inverts the selected five-element. -/
theorem product_inverts : Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.t * productFive * Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.t⁻¹ = productFive⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem z_generates_center :
    (center subgroup).map subgroup.subtype = zpowers z := by
  let : IsExtraspecial 5 subgroup :=
    IsExtraspecial.of_noncommutative_card_prime_cube card_subgroup subgroup_not_commutative
  have hz : (⟨z, RationalFusion.z_mem_subgroup⟩ : subgroup) ∈ center subgroup := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    exact Subtype.ext (RationalFusion.z_mem_centralizer g g.property)
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map.mpr ⟨_, hz, rfl⟩)) ?_).symm
  change Nat.card ((center subgroup).map subgroup.subtype) ≤ Nat.card (zpowers z)
  rw [Nat.card_zpowers, z_order, Subgroup.card_map_of_injective subgroup.subtype_injective,
    IsExtraspecial.center_order_p 5 subgroup]

/-- The selected cyclic subgroup is conjugate to the literal five-center. -/
theorem productFive_conjugate_center :
    ∃ g : Carrier, (zpowers productFive) =
      ((center subgroup).map subgroup.subtype).map (MulAut.conj g).toMonoidHom := by
  refine ⟨productConjugator, ?_⟩
  rw [z_generates_center, MonoidHom.map_zpowers]
  rfl

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner.FiveActors
