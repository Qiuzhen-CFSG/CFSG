module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ModelAction
public import Theory.GroupTheory.DerivedAutomorphismAction
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Parity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits

/-!
# A proper component image gives the full J₂ automorphism action

The checked standard-pair orbits identify the concrete permutation extension
with all automorphisms of the ATLAS J₂ carrier. Adjoining the explicit outer
involution doubles the carrier order. Faithful inner conjugation therefore
shows that the outer quotient has order two, without requiring an ambient
order or simplicity computation.

A faithful action on a normal J₂ covers its full automorphism group whenever
that component is proper: its index is at least two, which bounds the outer
quotient order. The resulting equivalence preserves the original component
marking. Properness remains explicit here; the local sieve discharges it.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.42,
printed p.1138; GLS3 Table 5.3g. The imported ATLAS J2G1-p100B0 data and
kernel-checked orbit calculations retain their original attribution.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
variable {G : Type*} [Group G] {I L M Yplus S : Subgroup G}
variable [(L.subgroupOf I).Normal]

namespace JankoTwoExtension
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- The sharp outer bound follows from the complete checked automorphism realization. -/
theorem card_outer : Nat.card (MulAut.Outer Carrier) = 2 := by
  let a := extensionEquivAut_of_pair_calculations
    first_generator_conjugate second_generator_orbits
  have hAut : Nat.card (MulAut Carrier) = 2 * Nat.card Carrier := by
    rw [← Nat.card_congr a.toEquiv]
    exact Subgroup.card_sup_zpowers_of_normalizing_involution _ _
      (by simpa only [pow_two] using involution_mul_self)
      involution_not_mem_generated involution_mem_normalizer
  have hconj : Function.Injective (MulAut.conj : Carrier →* MulAut Carrier) := by
    intro x y h
    apply Subgroup.inclusion_injective (show generated ≤ extension from le_sup_left)
    apply extensionAction_injective
    change extensionAction (intoExtension x) = extensionAction (intoExtension y)
    simpa only [extensionAction_inner] using h
  have hinner : Nat.card (MulAut.innerSubgroup Carrier) = Nat.card Carrier :=
    (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hc := (MulAut.innerSubgroup Carrier).card_mul_index
  change Nat.card (MulAut.innerSubgroup Carrier) * Nat.card (MulAut.Outer Carrier) =
    Nat.card (MulAut Carrier) at hc
  rw [hinner, hAut, Nat.mul_comm 2] at hc
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hc

/-- The canonical action covers Aut(J₂) as soon as its component is proper. -/
noncomputable def identificationOfProper [Finite G]
    (d : ComponentSetup I L M Yplus S)
    (e : L ⧸ pCore 2 L ≃* Carrier)
    (hproper : componentImage I L L ≠ ⊤) : JankoTwoIdentification I L := by
  apply identificationOfSurjective d e
  have hbound : Nat.card (MulAut.Outer (componentImage I L L)) ≤
      (componentImage I L L).index := by
    rw [Nat.card_congr (MulAut.outerCongr (componentModel d e)).toEquiv, card_outer]
    exact (componentImage I L L).one_lt_index_of_ne_top hproper
  exact (MulAut.congr (componentModel d e)).surjective.comp
    (MulAut.conjNormal_bijective_of_outer_card_le_index _ (componentImage_faithful d) hbound).2

end JankoTwoExtension

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve
