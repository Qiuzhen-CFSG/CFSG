module
public import CFSG.KnownSimple.SporadicCarriers
public import Theory.SpecificGroups.PrimeToFifteen.SporadicStructural
public import Theory.SpecificGroups.PrimeToFifteen.Leech
public import Theory.SpecificGroups.PrimeToFifteen.BabyMonster
public import Theory.SpecificGroups.PrimeToFifteen.Co1
public import Theory.SpecificGroups.PrimeToFifteen.Fischer

/-!
# Prime-to-fifteen solvability for all twenty-six sporadic carriers

Concrete cyclic words, subgroup orders, and existing local projections supply
a factor three or five for twenty-five carriers. The Baby Monster presentation
is solvable directly under the prime-to-three hypothesis. Transport follows
the literal carrier isomorphism, including the full finite guard inherited from
the section. No sporadic entry is omitted and no order certificate is assumed.

Source: the complete sporadic catalogue in GLS3 and Aschbacher–Smith §0.1;
the imported intrinsic modules record their individual constructions.
-/

public section
namespace CFSG.KnownSimple

theorem IsSporadicCarrier.solvable_of_coprime_three_five
    {G : Type*} [Group G] [Finite G] (h : IsSporadicCarrier G)
    (h3 : Nat.Coprime 3 (Nat.card G)) (h5 : Nat.Coprime 5 (Nat.card G)) :
    Group.IsSolvable G := by
  obtain ⟨name, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv] at h3 h5
  have hnot3 := Nat.prime_three.coprime_iff_not_dvd.mp h3
  have hnot5 := Nat.prime_five.coprime_iff_not_dvd.mp h5
  have hs : Group.IsSolvable name.Carrier := by
    cases name with
    | m11 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.m11).elim
    | m12 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.m12).elim
    | m22 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.m22).elim
    | m23 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.m23).elim
    | m24 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.m24).elim
    | j1 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.j1).elim
    | j2 => exact (hnot3 Theory.SpecificGroups.ThreeDivisibility.j2).elim
    | j3 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.j3).elim
    | j4 => exact (hnot3 Theory.SpecificGroups.ThreeDivisibility.j4).elim
    | hs => exact (hnot3 Theory.SpecificGroups.ThreeDivisibility.hs).elim
    | mcl => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.mcl).elim
    | he => exact (hnot3 Theory.SpecificGroups.ThreeDivisibility.held).elim
    | ru => exact (hnot3 Theory.SpecificGroups.ThreeDivisibility.rudvalis).elim
    | suz => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.suz).elim
    | onan => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.onan).elim
    | co1 => exact (hnot3 Sporadic.LeechRelated.Co1.three_dvd_card).elim
    | co2 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.co2).elim
    | co3 => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.co3).elim
    | fi22 => exact (hnot3 Sporadic.Fischer.Fi22.three_dvd_card).elim
    | fi23 => exact (hnot3 Sporadic.Fischer.Fi23.three_dvd_card).elim
    | fi24Prime => exact (hnot3 Sporadic.Fischer.Fi24Prime.three_dvd_card).elim
    | hn => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.haradaNorton).elim
    | ly => exact (hnot5 Theory.SpecificGroups.PrimeToFifteen.lyons).elim
    | th => exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.thompson).elim
    | babyMonster =>
      let : Finite BabyMonster.Carrier := Finite.of_equiv G e.toEquiv
      exact BabyMonster.solvable_of_coprime_three h3
    | monster =>
      let : Finite Sporadic.Monster.GriessGroup := Finite.of_equiv G e.toEquiv
      exact (hnot3 Theory.SpecificGroups.PrimeToFifteen.monster).elim
  let := hs
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
end CFSG.KnownSimple
