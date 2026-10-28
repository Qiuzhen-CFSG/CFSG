module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Families
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Reduction
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.RankTwo
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.OrderTwo

/-!
# The elementary-core orbit argument in the A₆ shadow

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 2.5.24, printed p.568.

The shared interface constructs the actual inner cyclic four-subgroup and
the two inner Klein four-subgroups, proves their exhaustive classification,
and transports Frattini subgroups and elementary families under the source's
right conjugation. It also derives 2.5.13(2) from the earlier center data.

`HasNormalizerOrbit` is exactly the orbit of the genuine O₂(N_H(E)) required
by `Frattini.frattini_ne_of_elementary_orbits`. `Families` supplies the final
Frattini correction for the original x, both for the full largest-elementary
family and for a family whose relevant conjugate remains in a smaller group.

The Frattini decomposition and omega calculation reduce elementary S_C to
orders two and four and establish z = z_K. In order four, the two local cores
form the largest-elementary family of order 32. In order two, containment
of E₁ˣ in K S_C gives a family in (S ∩ K)S_C; otherwise fusion constructs an
actual centralizing involution and the largest-elementary family has order
16. Their S-conjugacy gives the required orbit for the original x.

`hasNormalizerOrbit_of_elementary` assembles these branches and discharges
the reduction and relative-centralizer inputs. Its sole additional input
is the permitted earlier action clause `ZConjugateActions` from 2.5.22(1).
The parent supplies that clause and the Sylow contradiction completing
2.5.24; no largest-local-pair or later involution premise is used here.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- All elementary-core branches of the source orbit argument, retaining the
original crossing element and only the earlier 2.5.22(1) action input. -/
theorem hasNormalizerOrbit_of_elementary (d : EarlierSetup κ G)
    (hact : ZConjugateActions d) (hEA : IsElementaryAbelian 2 d.SC) :
    HasNormalizerOrbit d := by
  rcases card_SC_eq_two_or_four d hEA with htwo | hfour
  · have hz : d.z = d.zK := (involutions_of_elementary_core d hEA).1
    apply OrderTwo.hasNormalizerOrbit_of_elementary_two d hEA htwo hz hact
    intro E hE hEfour
    let : IsKleinFour E := hEfour
    exact RankTwo.localCore_eq d E hE
  · exact RankTwo.hasNormalizerOrbit_of_elementary_four d hEA hfour

/-- The literal orbit premise of `Frattini.frattini_ne_of_elementary_orbits`:
the subgroup being conjugated is the genuine O₂(N_H(E)). -/
theorem elementary_normalizer_orbit (d : EarlierSetup κ G)
    (hact : ZConjugateActions d) (hEA : IsElementaryAbelian 2 d.SC) :
    ∃ E : Subgroup G, E ≤ d.S ⊓ d.K ∧ IsKleinFour E ∧
      ∃ s ∈ d.S,
        rightConjugate d.x (twoCore (d.H ⊓ normalizer (E : Set G))) =
          rightConjugate s (twoCore (d.H ⊓ normalizer (E : Set G))) :=
  hasNormalizerOrbit_of_elementary d hact hEA

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
