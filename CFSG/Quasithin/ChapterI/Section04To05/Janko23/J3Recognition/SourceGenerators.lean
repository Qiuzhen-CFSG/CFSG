module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.LocalStructure
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.PairOrders

/-!
# Order reductions for source J₃ generators

In the local setup of Aschbacher–Smith I.4.7(2), the centralizer of the
specified involution has order 1920. A nontrivial ATLAS generating pair
supplies an element of order 19. Consequently source subgroups supplying
the divisors 243 and 17 force `50232960 ∣ |G|`, and in particular the
lower bound required by the presentation comparison.

The divisors are left explicit: the Sylow-three analysis and the
`L₂(16)` subgroup in the Janko–Thompson–Higman–McKay source route must
provide them. The generating pair is also still an input. No source
recognition theorem or construction of that pair is asserted here.

Sources: Aschbacher–Smith, combined manuscript of 1 March 2004, I.4.7,
printed p. 418; Janko (1968); Higman–McKay (1969); ATLAS `J3G1-P1`.
-/

namespace CFSG.Quasithin.Janko23.J3Recognition

open Sporadic.Janko3.RecognitionPresentation

variable {G : Type*} [Group G] [Finite G]

/-- The local centralizer and three odd divisors give the full required divisor. -/
public theorem order_dvd_of_odd_local_divisors {z : G} (hlocal : HTypeAt z)
    (h3 : 243 ∣ Nat.card G) (h17 : 17 ∣ Nat.card G) (h19 : 19 ∣ Nat.card G) :
    50232960 ∣ Nat.card G := by
  have h2 : 1920 ∣ Nat.card G := by
    rw [← hlocal.centralizer_card]
    exact (involutionCentralizer z).card_subgroup_dvd_card
  have hd := Nat.lcm_dvd (Nat.lcm_dvd (Nat.lcm_dvd h2 h3) h17) h19
  norm_num at hd ⊢
  exact hd

/-- Application to the literal generating pair used by the recognition consumer. -/
public theorem order_dvd_of_generators_of_odd_local_divisors [Nontrivial G]
    (htype : J3Type G) (hgen : HasGenerators G)
    (h3 : 243 ∣ Nat.card G) (h17 : 17 ∣ Nat.card G) :
    50232960 ∣ Nat.card G := by
  obtain ⟨z, hz⟩ := htype.1
  exact order_dvd_of_odd_local_divisors hz h3 h17 hgen.nineteen_dvd_card

/-- The final comparison's order premise from two genuine odd-local divisors. -/
public theorem card_lower_bound_of_generators_of_odd_local_divisors [Nontrivial G]
    (htype : J3Type G) (hgen : HasGenerators G)
    (h3 : 243 ∣ Nat.card G) (h17 : 17 ∣ Nat.card G) :
    50232960 ≤ Nat.card G :=
  Nat.le_of_dvd Nat.card_pos
    (order_dvd_of_generators_of_odd_local_divisors htype hgen h3 h17)

/-- Apply the reduction to actual source subgroups: a subgroup of order 243
and the order-4080 linear subgroup in the `L₂(16):2` construction. Their
inclusions into the ambient group supply precisely the two remaining divisors. -/
public theorem card_lower_bound_of_generators_of_subgroups [Nontrivial G]
    (htype : J3Type G) (hgen : HasGenerators G)
    (P L : Subgroup G) (hP : Nat.card P = 243) (hL : Nat.card L = 4080) :
    50232960 ≤ Nat.card G := by
  apply card_lower_bound_of_generators_of_odd_local_divisors htype hgen
  · exact hP ▸ P.card_subgroup_dvd_card
  · apply (show 17 ∣ 4080 by decide).trans
    exact hL ▸ L.card_subgroup_dvd_card

/-- The same reduction expressed at the source's involution centralizer. -/
public theorem centralizer_index_lower_bound_of_odd_local_divisors {z : G}
    (hlocal : HTypeAt z) (h3 : 243 ∣ Nat.card G)
    (h17 : 17 ∣ Nat.card G) (h19 : 19 ∣ Nat.card G) :
    26163 ≤ (involutionCentralizer z).index := by
  have hd := Nat.le_of_dvd Nat.card_pos
    (order_dvd_of_odd_local_divisors hlocal h3 h17 h19)
  rw [← (involutionCentralizer z).index_mul_card, hlocal.centralizer_card] at hd
  omega

end CFSG.Quasithin.Janko23.J3Recognition
