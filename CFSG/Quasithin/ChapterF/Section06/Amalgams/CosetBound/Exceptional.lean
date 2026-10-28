module

public import CFSG.Quasithin.ChapterF.Section06.Amalgams.CosetBound
public import CFSG.Quasithin.ChapterF.Section06.Amalgams.LocalStructure

/-!
# The size bound for exceptional Goldschmidt amalgams

At a vertex with F* different from its two-core, the source local reduction
proves that its normal cubic residual centralizes its two-core. The faithful
degree-six coset action then bounds the common Sylow order by sixteen.
No condition on the opposite vertex's generalized Fitting subgroup is needed.

The last application retains the literal images and overlap in G/O₂(G).
This discharges the mixed-vertex size bound used by the bounded recognition
of F.6.5's exceptional amalgams. The remaining identifications and the six
F.1.12 cases are separate source obligations.

Source: Aschbacher--Smith, F.6.5, printed pp.304--305.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Failure of characteristic two at either chosen vertex bounds the common
Sylow order by the two-part of 6!. -/
theorem IsGoldschmidtTriple.intersection_card_dvd_sixteen_of_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    Nat.card (G₁ ⊓ G₂ : Subgroup G) ∣ 16 :=
  h.intersection_card_dvd_sixteen_of_core_centralizes_residual hcore
    (h.local_core_centralizes_residual hbad)

/-- In particular this proves the mixed-vertex size bound, without a
characteristic-two assumption on the opposite vertex. -/
theorem IsGoldschmidtTriple.intersection_card_le_sixteen_of_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁) :
    Nat.card (G₁ ⊓ G₂ : Subgroup G) ≤ 16 :=
  Nat.le_of_dvd (by decide) (h.intersection_card_dvd_sixteen_of_not_characteristic_two hcore hbad)

/-- The original overlap has small image in G/O₂(G) whenever the chosen
quotient vertex fails characteristic two. -/
theorem IsGoldschmidtTriple.quotient_intersection_card_le_sixteen_of_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂)
    (hbad :
      let A := G₁.map (QuotientGroup.mk' (pCore 2 G))
      generalizedFitting A ≠ pCore 2 A) :
    Nat.card ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G))) ≤ 16 := by
  rw [h.quotient_twoCore_intersection]
  exact h.quotient_twoCore.intersection_card_le_sixteen_of_not_characteristic_two
    h.quotient_twoCore_eq_bot hbad

end CFSG.Quasithin.ChapterF
