module

public import Stellmacher.Recognition.Parrott.ChosenCoreCentralizer
public import Stellmacher.Recognition.Parrott.ChosenCoreCenterOrder
public import Stellmacher.Recognition.Parrott.ChosenCoreNormalizerQuotient

/-!
# The chosen center and its normalizer quotient

For the supplied second elementary subgroup data, put
`S = C_G(z) ∩ C_G(a)`. Under derived weak closure and the temporary
conjugacy of `z` with `a`, its center has order eight and `N_G(S)/S`
is isomorphic to the symmetric group on three points.

The local center calculation rules out orders four and sixteen using
characteristic commutator subgroups of `S`. The faithful normalizer action
on the resulting elementary center then gives the symmetric-three quotient.
This module discharges the center-order premise of that action theorem,
preserving the supplied fixed join and Sylow subgroup throughout.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and p.676, from “We claim that Z(S)” through the S₃ assertion.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {z : G}

/-- The chosen centralizer has center of order eight and normalizer quotient S₃,
under the original hypotheses and without an additional center-order premise. -/
public theorem chosen_center_card_eight_and_normalizer_quotient
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G)) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let N := normalizer (S : Set G)
    Nat.card (center S) = 8 ∧
      Nonempty ((N ⧸ S.subgroupOf N) ≃* Equiv.Perm (Fin 3)) := by
  have hcenter := d.chosen_center_card_eight h hconj hderived
  exact ⟨hcenter,
    chosen_centralizer_normalizer_quotient hns hN d h hself hderived hconj hcenter⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
