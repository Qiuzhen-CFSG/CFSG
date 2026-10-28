module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterAction
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaBounds
public import Stellmacher.Recognition.Parrott.ChosenCoreOmegaFromCenterEight

/-!
# The chosen omega filtration and universal displacement

For the supplied second elementary data, the center calculation and its S₃
normalizer quotient exclude index one or two for F in Ω₁(S). Hence Ω₁(S)
has order at least 128. The center-order calculation discharges the remaining
premise of the omega filtration theorem, giving index two in S,
|S| = 256, |Ω₁(S)| = 128, and |Ω₁(S):F| = 4. Every supplied element w
of the ambient derived two-core outside F normalizes S and has displacement
on Ω₁(S) contained in S′. No pointwise fixation of S′ is assumed.
All subgroups here are the actual supplied fixed join and chosen centralizer.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.676, from “As 3 divides” through [w, Ω₁(S)] ≤ S′.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The unconditional lower bounds from the chosen center and its S₃ quotient. -/
public theorem chosen_omega_lower_bounds [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G)) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let U := (omega₁ S (p := 2)).map S.subtype
    4 ≤ d.F.relIndex U ∧ 128 ≤ Nat.card (omega₁ S (p := 2)) := by
  exact chosen_omega_fixed_join_relIndex_ge_four hns hN d h hself hderived hconj
    (d.chosen_center_card_eight h hconj hderived)

/-- The source cardinalities conditional only on properness of the actual omega subgroup. -/
public theorem chosen_omega_geometry_of_proper [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G)) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V ≠ ⊤ → V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧ K.relIndex S = 4 ∧
      Nat.card (K ⊓ S : Subgroup G) = 64 := by
  exact chosen_omega_geometry_of_ne_top hns hN d h hself hderived hconj
    (d.chosen_center_card_eight h hconj hderived)

/-- The full chosen omega filtration under the original hypotheses. The
normalizer witness and displacement inclusion apply to every supplied w
in the ambient derived two-core outside the actual fixed join F. -/
public theorem chosen_omega_filtration [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G)) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧
      ∀ (w : G) (_hw : w ∈ E), w ∉ d.F →
        ∃ hwN : w ∈ normalizer (S : Set G),
          ∀ v ∈ V, v⁻¹ * S.normalizerMonoidHom ⟨w, hwN⟩ v ∈ commutator S := by
  exact chosen_omega_filtration_of_center_card_eight hns hN d h hself hderived hconj
    (d.chosen_center_card_eight h hconj hderived)

end Stellmacher.Recognition.ParrottSecondElementaryData
