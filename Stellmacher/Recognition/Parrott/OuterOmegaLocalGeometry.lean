module

public import Stellmacher.Recognition.Parrott.OuterOmegaCoreIndex
public import Stellmacher.Recognition.Parrott.OuterOmegaSuborbits
public import Stellmacher.Recognition.Parrott.OuterFusionReduction

/-!
# Local geometry for outer fusion

Collect the core-index and orbit-cardinality results for the actual omega
subgroup in the supplied Sylow. These retain the original subgroup inclusions
used by the outer-fusion reduction.

Source: Parrott (1972), pp.674–676.
-/

open Subgroup MulAction

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The actual outer omega satisfies the complete local geometry needed by the
outer-fusion reduction.

The order alternative comes from the faithful centralizer quotient. In the
order-thirty-two branch, the core intersection has index two, and the
Sylow-normalizer suborbit calculation gives the required eight-or-sixteen
alternative on every fused outer point. -/
public theorem outer_omega_local_geometry
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) :
    let H := centralizer ({z} : Set G)
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    let N := normalizer (X : Set G)
    let U := ((pCore 2 H).map H.subtype).subgroupOf X
    let A := T.subgroupOf N
    Nat.card X = 16 ∨
      (IsElementaryAbelian 2 X ∧ Nat.card X = 32 ∧ Nat.card U = 16 ∧
        ∀ x : X, IsConj z (x : G) → x ∉ U →
          Nat.card (orbit A x) = 8 ∨ Nat.card (orbit A x) = 16) := by
  let T : Subgroup G := d.sylow
  let yT : T := ⟨y, hyT⟩
  let Q := centralizer ({yT} : Set T)
  let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
  let H := centralizer ({z} : Set G)
  let N := normalizer (X : Set G)
  let U := ((pCore 2 H).map H.subtype).subgroupOf X
  let A := T.subgroupOf N
  change Nat.card X = 16 ∨
    (IsElementaryAbelian 2 X ∧ Nat.card X = 32 ∧ Nat.card U = 16 ∧
      ∀ x : X, IsConj z (x : G) → x ∉ U →
        Nat.card (orbit A x) = 8 ∨ Nat.card (orbit A x) = 16)
  rcases d.outer_omega_order_alternatives h y hyT hyJ hy with h16 | ⟨hElem, h32⟩
  · exact Or.inl h16
  · have hU := d.outer_omega_core_card_of_card_thirtyTwo h y hyT hyJ hy h32
    refine Or.inr ⟨hElem, h32, hU, ?_⟩
    intro x _ hx
    exact d.outer_omega_suborbit_eq_eight_or_sixteen h y hyT hyJ hy hElem h32 x hx

end Stellmacher.Recognition.ParrottSecondElementaryData
