module

public import Stellmacher.Recognition.Parrott.OuterOmegaSixteenUnconditional
public import Stellmacher.Recognition.Parrott.OuterOmegaLocalGeometry

/-!
# Unrestricted outer fusion in Parrott's growth argument

Core weak closure excludes fusion to an outer involution. The actual outer
omega is either of order sixteen, excluded by the unconditional fixed-join
normalizer theorem, or elementary of order thirty-two, excluded by the already
proved hyperplane and orbit argument. The supplied Sylow subgroup is retained.

Source: Parrott (1972), pp.673–674 and the first paragraph of p.676.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- The actual order-sixteen exclusion follows from the unrestricted fixed-join
normalizer theorem. -/
public theorem parrott_outer_omega_card_ne_sixteen_of_core_weakClosure_unrestricted
    {G : Type*} [Group G] [Finite G]
     (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    (∀ t : G, t ∈ J.map H.subtype → IsConj z t → t = z) →
    ∀ y : H, orderOf y = 2 → y ∉ J → IsConj z (y : G) →
      let P := centralizer ({y} : Set H)
      let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
      Nat.card X ≠ 16 := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change (∀ t : G, t ∈ J.map H.subtype → IsConj z t → t = z) → _
  intro hcore y hy hyJ hconj
  dsimp only
  intro hcard
  let P := centralizer ({y} : Set H)
  let X := (omega₁ P (p := 2)).map (H.subtype.comp P.subtype)
  let X₀ := zpowers (y : G) ⊔ (E ⊓ centralizer ({(y : G)} : Set G))
  obtain ⟨_, hcard₀, hle⟩ := parrott_outer_fixed_join_data z h y hy hyJ
  have heq : X₀ = X := eq_of_le_of_card_ge hle (by rw [hcard, hcard₀])
  have hweak : ∀ t : G, t ∈ E → IsConj z t → t = z := by
    intro t ht htconj
    obtain ⟨a, _, rfl⟩ := ht
    exact hcore _ (mem_map_of_mem H.subtype a.property) htconj
  have hleN := parrott_outer_fixed_join_normalizer_le_centralizer_unconditional z h hweak y hy hyJ
  change normalizer (X₀ : Set G) ≤ H at hleN
  rw [heq] at hleN
  exact parrott_outer_omega_normalizer_not_le_centralizer z h y hy hyJ hconj hleN

end Stellmacher.Recognition

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- Outer fusion exclusion with no ambient N₂ premise. -/
public theorem outer_omega_card_ne_sixteen_of_core_weakClosure_unrestricted
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z)
    (hcore : ∀ t : G, t ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → IsConj z t → t = z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G))
    (hyJ : y ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (hy : orderOf y = 2) (hconj : IsConj z y) :
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
    Nat.card X ≠ 16 := by
  let H := centralizer ({z} : Set G)
  let yH : H := ⟨y, d.sylow_le_centralizer hyT⟩
  have hyH : orderOf yH = 2 := (Subgroup.orderOf_coe yH).symm.trans hy
  have hyHJ : yH ∉ pCore 2 H := fun hh => hyJ (mem_map_of_mem H.subtype hh)
  have hnot := parrott_outer_omega_card_ne_sixteen_of_core_weakClosure_unrestricted
    z h hcore yH hyH hyHJ hconj
  have heq := d.outer_centralizer_omega_eq h y hyT hyJ hy
  dsimp only at hnot heq ⊢
  rw [← heq]
  exact hnot

/-- Outer fusion exclusion with no ambient N₂ premise. -/
public theorem outer_not_isConj_of_omega_geometry_unrestricted
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z)
    (hcore : ∀ t : G, t ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → IsConj z t → t = z)
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
    (Nat.card X = 16 ∨
      (IsElementaryAbelian 2 X ∧ Nat.card X = 32 ∧ Nat.card U = 16 ∧
        ∀ x : X, IsConj z (x : G) → x ∉ U →
          Nat.card (MulAction.orbit A x) = 8 ∨ Nat.card (MulAction.orbit A x) = 16)) →
      ¬ IsConj z y := by
  dsimp only
  intro hgeom hconj
  rcases hgeom with h16 | ⟨hXelem, h32, hU, hsub⟩
  · exact d.outer_omega_card_ne_sixteen_of_core_weakClosure_unrestricted h hcore
      y hyT hyJ hy hconj h16
  · exact d.outer_not_isConj_of_omega_thirtyTwo_geometry h hcore y hyT hyJ hy
      hXelem h32 hU hsub hconj

/-- Outer fusion exclusion with no ambient N₂ premise. -/
public theorem outer_not_isConj_of_core_weakClosure_unrestricted
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z)
    (hcore : ∀ t : G, t ∈ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype → IsConj z t → t = z) :
    ∀ y : G, y ∈ (d.sylow : Subgroup G) →
      y ∉ (pCore 2 (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype →
      orderOf y = 2 → ¬ IsConj z y := by
  intro y hyT hyJ hy
  exact d.outer_not_isConj_of_omega_geometry_unrestricted h hcore y hyT hyJ hy
    (d.outer_omega_local_geometry h y hyT hyJ hy)

end Stellmacher.Recognition.ParrottSecondElementaryData
