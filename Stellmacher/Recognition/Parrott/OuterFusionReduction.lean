module

public import Stellmacher.Recognition.Parrott.OuterCentralizerInSylow
public import Theory.GroupAction.ThirtyTwoEightSuborbit

/-!
# Reducing outer fusion to the actual omega geometry

Retain the supplied second elementary data d and T=d.sylow. For an outer
involution y in T, let X be the ambient image of Ω₁(C_T(y)). Core weak
closure excludes fusion to z if X has order sixteen, or if X is elementary
of order thirty-two with a half-sized core intersection and eight- or
sixteen-element N_T(X)-suborbits on its fused outer points.

In the large case, weak closure isolates z in that core intersection.
Normalizer movement and suborbit counting would give an orbit of length
nine. The binary hyperplane argument excludes that orbit: its other eight
points would be linearly independent in rank five. Thus the fusion
contradiction follows directly from the local geometry, without a separate
classification of automorphism groups or a two-core center calculation.

The geometry remains an explicit premise in this reduction. In particular,
this module does not infer it from the stronger core-involution premise
used in Lemma 3.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and the first paragraph of p.676. The hyperplane separation
argument gives an alternative to the final two-core argument on p.676.
-/

open Subgroup MulAction

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The original central involution belongs to the actual omega in the supplied T. -/
public theorem z_mem_outer_omega
    {G : Type*} [Group G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (y : G) (hyT : y ∈ (d.sylow : Subgroup G)) :
    let T : Subgroup G := d.sylow
    let yT : T := ⟨y, hyT⟩
    let Q := centralizer ({yT} : Set T)
    z ∈ (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype) := by
  let T : Subgroup G := d.sylow
  let yT : T := ⟨y, hyT⟩
  let Q := centralizer ({yT} : Set T)
  let zT : T := ⟨z, d.le_sylow d.z_mem_inf.2⟩
  have hzQ : zT ∈ Q := mem_centralizer_singleton_iff.mpr (Subtype.ext
    (mem_centralizer_singleton_iff.mp (d.sylow_le_centralizer hyT)).symm)
  let zQ : Q := ⟨zT, hzQ⟩
  have hzpow : zQ ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change z ^ 2 = 1
    exact h.involution ▸ pow_orderOf_eq_one z
  have hzomega : zQ ∈ omega₁ Q (p := 2) := subset_closure hzpow
  exact mem_map_of_mem (T.subtype.comp Q.subtype) hzomega

/-- The elementary order-thirty-two case follows from the half-sized core
intersection and the actual Sylow-normalizer suborbits. -/
public theorem outer_not_isConj_of_omega_thirtyTwo_geometry
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
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
    IsElementaryAbelian 2 X → Nat.card X = 32 → Nat.card U = 16 →
      (∀ x : X, IsConj z (x : G) → x ∉ U →
        Nat.card (orbit A x) = 8 ∨ Nat.card (orbit A x) = 16) →
      ¬ IsConj z y := by
  classical
  let H := centralizer ({z} : Set G)
  let T : Subgroup G := d.sylow
  let yT : T := ⟨y, hyT⟩
  let Q := centralizer ({yT} : Set T)
  let X := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
  let N := normalizer (X : Set G)
  let U := ((pCore 2 H).map H.subtype).subgroupOf X
  let A := T.subgroupOf N
  change IsElementaryAbelian 2 X → Nat.card X = 32 → Nat.card U = 16 →
    (∀ x : X, IsConj z (x : G) → x ∉ U →
      Nat.card (orbit A x) = 8 ∨ Nat.card (orbit A x) = 16) → ¬ IsConj z y
  intro hXelem hXcard hUcard hsuborbit hconj
  let : IsElementaryAbelian 2 X := hXelem
  let zX : X := ⟨z, d.z_mem_outer_omega h y hyT⟩
  have hzU : zX ∈ U := d.le_core d.z_mem_inf.2
  have hAz (a : A) : a • zX = zX := by
    apply Subtype.ext
    change ((a : N) : G) * z * ((a : N) : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp
      (d.sylow_le_centralizer a.property))
  have hconjOrbit (x : X) (hx : x ∈ orbit N zX) : IsConj z (x : G) := by
    obtain ⟨n, hn⟩ := hx
    exact isConj_iff.mpr ⟨(n : G), congrArg (fun a : X => (a : G)) hn⟩
  have hinter (x : X) (hx : x ∈ orbit N zX) (hxU : x ∈ U) : x = zX := by
    apply Subtype.ext
    exact hcore x hxU (hconjOrbit x hx)
  have hfix := smul_eq_of_binary_thirtyTwo_and_eight_or_sixteen_suborbits
    hXcard U hUcard zX hzU A hAz
    (fun x hx hxU => hsuborbit x (hconjOrbit x hx) hxU) hinter
  have hNH : N ≤ H := by
    intro n hn
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp
      (congrArg (fun a : X => (a : G)) (hfix ⟨n, hn⟩)))
  exact d.outer_omega_normalizer_not_le_centralizer h y hyT hyJ hy hconj hNH

/-- The exact local geometry sufficient to finish the outer-fusion exclusion,
with the original supplied Sylow and actual omega subgroup. -/
public theorem outer_not_isConj_of_omega_geometry
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (hN : IsNTwoGroup G)
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
          Nat.card (orbit A x) = 8 ∨ Nat.card (orbit A x) = 16)) →
      ¬ IsConj z y := by
  dsimp only
  intro hgeom hconj
  rcases hgeom with h16 | ⟨hXelem, h32, hU, hsub⟩
  · exact d.outer_omega_card_ne_sixteen_of_core_weakClosure hN h hcore
      y hyT hyJ hy hconj h16
  · exact d.outer_not_isConj_of_omega_thirtyTwo_geometry h hcore y hyT hyJ hy
      hXelem h32 hU hsub hconj

end Stellmacher.Recognition.ParrottSecondElementaryData
