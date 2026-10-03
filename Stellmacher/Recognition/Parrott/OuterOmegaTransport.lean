module

public import Stellmacher.Recognition.Parrott.OuterOmegaOrder

/-!
# Transport inside an outer elementary subgroup of order thirty-two

Every outer point of an elementary subgroup X of order thirty-two in the
supplied Sylow has X = Ω₁(C_T(x)): inclusion follows from elementarity and
the reverse inclusion from the uniform omega order bound. Consequently a
Sylow element carrying an outer point back into X normalizes X.

The subgroup X also contains every involution in each derived-core coset
it meets outside the core. This is the lifting step for Parrott's quotient
conjugacy argument, on pp.674 and 676 of the 1972 characterization paper.
-/

open Subgroup
open scoped IsMulCommutative

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- Every outer point of elementary thirty-two recovers the same omega. -/
public theorem outer_elementary_eq_omega
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    let T : Subgroup G := d.sylow
    let xT : T := ⟨x, hXT hx⟩
    let Q := centralizer ({xT} : Set T)
    X = (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype) := by
  let T : Subgroup G := d.sylow
  let xT : T := ⟨x, hXT hx⟩
  let Q := centralizer ({xT} : Set T)
  let W := (omega₁ Q (p := 2)).map (T.subtype.comp Q.subtype)
  change X = W
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx)
    (fun heq => hxJ (heq ▸ one_mem _))
  have hle : X ≤ W := by
    intro a ha
    have hax : a * x = x * a := congrArg X.subtype
      (mul_comm (⟨a, ha⟩ : X) ⟨x, hx⟩)
    let aQ : Q := ⟨⟨a, hXT ha⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext hax)⟩
    have haQ : aQ ∈ omega₁ Q (p := 2) := subset_closure (by
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian a ha)
    exact mem_map_of_mem (T.subtype.comp Q.subtype) haQ
  apply eq_of_le_of_card_ge hle
  rcases d.outer_omega_order_alternatives h x (hXT hx) hxJ hx2 with hc | ⟨_, hc⟩
  · change Nat.card W = 16 at hc
    omega
  · change Nat.card W = 32 at hc
    omega

/-- A Sylow transporter between outer points of elementary thirty-two
normalizes that elementary subgroup. -/
public theorem outer_elementary_transporter_mem_normalizer
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)
    (t : G) (ht : t ∈ (d.sylow : Subgroup G))
    (htx : t * x * t⁻¹ ∈ X) : t ∈ normalizer (X : Set G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let K := J.map H.subtype
  have htK : t ∈ normalizer (K : Set G) := by
    apply le_normalizer_map H.subtype
    exact mem_map_of_mem H.subtype
      (show (⟨t, d.sylow_le_centralizer ht⟩ : H) ∈ normalizer (J : Set H) by
        rw [normalizer_eq_top]; trivial)
  have htxJ : t * x * t⁻¹ ∉ K := fun hh =>
    hxJ ((mem_normalizer_iff.mp htK x).mpr hh)
  have hW := d.outer_elementary_eq_omega h X hXT hX _ htx htxJ
  let T : Subgroup G := d.sylow
  let xT : T := ⟨t * x * t⁻¹, hXT htx⟩
  let Q := centralizer ({xT} : Set T)
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨a, ha, rfl⟩
    rw [hW]
    have hax : a * x = x * a := congrArg X.subtype
      (mul_comm (⟨a, ha⟩ : X) ⟨x, hx⟩)
    have hconj : (MulAut.conj t) a * (t * x * t⁻¹) =
        (t * x * t⁻¹) * (MulAut.conj t) a := by
      simpa only [map_mul, MulAut.conj_apply] using congrArg (MulAut.conj t) hax
    let aQ : Q := ⟨⟨(MulAut.conj t) a,
      T.mul_mem (T.mul_mem ht (hXT ha)) (T.inv_mem ht)⟩,
      mem_centralizer_singleton_iff.mpr (Subtype.ext hconj)⟩
    have haQ : aQ ∈ omega₁ Q (p := 2) := subset_closure (by
      apply Subtype.ext
      apply Subtype.ext
      change ((MulAut.conj t) a) ^ 2 = 1
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a ha, map_one])
    exact mem_map_of_mem (T.subtype.comp Q.subtype) haQ
  · exact (card_map_of_injective (MulAut.conj t).injective).symm.le

/-- The derived-core fixed subgroup of any outer point lies in X. -/
public theorem outer_elementary_derived_fixed_le
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    E ⊓ centralizer ({x} : Set G) ≤ X := by
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx)
    (fun heq => hxJ (heq ▸ one_mem _))
  have hle := (d.outer_omega_fixed_join h x (hXT hx) hxJ hx2).2.2
  rw [← d.outer_elementary_eq_omega h X hXT hX x hx hxJ] at hle
  exact le_sup_right.trans hle

/-- Every involution in a derived-core coset of an outer point of X lies in X. -/
public theorem outer_elementary_involution_coset_mem
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    ∀ v : G, v ^ 2 = 1 → x⁻¹ * v ∈ E → v ∈ X := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  change ∀ v : G, v ^ 2 = 1 → x⁻¹ * v ∈ E → v ∈ X
  intro v hv he
  let : IsElementaryAbelian 2 (commutator J) := (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have he2 : (x⁻¹ * v) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ he
  have hcomm : (x⁻¹ * v) * x = x * (x⁻¹ * v) := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx2)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hv)
    have hei : (x⁻¹ * v)⁻¹ = x⁻¹ * v :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using he2)
    have hvx : v * x = x * v := by simpa only [mul_inv_rev, inv_inv, hxi, hvi] using hei
    rw [hxi, mul_assoc, hvx, ← mul_assoc]
  have heX := d.outer_elementary_derived_fixed_le h X hXT hX x hx hxJ
    ⟨he, mem_centralizer_singleton_iff.mpr hcomm⟩
  simpa only [mul_inv_cancel_left] using X.mul_mem hx heX

/-- The derived core normalizes every elementary thirty-two in the supplied
Sylow which contains an outer point. -/
public theorem derived_le_outer_elementary_normalizer
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    E ≤ normalizer (X : Set G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let xH : H := ⟨x, d.sylow_le_centralizer (hXT hx)⟩
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx)
    (fun heq => hxJ (heq ▸ one_mem _))
  have hxHJ : xH ∉ J := fun hh => hxJ (mem_map_of_mem H.subtype hh)
  have hxH2 : orderOf xH = 2 := (Subgroup.orderOf_coe xH).symm.trans hx2
  let X₀ := zpowers x ⊔ (E ⊓ centralizer ({x} : Set G))
  have hEX₀ : E ≤ normalizer (X₀ : Set G) :=
    (parrott_outer_fixed_join_geometry z h xH hxH2 hxHJ).2.2.2.2.2.2.2.2.1
  have hX₀ : X₀ ≤ X := sup_le (zpowers_le.mpr hx)
    (d.outer_elementary_derived_fixed_le h X hXT hX x hx hxJ)
  have hET : E ≤ (d.sylow : Subgroup G) := by
    dsimp only [E]
    rw [d.sylow_map, ← map_map]
    exact map_mono ((map_subtype_le (commutator J)).trans
      (pCore_isPGroup.le_sylow_of_normal d.localSylow))
  change E ≤ normalizer (X : Set G)
  intro t ht
  apply d.outer_elementary_transporter_mem_normalizer h X hXT hX x hx hxJ t (hET ht)
  exact hX₀ ((mem_normalizer_iff.mp (hEX₀ ht) x).mp (mem_sup_left (mem_zpowers x)))

/-- Elementary thirty-two containing an outer point meets a nontrivial
derived-core coset inside the core. -/
public theorem outer_elementary_exists_core_not_derived
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (X : Subgroup G) [IsElementaryAbelian 2 X]
    (hXT : X ≤ (d.sylow : Subgroup G)) (hX : Nat.card X = 32)
    (x : G) (hx : x ∈ X)
    (hxJ : x ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    ∃ a : G, a ∈ X ∧ a ∈ J.map H.subtype ∧ a ∉ E := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let K := J.map H.subtype
  let E := (commutator J).map (H.subtype.comp J.subtype)
  let U := K.subgroupOf X
  let Z := E ⊓ centralizer ({x} : Set G)
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx)
    (fun heq => hxJ (heq ▸ one_mem _))
  have hUcard : Nat.card U = 16 := by
    have hc := d.outer_omega_core_card_of_card_thirtyTwo h x (hXT hx) hxJ hx2
    dsimp only at hc
    rw [← d.outer_elementary_eq_omega h X hXT hX x hx hxJ] at hc
    exact hc hX
  let xH : H := ⟨x, d.sylow_le_centralizer (hXT hx)⟩
  have hxHJ : xH ∉ J := fun hh => hxJ (mem_map_of_mem H.subtype hh)
  have hxH2 : orderOf xH = 2 := (Subgroup.orderOf_coe xH).symm.trans hx2
  have hZcard : Nat.card Z = 8 :=
    (parrott_outer_fixed_join_geometry z h xH hxH2 hxHJ).2.1
  change ∃ a : G, a ∈ X ∧ a ∈ K ∧ a ∉ E
  by_contra hnone
  push Not at hnone
  let i : U → Z := fun a => ⟨((a : X) : G),
    hnone _ (a : X).property a.property,
    mem_centralizer_singleton_iff.mpr (congrArg X.subtype
      (mul_comm (a : X) (⟨x, hx⟩ : X)))⟩
  have hi : Function.Injective i := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun c : Z => (c : G)) hab))
  have hle := Nat.card_le_card_of_injective i hi
  rw [hUcard, hZcard] at hle
  omega

end Stellmacher.Recognition.ParrottSecondElementaryData
