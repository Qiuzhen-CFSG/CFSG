module

public import Stellmacher.Recognition.Parrott.NormalizerCore
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreCenter
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmega
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeAction
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreThreeCenters

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCore`.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The complete local normalizer-core package for the supplied F and T.
The witnesses are compatible across the center, fixed-point, and cyclic
centralizer conclusions. No order or core-structure conclusion is assumed. -/
public theorem exists_normalizer_core_of_local_inputs (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let X := K.map N.subtype
    let W := U.map (N.subtype.comp K.subtype)
    let ZK := (center K).map (N.subtype.comp K.subtype)
    let ZU := (center U).map ((N.subtype.comp K.subtype).comp U.subtype)
    letI : U.Characteristic := omega₁_characteristic K
    let V := U.map K.subtype
    letI : V.Normal := ConjAct.normal_of_characteristic_of_normal
    Group.IsSolvable N ∧
    Nat.card N = 6144 ∧ Nat.card K = 1024 ∧
    Nonempty ((N ⧸ K) ≃* Equiv.Perm (Fin 3)) ∧
    Nat.card (center K) = 4 ∧ Nat.card ZK = 4 ∧
    Nat.card U = 256 ∧ Nat.card (center U) = 8 ∧ Nat.card ZU = 8 ∧
    d.F ≤ W ∧ W ≤ X ∧ X ≤ (d.sylow : Subgroup G) ∧
    ZK ≤ ZU ∧ ZU ≤ E ⊓ d.F ∧
    W = X ⊓ centralizer (ZU : Set G) ∧
    Nonempty ((N ⧸ V) ≃* Equiv.Perm (Fin 4)) ∧
    ∃ (Q : Sylow 3 N) (t v b : G),
      let A := (Q : Subgroup N).map N.subtype
      Nat.card Q = 3 ∧
      t ∈ E ⊓ d.F ∧ v ∈ E ⊓ d.F ∧
      orderOf t = 2 ∧ orderOf v = 2 ∧
      t ∉ zpowers z ∧ v ∉ ZK ∧
      ZK = zpowers z ⊔ zpowers t ∧
      ZU = (zpowers z ⊔ zpowers t) ⊔ zpowers v ∧
      X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) ∧
      (∃ q : Q, ((q : N) : G) * z * ((q : N) : G)⁻¹ = t) ∧
      v ∈ centralizer (A : Set G) ∧
      ZU ⊓ centralizer (A : Set G) = zpowers v ∧
      d.F ⊓ centralizer (A : Set G) = zpowers v ∧
      ¬ IsConj z v ∧
      b ∈ X ∧ orderOf b = 4 ∧ b ^ 2 = v ∧
      X ⊓ centralizer (A : Set G) = zpowers b ∧
      IsCyclic (X ⊓ centralizer (A : Set G) : Subgroup G) ∧
      Nat.card (X ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
  intro H J E N K U X W ZK ZU V
  obtain ⟨hNcard, hKcard, hS3, hZKcard⟩ := d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper
  obtain ⟨hUcard, hZUcard, hZUle, hWC⟩ :=
    d.normalizer_core_omega_structure_of_local_inputs h hlocal hproper
  obtain ⟨Q, t, v, b, ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hq, hvC,
      hZUfix, hFfix, hnc, hbX, hb4, hb2, hbC, hcyclic, hcard, hS4⟩ :=
    d.exists_normalizer_three_action_of_local_inputs h hlocal hproper
  have hi : Function.Injective (N.subtype.comp K.subtype) :=
    N.subtype_injective.comp K.subtype_injective
  have hZKambient : Nat.card ZK = 4 :=
    (card_map_of_injective hi).trans hZKcard
  have hZUambient : Nat.card ZU = 8 := by
    calc
      Nat.card ZU = Nat.card (center U) := card_map_of_injective
        (N.subtype_injective.comp (K.subtype_injective.comp U.subtype_injective))
      _ = 8 := hZUcard
  have hWX : W ≤ X := by
    change U.map (N.subtype.comp K.subtype) ≤ K.map N.subtype
    rw [← map_map]
    exact map_mono (map_subtype_le U)
  have htZ : t ∈ ZK := by
    change ZK = zpowers z ⊔ zpowers t at hZK
    rw [hZK]
    exact mem_sup_right (mem_zpowers t)
  have hXC := d.normalizer_core_eq_sylow_centralizer_of_local_inputs h hlocal hproper t htZ htz
  exact ⟨hlocal.second_normalizer_solvable d, hNcard, hKcard, hS3, hZKcard, hZKambient,
    hUcard, hZUcard, hZUambient, d.normalizer_core_omega_inclusions.1, hWX,
    d.normalizer_core_le_sylow, d.normalizer_core_omega_inclusions.2.1, hZUle,
    hWC, hS4, Q, t, v, b, d.normalizer_three_card_of_local_inputs h hlocal hproper Q,
    ht, hv, ht2, hv2, htz, hvZ, hZK, hZU, hXC, hq, hvC, hZUfix, hFfix, hnc,
    hbX, hb4, hb2, hbC, hcyclic, hcard⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
