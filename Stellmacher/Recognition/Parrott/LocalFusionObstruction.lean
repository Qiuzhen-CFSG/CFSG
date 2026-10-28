module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalizer obstructions for Parrott's local fusion computations

For the supplied Sylow subgroup T and an involution t, suppose the common
centralizer C_G(z) ∩ C_G(t) is C_T(t), of order less than 2048. Fusion of
z and t then forces the normalizer of C_T(t) outside C_G(z). The same is
true of the normalizer of the actual ambient image of Ω₁(C_T(t)′).

If Z(C_T(t)) = ⟨z,t⟩, a characteristic subgroup of order two in C_T(t)
excludes fusion. The version for characteristic subgroups of C_T(t)′
applies to both its derived subgroup and its square subgroup when abelian.

These are the general exclusion steps in Parrott (1972), pp.676–677.
This module keeps the local centralizer and characteristic-subgroup
computations as explicit premises; constructing the two representatives
and proving those computations is separate work.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem localSylow_card (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) : Nat.card d.localSylow = 2048 := by
  have hc := d.sylow_card h
  rw [d.sylow_map, card_map_of_injective
    (centralizer ({z} : Set G)).subtype_injective] at hc
  exact hc

/-- Fusion forces the local centralizer normalizer outside C_G(z). -/
public theorem local_fusion_normalizer_obstruction (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (t : G)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048)
    (hconj : IsConj z t) :
    ¬ normalizer ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Set G) ≤
      centralizer ({z} : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    d.sylow.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  change ¬ normalizer (((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤
    centralizer ({z} : Set G)
  rw [← hlocal] at hp hsmall ⊢
  apply normalizer_inf_centralizer_not_le_of_isConj z t hconj hp d.localSylow
  rwa [d.localSylow_card h]

/-- Fusion forces the normalizer of Ω₁(C_T(t)′) outside C_G(z).
The omega subgroup is taken after passing to the derived subgroup. -/
public theorem local_fusion_omega_derived_obstruction (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (t : G)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048)
    (hconj : IsConj z t) :
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    let W := (omega₁ (commutator C) (p := 2)).map (C.subtype.comp (commutator C).subtype)
    ¬ normalizer (W : Set G) ≤ centralizer ({z} : Set G) := by
  intro C W hN
  let O := omega₁ (commutator C) (p := 2)
  let : O.Characteristic := omega₁_characteristic (commutator C)
  have hCW : normalizer (C : Set G) ≤ normalizer (W : Set G) := by
    have hle := normalizer_le_normalizer_characteristic_image C
      (O.map (commutator C).subtype)
    rwa [map_map] at hle
  exact d.local_fusion_normalizer_obstruction h t hlocal hsmall hconj (hCW.trans hN)

/-- The four possible omega images in the t-centralizer computation each
exclude fusion under the second self-normalizer assumption. -/
public theorem local_fusion_omega_derived_cases (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G)) (t : G)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048)
    (A : Subgroup G) (hA : (commutator A).map A.subtype = zpowers z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    let W := (omega₁ (commutator C) (p := 2)).map (C.subtype.comp (commutator C).subtype)
    (W = E ∨ W = d.F ∨ W = A ∨ centralizer (W : Set G) = A) → ¬ IsConj z t := by
  intro H E C W hcases hconj
  have hAnorm : normalizer (A : Set G) ≤ H :=
    normalizer_le_centralizer_of_characteristic_involution A (commutator A)
      z h.involution hA
  apply d.local_fusion_omega_derived_obstruction h t hlocal hsmall hconj
  change normalizer (W : Set G) ≤ H
  rcases hcases with hE | hF | hWA | hCA
  · rw [hE]
    exact (parrott_derived_normalizer_of_nTwo hN z h).le
  · rw [hF, hself]
    exact d.sylow_le_centralizer
  · rw [hWA]
    exact hAnorm
  · have hle := normalizer_le_normalizer_centralizer W
    rw [hCA] at hle
    exact hle.trans hAnorm

/-- A characteristic subgroup of order two in a local centralizer with
center ⟨z,t⟩ excludes fusion, without specifying its nonidentity element. -/
public theorem local_fusion_characteristic_two (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (t : G) (ht : orderOf t = 2) (hzt : Commute z t)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048) :
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    (center C).map C.subtype = closure ({z, t} : Set G) →
    ∀ K : Subgroup C, K.Characteristic → Nat.card K = 2 → ¬ IsConj z t := by
  have hp : IsPGroup 2 ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
    d.sylow.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hs : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) <
      Nat.card d.localSylow := by
    rw [d.localSylow_card h]
    exact hsmall
  rw [← hlocal] at hp hs
  dsimp only
  rw [← hlocal]
  intro hcenter K hKchar hKcard
  let : K.Characteristic := hKchar
  exact not_isConj_of_common_centralizer_characteristic_two z t h.involution ht hzt
    hp d.localSylow hs hcenter K hKcard

/-- The characteristic order-two obstruction can be computed in the derived
subgroup, as in the V″ and ℧¹(V′) branches of Parrott's argument. -/
public theorem local_fusion_derived_characteristic_two (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (t : G) (ht : orderOf t = 2) (hzt : Commute z t)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048) :
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    (center C).map C.subtype = closure ({z, t} : Set G) →
    ∀ K : Subgroup (commutator C), K.Characteristic → Nat.card K = 2 → ¬ IsConj z t := by
  intro C hcenter K hKchar hKcard
  let : K.Characteristic := hKchar
  apply d.local_fusion_characteristic_two h t ht hzt hlocal hsmall hcenter
    (K.map (commutator C).subtype) inferInstance
  rwa [card_map_of_injective (commutator C).subtype_injective]

/-- The square subgroup of the derived local centralizer, ℧¹(C_T(t)′),
excludes fusion if it has order two. This is the square subgroup of the
derived group, not the square subgroup of the whole centralizer. -/
public theorem local_fusion_derived_square_two (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (t : G) (ht : orderOf t = 2) (hzt : Commute z t)
    (hlocal : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) =
      (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G))
    (hsmall : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) : Subgroup G) < 2048) :
    let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
    (center C).map C.subtype = closure ({z, t} : Set G) →
    Nat.card (closure (Set.range (fun x : commutator C => x ^ 2))) = 2 → ¬ IsConj z t := by
  intro C hcenter hcard
  exact d.local_fusion_derived_characteristic_two h t ht hzt hlocal hsmall hcenter
    (closure (Set.range (fun x : commutator C => x ^ 2)))
    (closure_range_pow_characteristic 2) hcard

end Stellmacher.Recognition.ParrottSecondElementaryData
