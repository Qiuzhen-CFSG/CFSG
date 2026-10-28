module

public import Stellmacher.Recognition.Parrott.ChosenCoreNormalizerQuotient
public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLocalBounds
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.ElementaryIndexTwoNormalizer
public import Theory.GroupTheory.PGroup.Omega

/-!
# The lower bound for the chosen omega subgroup

For the supplied second elementary data put `S = C_G(z) ∩ C_G(a)` and
`U = Ω₁(S)`, regarded as an actual ambient subgroup. The fixed join `F`
lies in `U`. Given that the chosen center has order eight, the symmetric-three normalizer quotient supplies a factor
three in the order of `N_G(U)`. Since `F` is self-centralizing and its
normalizer is the supplied two-Sylow, `F` cannot have index two in `U`.
Equality is excluded by characteristicity of omega and movement of `F`
by `N_G(S)`. Consequently `|U:F| ≥ 4` and `|U| ≥ 128`.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.676, “As 3 divides” through the exclusion of maximality of `F` in omega.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] {z : G}

/-- The supplied elementary subgroup lies in the actual chosen omega image. -/
public theorem fixed_join_le_chosen_omega (d : ParrottSecondElementaryData z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    d.F ≤ (omega₁ S (p := 2)).map S.subtype := by
  intro S x hx
  let : IsElementaryAbelian 2 d.F := d.elementary
  refine ⟨⟨x, d.le_chosen_centralizer hx⟩, subset_closure ?_, rfl⟩
  change (⟨x, d.le_chosen_centralizer hx⟩ : S) ^ (2 ^ 1) = 1
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx

/-- Characteristicity of omega preserves the actual ambient normalizer inclusion. -/
public theorem chosen_normalizer_le_omega_normalizer (d : ParrottSecondElementaryData z) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    normalizer (S : Set G) ≤
      normalizer (((omega₁ S (p := 2)).map S.subtype : Subgroup G) : Set G) := by
  intro S
  let : (omega₁ S (p := 2)).Characteristic := omega₁_characteristic S
  exact normalizer_le_normalizer_characteristic_image S (omega₁ S (p := 2))

variable [Finite G]

/-- The S₃ quotient forces a factor three in the omega normalizer order. -/
public theorem chosen_omega_normalizer_card_three_dvd [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    3 ∣ Nat.card (normalizer
      (((omega₁ S (p := 2)).map S.subtype : Subgroup G) : Set G)) := by
  intro S
  let N := normalizer (S : Set G)
  obtain ⟨e⟩ :=
    chosen_centralizer_normalizer_quotient hns hN d h hself hderived hconj hcenter
  have hc : Nat.card (N ⧸ S.subgroupOf N) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdiv : 3 ∣ Nat.card N := by
    have hd : Nat.card (N ⧸ S.subgroupOf N) ∣ Nat.card N :=
      (S.subgroupOf N).index_dvd_card
    rw [hc] at hd
    exact (by decide : 3 ∣ 6).trans hd
  exact hdiv.trans (card_dvd_of_le d.chosen_normalizer_le_omega_normalizer)

/-- The chosen omega has at least four cosets of the supplied fixed join.
In particular the fixed join is neither the whole omega nor maximal in it. -/
public theorem chosen_omega_fixed_join_relIndex_ge_four [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let S := centralizer ({z} : Set G) ⊓ centralizer ({(d.a : G)} : Set G)
    let U := (omega₁ S (p := 2)).map S.subtype
    4 ≤ d.F.relIndex U ∧ 128 ≤ Nat.card (omega₁ S (p := 2)) := by
  intro S U
  have hFU : d.F ≤ U := d.fixed_join_le_chosen_omega
  have hUS : U ≤ S := map_subtype_le _
  have hneone : d.F.relIndex U ≠ 1 := by
    intro hi
    have heq : U = d.F := le_antisymm (relIndex_eq_one.mp hi) hFU
    apply d.chosen_centralizer_normalizer_not_le_fixed_join_normalizer h hself hconj
    have hh := d.chosen_normalizer_le_omega_normalizer
    change normalizer (S : Set G) ≤ normalizer (U : Set G) at hh
    rwa [heq] at hh
  have hnetwo : d.F.relIndex U ≠ 2 := by
    apply relIndex_ne_two_of_three_dvd_normalizer d.F U d.elementary hFU
      d.centralizer_eq.le
    · rw [hself]
      exact d.sylow.isPGroup'
    · exact chosen_omega_normalizer_card_three_dvd hns hN d h hself hderived hconj hcenter
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) d.F U bot_le hFU
  rw [relIndex_bot_left, relIndex_bot_left, d.card] at hc
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hd : Nat.card U ∣ 2048 := by
    have hh := card_dvd_of_le (hUS.trans (d.chosen_centralizer_le_sylow h))
    rwa [d.sylow_card h] at hh
  have hnethree : d.F.relIndex U ≠ 3 := by
    intro hi
    have hu : Nat.card U = 96 := by omega
    rw [hu] at hd
    norm_num at hd
  have hge : 4 ≤ d.F.relIndex U := by omega
  refine ⟨hge, ?_⟩
  have hmap : Nat.card U = Nat.card (omega₁ S (p := 2)) :=
    card_map_of_injective S.subtype_injective
  omega

/-- Once the chosen omega is proper, the source cardinalities and its index
are forced. This separates the counting argument from the local properness
calculation without replacing either of the actual subgroups. -/
public theorem chosen_omega_geometry_of_ne_top [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hself : normalizer (d.F : Set G) = (d.sylow : Subgroup G))
    (hderived : ∀ t : G, t ∈ (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype) → IsConj z t → t = z)
    (hconj : IsConj z (d.a : G))
    (hcenter : Nat.card (center (centralizer ({z} : Set G) ⊓
      centralizer ({(d.a : G)} : Set G) : Subgroup G)) = 8) :
    let H := centralizer ({z} : Set G)
    let K := (pCore 2 H).map H.subtype
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let V := omega₁ S (p := 2)
    V ≠ ⊤ → V.index = 2 ∧ Nat.card S = 256 ∧ Nat.card V = 128 ∧
      d.F.relIndex (V.map S.subtype) = 4 ∧ K.relIndex S = 4 ∧
      Nat.card (K ⊓ S : Subgroup G) = 64 := by
  intro H K S V hproper
  have hlarge := (chosen_omega_fixed_join_relIndex_ge_four
    hns hN d h hself hderived hconj hcenter).2
  change 128 ≤ Nat.card V at hlarge
  have hsmall := (d.chosen_centralizer_card_bounds h).2
  change Nat.card S ≤ 256 at hsmall
  have hc := V.card_mul_index
  have hneone : V.index ≠ 1 := fun hi => hproper (index_eq_one.mp hi)
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hi : 2 ≤ V.index := by
    have hnezero : V.index ≠ 0 := by intro hh; rw [hh, mul_zero] at hc; omega
    omega
  have htwice : Nat.card V * 2 ≤ Nat.card S :=
    (Nat.mul_le_mul_left (Nat.card V) hi).trans_eq hc
  have hV : Nat.card V = 128 := by omega
  have hS : Nat.card S = 256 := by omega
  have hindex : V.index = 2 := by rw [hV, hS] at hc; omega
  have hFU : d.F ≤ V.map S.subtype := d.fixed_join_le_chosen_omega
  have hFindex : d.F.relIndex (V.map S.subtype) = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) d.F (V.map S.subtype) bot_le hFU
    rw [relIndex_bot_left, relIndex_bot_left, d.card,
      card_map_of_injective S.subtype_injective, hV] at hh
    omega
  have hKindex : K.relIndex S = 4 := by
    rcases d.chosen_core_relIndex_cases h with ht | ht
    · have hh := (d.chosen_card_of_core_relIndex_two h ht).2
      change Nat.card S = 128 at hh
      omega
    · exact ht
  have hKcard : Nat.card (K ⊓ S : Subgroup G) = 64 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ S) S bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, hKindex, hS] at hh
    omega
  exact ⟨hindex, hS, hV, hFindex, hKindex, hKcard⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
