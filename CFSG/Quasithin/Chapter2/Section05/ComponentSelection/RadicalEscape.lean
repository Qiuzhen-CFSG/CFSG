module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EscapingNormalizer

/-!
# Component selection from its actual escaping radical normalizer

Saturation makes the component radical the exact normalizer two-core and
supplies all local-pair invariance. Once the model's actual normalizer is
in He and escapes M, its U-orbit join constructs a pair in the component
adjoined to the original Sylow subgroup. Both starred conditions survive.

Source: Aschbacher--Smith 2.5.3(4), printed p.553. The explicit local He
input belongs to the model branch and is discharged at the source consumer.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- The actual radical normalizer selects the component while preserving both stars. -/
theorem component_join_preserves_stars_of_escaping_radical
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (D : Subgroup H) (hD : IsComponent H D)
    (hne : D ⊓ (twoCore HU).subgroupOf H ≠ ⊥)
    (hNe : (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ∈ Chapter1.He G)
    (hout : ¬ (D ⊓ normalizer ((D ⊓ (twoCore HU).subgroupOf H : Subgroup H) : Set H)).map
      H.subtype ≤ M) :
    let X := D.map H.subtype ⊔ (S : Subgroup H).map H.subtype
    X ∈ gammaZero (Chapter1.He G) M ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  let Q := (twoCore HU).subgroupOf H
  let R := D ⊓ Q
  let N := D ⊓ normalizer (R : Set H)
  have hNR : N.pCoreIn 2 = R := saturated_component_radical hpair hsat D hD
  have hNc : twoCore (N.map H.subtype) ≠ ⊥ := by
    intro hb
    have he : R.map H.subtype = ⊥ := by
      rw [← hNR, map_pCoreIn_of_injective 2 N H.subtype H.subtype_injective]
      exact hb
    exact hne ((map_eq_bot_iff_of_injective _ H.subtype_injective).mp he)
  have hAQ : U.subgroupOf H ≤ normalizer (Q : Set H) := by
    intro a ha x
    exact le_normalizer_twoCore HU (hpair.1.2.2.2.1 ha) (x : G)
  have hAR : U.subgroupOf H ⊓ normalizer (D : Set H) ≤ normalizer (R : Set H) :=
    (le_inf inf_le_right (inf_le_left.trans hAQ)).trans inf_normalizer_le_normalizer_inf
  have hAN : U.subgroupOf H ⊓ normalizer (D : Set H) ≤ normalizer (N : Set H) :=
    (le_inf inf_le_right (hAR.trans (normalizer (R : Set H)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hinv : U ⊓ normalizer (D.map H.subtype : Set G) ≤
      normalizer (N.map H.subtype : Set G) := by
    rintro a ⟨ha, hd⟩
    let aH : H := ⟨a, (hUS.trans (map_subtype_le _)) ha⟩
    have hdH : aH ∈ normalizer (D : Set H) := by
      have he := subgroupOf_normalizer_eq (map_subtype_le D)
      rw [show (D.map H.subtype).subgroupOf H = D from
        comap_map_eq_self_of_injective H.subtype_injective D] at he
      rw [← he]
      exact hd
    exact N.le_normalizer_map H.subtype ⟨aH, hAN ⟨ha, hdH⟩, rfl⟩
  exact component_join_preserves_stars_of_escaping_seed hH hpair hbig S hUS D hD
    (N.map H.subtype) (map_mono inf_le_left) hinv hNe hNc hout

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
