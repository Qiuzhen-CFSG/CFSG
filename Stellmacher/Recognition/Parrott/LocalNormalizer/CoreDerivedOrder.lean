module

public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOrder
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreCenter
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreDerivedOmega

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerCoreDerivedOrder`.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The actual ambient derived subgroup of O₂(N_G(F)) has order sixty-four. -/
public theorem normalizer_core_derived_order_of_local_inputs
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    Nat.card ((commutator X).map X.subtype) = 64 := by
  intro N X
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let i := H.subtype.comp J.subtype
  let E := (commutator J).map i
  let D := (commutator X).map X.subtype
  let P := D.comap i
  let q := QuotientGroup.mk' (commutator J)
  have hi : Function.Injective i := H.subtype_injective.comp J.subtype_injective
  obtain ⟨t, ht, htz, _, _, _, hcenter⟩ :=
    d.exists_normalizer_core_center_generator_of_local_inputs h hlocal hproper
  have htZ : t ∈ (center (pCore 2 N)).map (N.subtype.comp (pCore 2 N).subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hXC : X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :=
    d.normalizer_core_eq_sylow_centralizer_of_local_inputs h hlocal hproper t htZ htz
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hXC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order_of_solvable h (hlocal.second_normalizer_solvable d) hproper).2.1
  have hVcard : Nat.card (P.map q) = 4 := by
    change Nat.card ((((commutator X).map X.subtype).comap i).map q) = 4
    rw [hXC]
    exact d.t_centralizer_derived_quotient_card h t ht.1 htz hCcard
  have hDcore : D ≤ i.range := by
    rw [MonoidHom.range_comp, range_subtype]
    exact d.sylow_subgroup_commutator_le_core h X d.normalizer_core_le_sylow
  have hPmap : P.map i = D := map_comap_eq_self hDcore
  have hPcard : Nat.card P = Nat.card D := by
    rw [← card_map_of_injective hi, hPmap]
  have hmeet : Nat.card (P ⊓ commutator J : Subgroup J) = 16 := by
    rw [← card_map_of_injective hi, map_inf _ _ _ hi, hPmap]
    change Nat.card (D ⊓ E : Subgroup G) = 16
    rw [d.normalizer_core_derived_inf_original_derived_of_local_inputs h hlocal hproper]
    exact d.inf_card
  have hindex : (commutator J).relIndex P = 4 := by
    rw [← QuotientGroup.ker_mk' (commutator J), relIndex_ker]
    exact hVcard
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup J) (P ⊓ commutator J) P
    bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left,
    hindex, hmeet, hPcard] at hcount
  exact hcount.symm

end Stellmacher.Recognition.ParrottSecondElementaryData
