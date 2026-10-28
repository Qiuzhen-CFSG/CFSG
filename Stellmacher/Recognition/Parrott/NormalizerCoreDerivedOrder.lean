module

public import Stellmacher.Recognition.Parrott.NormalizerCoreDerivedOmega
public import Stellmacher.Recognition.Parrott.DerivedTQuotientOrder

/-!
# The derived order of the second normalizer core

Write X for the ambient image of O₂(N_G(F)). Identify X with C_T(t),
whose derived image in J/J′ has order four. The intersection of X′ with
the original derived core is E∩F, of order sixteen. Counting this kernel
and image gives |X′|=64 and |X′:F|=2.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, paragraph beginning “An easy computation shows that K′”.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The actual ambient derived subgroup of O₂(N_G(F)) has order sixty-four. -/
public theorem normalizer_core_derived_order
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
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
    d.exists_normalizer_core_center_generator h hN hproper
  have htZ : t ∈ (center (pCore 2 N)).map (N.subtype.comp (pCore 2 N).subtype) := by
    rw [hcenter]
    exact mem_sup_right (mem_zpowers t)
  have hXC : X = (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :=
    d.normalizer_core_eq_sylow_centralizer h hN hproper t htZ htz
  have hCcard : Nat.card ((d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G) :
      Subgroup G) = 1024 := by
    rw [← hXC, card_map_of_injective N.subtype_injective]
    exact (d.normalizer_core_order h hN hproper).2.1
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
    rw [d.normalizer_core_derived_inf_original_derived h hN hproper]
    exact d.inf_card
  have hindex : (commutator J).relIndex P = 4 := by
    rw [← QuotientGroup.ker_mk' (commutator J), relIndex_ker]
    exact hVcard
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup J) (P ⊓ commutator J) P
    bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left,
    hindex, hmeet, hPcard] at hcount
  exact hcount.symm

/-- The supplied elementary subgroup has index two in the actual derived core. -/
public theorem elementary_relIndex_normalizer_core_derived
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    d.F.relIndex ((commutator X).map X.subtype) = 2 := by
  intro N X
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) d.F
    ((commutator X).map X.subtype) bot_le (d.elementary_le_normalizer_core_derived h hN hproper)
  rw [relIndex_bot_left, relIndex_bot_left, d.card,
    d.normalizer_core_derived_order h hN hproper] at hh
  omega

end Stellmacher.Recognition.ParrottSecondElementaryData
