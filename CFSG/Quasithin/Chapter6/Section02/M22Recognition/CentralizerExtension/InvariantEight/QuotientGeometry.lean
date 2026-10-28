module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.InvariantEight.QuotientData
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.CoreData
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Locating the eight using the compatible symmetric quotient

Let `M/V ≃ S₅` carry the image of `L` to `A₅`. An order-eight subgroup
`U` normal in a Sylow two-subgroup `T`, with `|U ∩ V| = 4`, has an image of
order two normal in the actual image of `T`. That image lies in `A₅`:
a normal subgroup of order two is central in `T`, whereas an odd involution
of `S₅` is a transposition and has centralizer order twelve, indivisible by
`|T| = 8`. Pulling back along the same quotient map gives `U ≤ L`.

This is the containment step for the source normal closure in the p.688
branch of Aschbacher–Smith, Proposition 6.2.13 (PDF p.705). The normality is
relative to `T`; neither an ambient normality assertion nor a splitting is
used. The natural `SL₂(4)` action used elsewhere in that branch is not
replaced by the compatible quotient interface.
-/

open Subgroup
private abbrev Sym5 := Equiv.Perm (Fin 5)
private theorem odd_involution_centralizer_card (x : Sym5) (hx : x ^ 2 = 1)
    (hs : Equiv.Perm.sign x ≠ 1) : Nat.card (centralizer ({x} : Set Sym5)) = 12 := by
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hx
  have hb := x.sum_cycleType_le
  rw [ht] at hb
  simp only [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hb
  have hsign : Equiv.Perm.sign x = (-1 : ℤˣ) ^ x.cycleType.card := by
    rw [Equiv.Perm.sign_of_cycleType', ht, Multiset.map_replicate, Multiset.prod_replicate]
    norm_num
  have hn : x.cycleType.card = 1 := by
    by_contra hne
    have hc : x.cycleType.card = 0 ∨ x.cycleType.card = 2 := by omega
    rcases hc with hc | hc <;> apply hs <;> simpa [hc] using hsign
  have htype : x.cycleType = {2} := by rw [ht, hn]; rfl
  rw [Equiv.Perm.nat_card_centralizer, htype]
  norm_num [Nat.factorial]

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
private theorem sylow_five_normal_two_even (T : Sylow 2 Sym5) (A : Subgroup Sym5)
    (hAT : A ≤ T) [(A.subgroupOf T).Normal] (hA : Nat.card A = 2) :
    A ≤ alternatingGroup (Fin 5) := by
  have hAc : Nat.card (A.subgroupOf T) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hA
  have hcentral := central_of_normal_card_two (A.subgroupOf T) hAc
  have hTc : Nat.card T = 8 := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin]
    decide +kernel
  intro x hx
  change Equiv.Perm.sign x = 1
  by_contra hs
  have hx2 : x ^ 2 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨x, hx⟩ : A))
    rw [hA] at hp
    exact congrArg Subtype.val hp
  have hTC : (T : Subgroup Sym5) ≤ centralizer ({x} : Set Sym5) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp (hcentral (show (⟨x, hAT hx⟩ : T) ∈ A.subgroupOf T from hx)) ⟨t, ht⟩)
  have hd := card_dvd_of_le hTC
  rw [hTc, odd_involution_centralizer_card x hx2 hs] at hd
  norm_num at hd

/-- The common quotient map locates the eight in the actual layer. -/
public theorem eight_le_layer_of_compatible_quotient
    {M : Type*} [Group M] [Finite M] (V L : Subgroup M) [V.Normal]
    (hq : CompatibleSymmetricFiveQuotient V L)
    (T : Sylow 2 M) (U : Subgroup M) (hUT : U ≤ T)
    [(U.subgroupOf T).Normal] (hU : Nat.card U = 8)
    (hUV : Nat.card (U ⊓ V : Subgroup M) = 4) : U ≤ L := by
  obtain ⟨e, hL⟩ := hq.quotient
  let q := e.toMonoidHom.comp (QuotientGroup.mk' V)
  have hqsurj : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective V)
  have hk : q.ker = V := by
    ext x
    change e (QuotientGroup.mk' V x) = 1 ↔ x ∈ V
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let Tbar := T.mapSurjective hqsurj
  let A := U.map q
  have hAT : A ≤ Tbar := map_mono hUT
  have hn : (T : Subgroup M) ≤ normalizer (U : Set M) :=
    (normal_subgroupOf_iff_le_normalizer hUT).mp inferInstance
  let : (A.subgroupOf Tbar).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAT).mpr ((map_mono hn).trans (U.le_normalizer_map q))
  have hAc : Nat.card A = 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup M) (U ⊓ q.ker) U bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, relIndex_ker, hk,
      hUV, hU] at hc
    change 4 * Nat.card A = 8 at hc
    omega
  have hAL : A ≤ L.map q := by
    rw [hL]
    exact sylow_five_normal_two_even Tbar A hAT hAc
  have hle := map_le_iff_le_comap.mp hAL
  rwa [comap_map_eq, hk, sup_eq_left.mpr hq.kernel_le_layer] at hle
end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension

