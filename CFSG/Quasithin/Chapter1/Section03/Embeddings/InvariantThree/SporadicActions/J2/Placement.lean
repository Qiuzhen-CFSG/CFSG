module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.Covers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Representatives
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Coverage
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.WordChecks

/-!
# Placing J₂ source pairs in the fixed second normalizer

Conjugate the source Sylow subgroup to the fixed `Seed.s`. The transported
product `RS` has only two and three as prime divisors. The checked double-coset
cover and order-five words therefore force this product into the fixed
normalizer of `Seed.q₂`.

`j2_pair_placement_of_seed_sylow` discharges the coverage and finite local
checks using `Placement.Coverage` and `Placement.WordChecks`. Its sole additional
input is that `Seed.s` is a Sylow two-subgroup. The source pair-action assembly
supplies that input and proves the further local structure and action facts.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), and GLS3 Table 5.3g.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

namespace J2Placement

/-- Prime-order witnesses turn double-coset coverage into a concrete overgroup
bound. This needs no simplicity, total order, or maximal-subgroup catalogue. -/
theorem overgroup_le_second_normalizer_of_certificates
    (hcover : Covers) (hs : Seed.s ≤ Seed.p₂)
    (hcheck : ∀ i : Fin 72, representative i ∈ Seed.p₂ ∨ orderOf (obstruction i) = 5)
    (H : Subgroup Carrier) (hSH : Seed.s ≤ H) (h5 : ¬ 5 ∣ Nat.card H) :
    H ≤ Seed.p₂ := by
  intro x hx
  obtain ⟨i, a, b, ha, hb, rfl⟩ := hcover x
  have hi : representative i ∈ H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem (hSH ha)) hx) (H.inv_mem (hSH hb))
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh
  have hip : representative i ∈ Seed.p₂ := by
    rcases hcheck i with hip | ho
    · exact hip
    · have hd := H.orderOf_dvd_natCard (obstruction_mem H hSH i hi)
      exact (h5 (ho ▸ hd)).elim
  exact Seed.p₂.mul_mem (Seed.p₂.mul_mem (hs ha) hip) (hs hb)

end J2Placement

/-- Conjugacy and the genuine source permutability reduce placement to a
prime-five-free overgroup calculation at the marked Sylow subgroup. -/
theorem j2_pair_placement_of_five_free_overgroups
    (hs : ∃ T : Sylow 2 Carrier, (T : Subgroup Carrier) = Seed.s)
    (hlocal : ∀ H : Subgroup Carrier, Seed.s ≤ H → ¬ 5 ∣ Nat.card H → H ≤ Seed.p₂)
    (S : Sylow 2 Carrier) (R : Subgroup Carrier) (h : PairInput S R) :
    ∃ g : Carrier, (S : Subgroup Carrier).map (MulAut.conj g).toMonoidHom = Seed.s ∧
      R.map (MulAut.conj g).toMonoidHom ≤ Seed.p₂ := by
  obtain ⟨T, hT⟩ := hs
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier S T
  let e := MulAut.conj g
  have hS : (S : Subgroup Carrier).map e.toMonoidHom = Seed.s := by
    change ((g • S : Sylow 2 Carrier) : Subgroup Carrier) = Seed.s
    rw [hg, hT]
  have hm := pairInput_map e h
  let H : Subgroup Carrier := R.map e.toMonoidHom ⊔ (S : Subgroup Carrier).map e.toMonoidHom
  have hSH : Seed.s ≤ H := by
    rw [← hS]
    exact le_sup_right
  have h5 : ¬ 5 ∣ Nat.card H := by
    intro hd
    have hp := EvenRankTwo.product_prime_divisors hm (by decide : Nat.Prime 5) hd
    omega
  exact ⟨g, hS, le_sup_left.trans (hlocal H hSH h5)⟩

/-- Assembly of the finite certificates, retaining their explicit hypotheses
for reuse independently of the concrete checks below. -/
theorem j2_pair_placement_of_doubleCoset_certificates
    (hs : ∃ T : Sylow 2 Carrier, (T : Subgroup Carrier) = Seed.s)
    (hcover : J2Placement.Covers) (hnorm : Seed.s ≤ Seed.p₂)
    (hcheck : ∀ i : Fin 72,
      J2Placement.representative i ∈ Seed.p₂ ∨ orderOf (J2Placement.obstruction i) = 5)
    (S : Sylow 2 Carrier) (R : Subgroup Carrier) (h : PairInput S R) :
    ∃ g : Carrier, (S : Subgroup Carrier).map (MulAut.conj g).toMonoidHom = Seed.s ∧
      R.map (MulAut.conj g).toMonoidHom ≤ Seed.p₂ :=
  j2_pair_placement_of_five_free_overgroups hs
    (J2Placement.overgroup_le_second_normalizer_of_certificates hcover hnorm hcheck) S R h

/-- Every source pair is conjugate into the fixed second normalizer, with its
Sylow two-subgroup sent to `Seed.s`. Only the Sylow property of `Seed.s` remains
an input; coverage, normalization and the order-five obstructions are proved. -/
theorem j2_pair_placement_of_seed_sylow
    (hs : ∃ T : Sylow 2 Carrier, (T : Subgroup Carrier) = Seed.s)
    (S : Sylow 2 Carrier) (R : Subgroup Carrier) (h : PairInput S R) :
    ∃ g : Carrier, (S : Subgroup Carrier).map (MulAut.conj g).toMonoidHom = Seed.s ∧
      R.map (MulAut.conj g).toMonoidHom ≤ Seed.p₂ :=
  j2_pair_placement_of_doubleCoset_certificates hs J2Placement.covers
    J2Placement.s_le_p₂ J2Placement.representative_mem_p₂_or_orderOf_obstruction S R h

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
