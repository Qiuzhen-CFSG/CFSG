module
public import Theory.GroupTheory.PCoreIntersectionFivePoint
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutionCentralizer
public import Theory.SpecificGroups.SymmetricFiveInvolutions

/-!
# Selecting the ambient order-twelve image

Let a finite group have a quotient with two-core of order 32 and kernel
of order 64. A second map to S₅ with two-group kernel, intersecting the
first kernel in order 32, cannot have kernel order 2048: its image in the
first quotient would be a normal two-subgroup of order 64. The first
kernel has a normal image of order two in S₅. Its generator is a
transposition, whose centralizer excludes the remaining order-24 case.
The surviving image is the entire transposition centralizer, and the
second kernel has order 1024.

This compares two distinct literal homomorphisms; it does not identify
their kernels. The original Rudvalis point-centralizer application is in
Chapter13/Section03/SourceCompletion/OriginalOddNormalizer/RudvalisAmbientOrder.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Two compatible kernel orders select the whole transposition centralizer in S₅. -/
theorem fivePoint_image_exact_of_two_kernels
    {B H : Type*} [Group B] [Finite B] [Group H] [Finite H]
    (b : B →* H) (hb : Function.Surjective b)
    (r : B →* Equiv.Perm (Fin 5))
    (hcore : Nat.card (pCore 2 H) = 32)
    (hbk : Nat.card b.ker = 64)
    (hinter : Nat.card (b.ker ⊓ r.ker : Subgroup B) = 32)
    (hrtwo : IsPGroup 2 r.ker)
    (hsize : (Nat.card r.ker = 2048 ∧ Nat.card r.range = 6) ∨
      (Nat.card r.ker = 1024 ∧ Nat.card r.range = 12) ∨
      (Nat.card r.ker = 512 ∧ Nat.card r.range = 24)) :
    Nat.card r.ker = 1024 ∧ Nat.card r.range = 12 ∧
      ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
        b.ker.map r = zpowers t ∧ r.range = centralizer ({t} : Set _) := by
  have hsmall : Nat.card r.ker ≤ 1024 := by
    let : (r.ker.map b).Normal := Subgroup.Normal.map inferInstance b hb
    have hle : r.ker.map b ≤ pCore 2 H := le_sSup ⟨inferInstance,hrtwo.map b⟩
    have hc : Nat.card (r.ker.map b) ≤ 32 := hcore ▸ Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    have hm := IsElementaryAbelian.card_inf_ker_mul_card_map r.ker b
    rw [inf_comm,hinter] at hm
    omega
  let N := b.ker.map r
  have hN : Nat.card N = 2 := by
    have hm := IsElementaryAbelian.card_inf_ker_mul_card_map b.ker r
    rw [hinter,hbk] at hm
    change Nat.card (b.ker.map r) = 2
    omega
  obtain ⟨t,ht,ht1⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ N ≤ ⊥ from fun h => by
      have hh := card_eq_one.mpr (bot_unique h)
      omega)
  have ht2 : orderOf t = 2 := by
    have hd : orderOf (⟨t,ht⟩ : N) ∣ 2 := hN ▸ orderOf_dvd_natCard _
    rw [←orderOf_coe] at hd
    exact (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      (fun h => ht1 (mem_bot.mpr (orderOf_eq_one_iff.mp h)))
  have hNC : r.range ≤ centralizer (N : Set (Equiv.Perm (Fin 5))) := by
    apply le_trans ?_ (normalizer_le_centralizer_of_card_two N hN)
    rintro x ⟨y,rfl⟩
    exact b.ker.le_normalizer_map r
      (mem_map_of_mem r (show y ∈ normalizer (b.ker : Set B) from le_normalizer_of_normal (mem_top y)))
  have hCt : r.range ≤ centralizer ({t} : Set (Equiv.Perm (Fin 5))) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hNC hx) t ht).symm)
  have hd := card_dvd_of_le hCt
  have hout : t ∉ alternatingGroup (Fin 5) := by
    intro heven
    rw [Equiv.Perm.even_involution_five_centralizer_card t ht2 heven] at hd
    rcases hsize with h|h|h <;> rw [h.2] at hd <;> norm_num at hd
  have hs := Equiv.Perm.five_isSwap_of_outer_involution t ht2 hout
  have hC : Nat.card (centralizer ({t} : Set (Equiv.Perm (Fin 5)))) = 12 := by
    rw [Equiv.Perm.nat_card_centralizer,Equiv.Perm.isSwap_iff_cycleType.mp hs]
    norm_num
  rw [hC] at hd
  have he : Nat.card r.ker = 1024 ∧ Nat.card r.range = 12 := by
    rcases hsize with h|h|h
    · omega
    · exact h
    · rw [h.2] at hd
      norm_num at hd
  refine ⟨he.1,he.2,t,hs,?_,?_⟩
  · apply (eq_of_le_of_card_ge (zpowers_le.mpr ht) ?_).symm
    rw [Nat.card_zpowers,ht2,hN]
  · exact eq_of_le_of_card_ge hCt (by rw [he.2,hC])

end Theory.GroupTheory
