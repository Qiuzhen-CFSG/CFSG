module

public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Arithmetic
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import GorensteinWalter.LinearRingEquiv
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Field restrictions for the dihedral-centralizer recognition theorem

In odd-characteristic PSL₂, an involution centralizer is a cyclic torus
extended by an external inverting involution. Adjoining that reflection
doubles the torus order, so the centralizer has order q − 1 or q + 1.
Centralizer order eight therefore forces q = 7 or 9. Above order eight,
the prime-power neighbor theorem forces q to be a Fermat or Mersenne
prime p. The coefficient-ring equivalence F ≃ ZMod p induces an actual
isomorphism of projective special linear groups.

The final wrappers apply these results to the distinguished involution and
literal centralizer of the I.4.1 hypotheses, along an independently supplied
PSL₂ isomorphism. Recognition of that initial model remains with the source
assembly owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.4.1, printed p.415 (PDF p.426).
-/

public section
noncomputable section

namespace CFSG.Quasithin
open GorensteinWalter Subgroup

/-- The exact order of an involution centralizer in odd-characteristic PSL₂. -/
theorem psl2_involution_centralizer_card
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F} (ht : IsInvolution t) :
    Nat.card (centralizer ({t} : Set (PSL2 F))) = Nat.card F - 1 ∨
      Nat.card (centralizer ({t} : Set (PSL2 F))) = Nat.card F + 1 := by
  obtain ⟨T, s, _hcyclic, _htT, hs, hsout, hinv, hcentralizer, _heven, htorus⟩ :=
    psl2_reflected_torus_card hF ht
  have hnorm : s ∈ normalizer (T : Set (PSL2 F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      change s * y * s⁻¹ ∈ T
      rw [hinv y hy]
      exact T.inv_mem hy
    · intro x hx
      refine mem_map.mpr ⟨x⁻¹, T.inv_mem hx, ?_⟩
      change s * x⁻¹ * s⁻¹ = x
      rw [hinv (x⁻¹) (T.inv_mem hx), inv_inv]
  have hdouble := card_sup_zpowers_of_normalizing_involution T s hs.2 hsout hnorm
  rw [← hcentralizer] at hdouble
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, k, _hp, hpodd, _hk, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  obtain ⟨k, hk⟩ := hodd
  rcases htorus with hminus | hplus
  · left
    omega
  · right
    omega

/-- A power-of-two involution centralizer forces the field size to be a neighbor
of the same power of two. The count does not need a lower bound on `n`. -/
theorem psl2_field_card_neighbors
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F} (ht : IsInvolution t)
    {n : ℕ} (hcard : Nat.card (centralizer ({t} : Set (PSL2 F))) = 2 ^ n) :
    Nat.card F + 1 = 2 ^ n ∨ Nat.card F = 2 ^ n + 1 := by
  have hpos : 0 < Nat.card F := Nat.card_pos
  rcases psl2_involution_centralizer_card hF ht with hminus | hplus
  · right
    omega
  · left
    omega

/-- The two field sizes in the centralizer-order-eight case of I.4.1. -/
theorem psl2_field_card_seven_or_nine
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F} (ht : IsInvolution t)
    (hcard : Nat.card (centralizer ({t} : Set (PSL2 F))) = 8) :
    Nat.card F = 7 ∨ Nat.card F = 9 := by
  have h := psl2_field_card_neighbors hF ht (n := 3) (by simpa using hcard)
  norm_num at h
  omega

/-- Above centralizer order eight, the field itself has prime order. -/
theorem psl2_field_card_prime_of_three_lt
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F} (ht : IsInvolution t)
    {n : ℕ} (hn : 3 < n)
    (hcard : Nat.card (centralizer ({t} : Set (PSL2 F))) = 2 ^ n) :
    ∃ p : ℕ, Nat.card F = p ∧ IsFermatOrMersennePrime p := by
  have hneighbor := psl2_field_card_neighbors hF ht hcard
  obtain ⟨p, k, hp, hpodd, hk, hq⟩ := hF
  rw [hq] at hneighbor
  obtain ⟨hkone, hprime⟩ :=
    prime_power_two_power_neighbors_of_three_lt hp hpodd hk hn hneighbor
  refine ⟨p, ?_, hprime⟩
  simpa only [hkone, pow_one] using hq

/-- The numerical restriction gives an actual prime-field PSL₂ isomorphism. -/
theorem psl2_prime_field_equiv_of_three_lt
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F} (ht : IsInvolution t)
    {n : ℕ} (hn : 3 < n)
    (hcard : Nat.card (centralizer ({t} : Set (PSL2 F))) = 2 ^ n) :
    ∃ p : ℕ, Nat.card F = p ∧ IsFermatOrMersennePrime p ∧
      Nonempty (PSL2 F ≃* PSL2 (ZMod p)) := by
  obtain ⟨p, hq, hp⟩ := psl2_field_card_prime_of_three_lt hF ht hn hcard
  let : Fintype F := Fintype.ofFinite F
  let e : ZMod p ≃+* F := ZMod.ringEquivOfPrime F hp.1 (by
    simpa only [← Nat.card_eq_fintype_card] using hq)
  exact ⟨p, hq, hp, ⟨(psl2RingEquiv e).symm⟩⟩

namespace DihedralInvolutionCentralizerHypotheses
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

private theorem transported_involution_centralizer
    (h : DihedralInvolutionCentralizerHypotheses G n)
    {F : Type*} [Field F] [Finite F] (e : G ≃* PSL2 F) :
    IsInvolution (e h.z) ∧
      Nat.card (centralizer ({e h.z} : Set (PSL2 F))) = 2 ^ n := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro he
    apply h.involution.1
    apply e.injective
    simpa only [map_one] using he
  · simpa only [map_pow, map_one] using congrArg e h.involution.2
  · calc
      _ = Nat.card (centralizer ({h.z} : Set G)) :=
        (Nat.card_congr
          (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e h.z).toEquiv).symm
      _ = 2 ^ n := h.centralizer_card

/-- Transport I.4.1's literal centralizer to an independently recognized PSL₂ model. -/
theorem field_card_neighbors
    (h : DihedralInvolutionCentralizerHypotheses G n)
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F) :
    Nat.card F + 1 = 2 ^ n ∨ Nat.card F = 2 ^ n + 1 := by
  obtain ⟨ht, hcard⟩ := h.transported_involution_centralizer e
  exact psl2_field_card_neighbors hF ht hcard

/-- The order-eight source hypotheses restrict any odd PSL₂ model to sizes seven or nine. -/
theorem field_card_seven_or_nine
    (h : DihedralInvolutionCentralizerHypotheses G 3)
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F) :
    Nat.card F = 7 ∨ Nat.card F = 9 := by
  obtain ⟨ht, hcard⟩ := h.transported_involution_centralizer e
  exact psl2_field_card_seven_or_nine hF ht (by simpa using hcard)

/-- The field restriction in I.4.1(3), including the actual isomorphism from the
original group. Only the initial odd-field PSL₂ recognition remains an input. -/
theorem prime_field_equiv_of_three_lt
    (h : DihedralInvolutionCentralizerHypotheses G n)
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F) (hn : 3 < n) :
    ∃ p : ℕ, Nat.card F = p ∧ IsFermatOrMersennePrime p ∧
      Nonempty (G ≃* PSL2 (ZMod p)) := by
  obtain ⟨ht, hcard⟩ := h.transported_involution_centralizer e
  obtain ⟨p, hq, hp, ⟨ep⟩⟩ := psl2_prime_field_equiv_of_three_lt hF ht hn hcard
  exact ⟨p, hq, hp, ⟨e.trans ep⟩⟩

end DihedralInvolutionCentralizerHypotheses
end CFSG.Quasithin
