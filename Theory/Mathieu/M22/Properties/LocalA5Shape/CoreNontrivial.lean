module

public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Alternating.Aut
public import Theory.PGroupCore

/-!
# The local A5 section in M22 has nontrivial two-core

No involution centralizes a subgroup whose order is divisible by five:
M22 involution centralizers have order 384. Hence a full Sylow subgroup
normalizing an actual A5 acts faithfully on it. Its order would divide
|Aut(A5)| = 120, contradicting the factor sixteen in the Sylow order.
A subgroup with A5 quotient by its two-core therefore has nontrivial core.

This is the trivial-core branch in the E16:A5 shape calculation used by
Aschbacher--Smith A.3.14(6) and 10.2.9, pp.49 and 750--751.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22LocalA5Shape

/-- Five-divisibility excludes a nontrivial Sylow centralizer. -/
theorem sylow_centralizer_eq_bot (S : Sylow 2 M22) (B : Subgroup M22)
    (h5 : 5 ∣ Nat.card B) : (S : Subgroup M22) ⊓ centralizer (B : Set M22) = ⊥ := by
  let C := (S : Subgroup M22) ⊓ centralizer (B : Set M22)
  by_contra h
  let : Nontrivial C := C.nontrivial_iff_ne_bot.mpr h
  have hp : IsPGroup 2 C := S.isPGroup'.to_le inf_le_left
  obtain ⟨n, hn, hc⟩ := hp.nontrivial_iff_card.mp inferInstance
  have hd : 2 ∣ Nat.card C := by
    rw [hc]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
  have ht2 : orderOf (t : M22) = 2 := by simpa only [orderOf_coe] using ht
  have hB : B ≤ centralizer ({(t : M22)} : Set M22) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (t.property.2 b hb)
  have hd5 := h5.trans (card_dvd_of_le hB)
  rw [M22FourNormalizers.involution_centralizer_card t ht2] at hd5
  norm_num at hd5

/-- A full native Sylow cannot normalize an actual A5 subgroup. -/
theorem alternatingFive_not_normalized_by_sylow
    (S : Sylow 2 M22) (B : Subgroup M22)
    (e : B ≃* alternatingGroup (Fin 5))
    (hSB : (S : Subgroup M22) ≤ normalizer (B : Set M22)) : False := by
  have hc : Nat.card B = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hfaith := sylow_centralizer_eq_bot S B (by rw [hc]; decide)
  let f := B.normalizerMonoidHom.comp (inclusion hSB)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property, ?_⟩
    change inclusion hSB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let eA : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let j := eA.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
  have hj : Function.Injective j := eA.symm.injective.comp ((MulAut.congr e).injective.comp hf)
  have hd : Nat.card S ∣ 120 := by
    have hd := card_dvd_of_injective j hj
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
      show Nat.factorial 5 = 120 from rfl] using hd
  have hs : 16 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 4)
    (by rw [m22_order]; decide)
  have hbad := hs.trans hd
  norm_num at hbad

/-- The actual A5 two-core quotient of a Sylow-normalized subgroup has
nontrivial two-core. -/
theorem core_ne_bot_of_normalized
    (S : Sylow 2 M22) (B : Subgroup M22)
    (hSB : (S : Subgroup M22) ≤ normalizer (B : Set M22))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5)) : pCore 2 B ≠ ⊥ := by
  intro hcore
  let e : B ⧸ pCore 2 B ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact alternatingFive_not_normalized_by_sylow S B (e.symm.trans eB) hSB

end Sporadic.Mathieu.M22LocalA5Shape
