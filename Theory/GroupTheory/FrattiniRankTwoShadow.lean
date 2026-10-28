module

public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.Data.Fintype.Perm

import Mathlib.Tactic.NormNum

/-!
# Removing the Frattini kernel of a binary rank-two shadow

Let `C` be the preimage of `Φ(H/O₂(H))` in a finite group `H`. If `H/C`
is isomorphic to `S₃ × S₃` and the three-part of `|H|` is at most nine,
then `Φ(H/O₂(H)) = 1`, `C = O₂(H)`, and `H/O₂(H) ≃ S₃ × S₃`.

Work in `Q = H/O₂(H)`, whose two-core is trivial. The Frattini argument
and nongeneration make every Sylow subgroup of `Φ(Q)` normal in `Q`, so
the Frattini subgroup has odd order. Since its index is 36, the three-part
bound also excludes three from its order. Thus its order and index are
coprime. Schur–Zassenhaus supplies a complement, which nongeneration
forces to be all of `Q`; hence the Frattini subgroup is trivial.
No solvability hypothesis is required.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), final paragraph of the proof
of 15.3.35, printed p.1139. The preimage convention for `O_{2,Φ}` is on
printed p.491. This module proves the finite-group kernel elimination;
the source application supplies the three-part bound separately.
-/

namespace Subgroup

/-- A prime absent from the normal prime core is absent from the order of
the Frattini subgroup: its Sylow subgroup is normal in the ambient group. -/
public theorem not_dvd_card_frattini_of_pCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hc : pCore p G = ⊥) : ¬ p ∣ Nat.card (frattini G) := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := frattini G)
  have hn : ((P : Subgroup (frattini G)).map (frattini G).subtype).Normal :=
    normalizer_eq_top_iff.mp (frattini_nongenerating P.normalizer_sup_eq_top)
  have hle : (P : Subgroup (frattini G)).map (frattini G).subtype ≤ pCore p G :=
    le_sSup ⟨hn, P.isPGroup'.map _⟩
  rw [hc] at hle
  have hP : (P : Subgroup (frattini G)) = ⊥ := by
    apply Subgroup.map_injective (frattini G).subtype_injective
    simpa using bot_unique hle
  simpa [hP] using P.not_dvd_index

/-- A finite Frattini subgroup whose order is coprime to its index is trivial. -/
public theorem frattini_eq_bot_of_coprime_index
    {G : Type*} [Group G] [Finite G]
    (hcop : Nat.Coprime (Nat.card (frattini G)) (frattini G).index) :
    frattini G = ⊥ := by
  obtain ⟨K, hK⟩ := exists_left_complement'_of_coprime hcop
  have ht : K = ⊤ := frattini_nongenerating hK.sup_eq_top
  simpa [ht] using hK.disjoint

end Subgroup

open Subgroup

namespace FrattiniRankTwoShadow

private theorem reduced_frattini_eq_bot {G : Type*} [Group G] [Finite G]
    (hc : pCore 2 G = ⊥) (hi : (frattini G).index = 36)
    (hthree : (Nat.card G).factorization 3 ≤ 2) : frattini G = ⊥ := by
  have htwo : ¬ 2 ∣ Nat.card (frattini G) :=
    not_dvd_card_frattini_of_pCore_eq_bot hc
  have hcount := (frattini G).card_mul_index
  rw [hi] at hcount
  have hf := congrArg (fun n : ℕ => n.factorization 3) hcount
  rw [Nat.factorization_mul Nat.card_pos.ne' (by decide)] at hf
  have h36 : (36 : ℕ).factorization 3 = 2 := by
    rw [show 36 = 2 ^ 2 * 3 ^ 2 by decide,
      Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow]
    norm_num
  simp only [Finsupp.add_apply, h36] at hf
  have hnthree : ¬ 3 ∣ Nat.card (frattini G) := by
    intro hd
    have hp := Nat.prime_three.factorization_pos_of_dvd Nat.card_pos.ne' hd
    omega
  apply frattini_eq_bot_of_coprime_index
  rw [hi, show 36 = 2 ^ 2 * 3 ^ 2 by decide, Nat.coprime_mul_iff_right]
  exact ⟨((Nat.prime_two.coprime_iff_not_dvd.mpr htwo).symm).pow_right 2,
    ((Nat.prime_three.coprime_iff_not_dvd.mpr hnthree).symm).pow_right 2⟩

/-- The Frattini subgroup of the two-core quotient vanishes when the
Frattini shadow is `S₃ × S₃` and the three-part of the group order is at most nine. -/
public theorem frattini_quotient_twoCore_eq_bot {H : Type*} [Group H] [Finite H]
    (hmodel : Nonempty ((H ⧸ (frattini (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hthree : (Nat.card H).factorization 3 ≤ 2) :
    frattini (H ⧸ pCore 2 H) = ⊥ := by
  let Q := H ⧸ pCore 2 H
  let C := (frattini Q).comap (QuotientGroup.mk' (pCore 2 H))
  have hc : pCore 2 Q = ⊥ := by
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (pCore 2 H))
    rw [(QuotientGroup.mk' (pCore 2 H)).comap_pCore_of_ker_isPGroup
      (QuotientGroup.mk'_surjective _) (by
        rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)]
    exact (QuotientGroup.ker_mk' (pCore 2 H)).symm
  have hC : C.index = 36 := by
    obtain ⟨e⟩ := hmodel
    rw [index_eq_card, Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hi : (frattini Q).index = 36 := by
    rw [← index_comap_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 H))]
    exact hC
  apply reduced_frattini_eq_bot hc hi
  exact ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (pCore 2 H).card_quotient_dvd_card 3).trans hthree

/-- Under the rank-two shadow and order bound, the full preimage `O_{2,Φ}(H)`
equals the actual two-core. -/
public theorem frattini_preimage_eq_twoCore {H : Type*} [Group H] [Finite H]
    (hmodel : Nonempty ((H ⧸ (frattini (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hthree : (Nat.card H).factorization 3 ≤ 2) :
    (frattini (H ⧸ pCore 2 H)).comap (QuotientGroup.mk' (pCore 2 H)) =
      pCore 2 H := by
  rw [frattini_quotient_twoCore_eq_bot hmodel hthree]
  exact QuotientGroup.ker_mk' (pCore 2 H)

/-- The given shadow isomorphism yields an isomorphism over the two-core,
after proving the equality of the two denominators. -/
public theorem quotient_twoCore_equiv {H : Type*} [Group H] [Finite H]
    (hmodel : Nonempty ((H ⧸ (frattini (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hthree : (Nat.card H).factorization 3 ≤ 2) :
    Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  obtain ⟨e⟩ := hmodel
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (frattini_preimage_eq_twoCore ⟨e⟩ hthree).symm).trans e⟩

end FrattiniRankTwoShadow
