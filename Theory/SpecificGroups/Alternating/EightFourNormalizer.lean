module
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms

/-!
# A₄ normalizers cannot have the small source index in degree eight

Conjugation embeds N(B)/C(B) into Aut(B). For B isomorphic to A₄, the
existing automorphism equivalence identifies Aut(B) with S₄. When |C(B)| ≤ 2,
this shows |N(B)| divides 48. Its intersection with any subgroup of order 64
therefore has order dividing gcd(48,64) = 16, so its relative index is at least
four. In particular it cannot satisfy the source bound of two.

The final consumer uses the literal image in S₈ of an arbitrary Sylow
2-subgroup of A₈; its order 64 is derived from the alternating-group order.
Source application: Aschbacher–Smith 2.4.32, the alternating-eight exclusion.
-/

public noncomputable section
open Subgroup
namespace AlternatingEight

/-- The centralizer bound and the actual automorphism group of A₄ bound
the order of its whole symmetric-group normalizer. -/
theorem four_normalizer_card_dvd
    (B : Subgroup (Equiv.Perm (Fin 8))) (eB : B ≃* alternatingGroup (Fin 4))
    (hc : Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) ≤ 2) :
    Nat.card (normalizer (B : Set (Equiv.Perm (Fin 8)))) ∣ 48 := by
  let f := B.normalizerMonoidHom
  have hAut : Nat.card (MulAut B) = 24 := by
    rw [Nat.card_congr (MulAut.congr eB).toEquiv,
      ← Nat.card_congr AlternatingFourPair.eA.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hr : Nat.card f.range ∣ 24 := hAut ▸ f.range.card_subgroup_dvd_card
  have hk : Nat.card f.ker ∣ 2 := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (B : Set (Equiv.Perm (Fin 8))))).toEquiv]
    have hp : 0 < Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) := Nat.card_pos
    have he : Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) = 1 ∨
        Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) = 2 := by omega
    rcases he with he | he <;> simp only [he] <;> decide
  have hcount := f.ker.card_mul_index
  rw [index_ker] at hcount
  rw [← hcount]
  exact Nat.mul_dvd_mul hk hr

/-- Any subgroup of order64 meets this normalizer in index at least four. -/
theorem four_normalizer_relIndex_ge_four
    (B Q : Subgroup (Equiv.Perm (Fin 8))) (eB : B ≃* alternatingGroup (Fin 4))
    (hc : Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) ≤ 2)
    (hQ : Nat.card Q = 64) :
    4 ≤ (normalizer (B : Set (Equiv.Perm (Fin 8)))).relIndex Q := by
  let N := normalizer (B : Set (Equiv.Perm (Fin 8)))
  change 4 ≤ N.relIndex Q
  have hI64 : Nat.card (N ⊓ Q : Subgroup (Equiv.Perm (Fin 8))) ∣ 64 :=
    hQ ▸ card_dvd_of_le (show N ⊓ Q ≤ Q from inf_le_right)
  have hI48 : Nat.card (N ⊓ Q : Subgroup (Equiv.Perm (Fin 8))) ∣ 48 :=
    (card_dvd_of_le (show N ⊓ Q ≤ N from inf_le_left)).trans (four_normalizer_card_dvd B eB hc)
  have hI16 : Nat.card (N ⊓ Q : Subgroup (Equiv.Perm (Fin 8))) ∣ 16 := by
    simpa only [show Nat.gcd 64 48 = 16 from rfl] using Nat.dvd_gcd hI64 hI48
  have hle := Nat.le_of_dvd (by decide : 0 < 16) hI16
  have hcount : Nat.card (N ⊓ Q : Subgroup (Equiv.Perm (Fin 8))) * N.relIndex Q = 64 := by
    simpa only [relIndex_bot_left,inf_relIndex_right,hQ] using
      relIndex_mul_relIndex (⊥ : Subgroup (Equiv.Perm (Fin 8))) (N ⊓ Q) Q bot_le inf_le_right
  by_contra hn
  have hi : N.relIndex Q ≤ 3 := by omega
  have hh := Nat.mul_le_mul hle hi
  rw [hcount] at hh
  norm_num at hh

/-- The small source normalizer index is incompatible with an A₄ having
centralizer of order at most two in S₈. -/
theorem four_normalizer_index_false
    (B Q : Subgroup (Equiv.Perm (Fin 8))) (eB : B ≃* alternatingGroup (Fin 4))
    (hc : Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) ≤ 2)
    (hQ : Nat.card Q = 64)
    (hindex : (normalizer (B : Set (Equiv.Perm (Fin 8)))).relIndex Q ≤ 2) : False := by
  have hh := four_normalizer_relIndex_ge_four B Q eB hc hQ
  omega

/-- The literal image of every inner Sylow two-subgroup has order64. -/
theorem sylow_image_card (P : Sylow 2 (alternatingGroup (Fin 8))) :
    Nat.card ((P : Subgroup (alternatingGroup (Fin 8))).map
      (alternatingGroup (Fin 8)).subtype) = 64 := by
  rw [card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective,P.card_eq_multiplicity]
  have ha : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card,Nat.factorial]
  rw [ha,show 20160 = 2^6*315 from rfl,
    Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

/-- The source bound already fails on an inner Sylow subgroup of A₈. -/
theorem four_normalizer_sylow_index_false
    (B : Subgroup (Equiv.Perm (Fin 8))) (eB : B ≃* alternatingGroup (Fin 4))
    (hc : Nat.card (centralizer (B : Set (Equiv.Perm (Fin 8)))) ≤ 2)
    (P : Sylow 2 (alternatingGroup (Fin 8)))
    (hindex : (normalizer (B : Set (Equiv.Perm (Fin 8)))).relIndex
      ((P : Subgroup (alternatingGroup (Fin 8))).map (alternatingGroup (Fin 8)).subtype) ≤ 2) : False :=
  four_normalizer_index_false B _ eB hc (sylow_image_card P) hindex

end AlternatingEight
end
