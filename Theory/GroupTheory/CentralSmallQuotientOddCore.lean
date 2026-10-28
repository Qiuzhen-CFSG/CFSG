module

public import Theory.GroupTheory.CentralS3InvolutionComplement
public import Theory.PGroupCore

/-!
# Odd normal core from a small central quotient

If a finite normal subgroup has a central kernel of order at most two and
quotient of order six, its unique Sylow three subgroup is characteristic in
the normal subgroup.  It therefore embeds as a nontrivial normal odd-order
subgroup of the ambient group, so the ambient 2-prime core is nontrivial.

This is the central-extension input used in the centered radius-one branch of
Goldschmidt's local analysis.
-/

namespace Subgroup

/-- A central extension of a group of order six supplies a normal cubic
subgroup of the ambient group, lying in its 2-prime core. -/
public theorem exists_normal_cubic_subgroup_of_central_small_quotient
    {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal]
    (Z : Subgroup K) [Z.Normal] (hZ : Z ≤ center K)
    (hZcard : Nat.card Z ≤ 2) (hquot : Nat.card (K ⧸ Z) = 6) :
    ∃ N : Subgroup H, N.Normal ∧ Nat.card N = 3 ∧ N ≤ pPrimeCore 2 H := by
  classical
  have hKcard : Nat.card K = 6 * Nat.card Z := by
    rw [card_eq_card_quotient_mul_card_subgroup Z, hquot]
  let P : Sylow 3 K := Sylow.nonempty.some
  obtain ⟨hPcard, hPnormal⟩ :=
    central_small_sylow_three_normal Z hZ hZcard hKcard P
  let : (P : Subgroup K).Characteristic := P.characteristic_of_normal hPnormal
  let N : Subgroup H := (P : Subgroup K).map K.subtype
  have hNnormal : N.Normal := inferInstance
  have hNcard : Nat.card N = 3 :=
    (card_map_of_injective K.subtype_injective).trans hPcard
  have hNle : N ≤ pPrimeCore 2 H :=
    le_sSup ⟨hNnormal, by rw [hNcard]; decide⟩
  exact ⟨N, hNnormal, hNcard, hNle⟩

/-- A central extension of a group of order six has a nontrivial ambient
2-prime core, when the extension is normal in the ambient finite group. -/
public theorem pPrimeCore_ne_bot_of_central_small_quotient
    {H : Type*} [Group H] [Finite H]
    (K : Subgroup H) [K.Normal]
    (Z : Subgroup K) [Z.Normal] (hZ : Z ≤ center K)
    (hZcard : Nat.card Z ≤ 2) (hquot : Nat.card (K ⧸ Z) = 6) :
    pPrimeCore 2 H ≠ ⊥ := by
  obtain ⟨N, hNnormal, hNcard, hNle⟩ :=
    exists_normal_cubic_subgroup_of_central_small_quotient K Z hZ hZcard hquot
  intro hcore
  have hNbot : N = ⊥ := le_bot_iff.mp (hcore ▸ hNle)
  rw [hNbot, card_bot] at hNcard
  omega

end Subgroup
