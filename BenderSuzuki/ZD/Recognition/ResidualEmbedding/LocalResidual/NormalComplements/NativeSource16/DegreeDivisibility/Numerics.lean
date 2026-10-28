module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.DegreeDivisibility.RootNormalizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Canceling the pair Sylow factor in the source normalizer count

A normalizing two-subgroup P disjoint from a Sylow two-subgroup S of D
contributes |P||S| to the centralizer of u in the source normalizer N. Its
orbit has |Q| elements, so |Q||P||S| divides |M|. The odd index of S in D
can be canceled, giving |Q||P| dividing [M:D]. All products are literal
subgroup products; no Sylow-order inequality substitutes for divisibility.

Source: GLS IV, Chapter 2, Lemma 16.4(c), final paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem binary_factor_dvd_relIndex
    (M D : Subgroup G) (hDM : D ≤ M) (S : Sylow 2 D) {k : ℕ}
    (hdiv : 2 ^ k * Nat.card S ∣ Nat.card M) : 2 ^ k ∣ D.relIndex M := by
  have hM := relIndex_mul_relIndex (⊥ : Subgroup G) D M bot_le hDM
  simp only [relIndex_bot_left] at hM
  have hD := (S : Subgroup D).card_mul_index
  have he : Nat.card M = (D.relIndex M * (S : Subgroup D).index) * Nat.card S := by
    rw [← hM, ← hD]
    ring
  rw [he] at hdiv
  have hd := Nat.dvd_of_mul_dvd_mul_right (Nat.card_pos (α := S)) hdiv
  exact (Nat.prime_two.coprime_pow_of_not_dvd S.not_dvd_index).symm.dvd_of_dvd_mul_right hd

/-- The source orbit count, together with actual normalizing subgroups of its
centralizer, gives the required two-power divisor of [M:D]. -/
public theorem source16_root_product_dvd_pair_index
    (M D N P Q : Subgroup G) (u : G)
    (hDM : D ≤ M) (hNM : N ≤ M) (S : Sylow 2 D)
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q)
    (hPC : P ≤ N ⊓ centralizer ({u} : Set G))
    (hSC : (S : Subgroup D).map D.subtype ≤ N ⊓ centralizer ({u} : Set G))
    (hSP : (S : Subgroup D).map D.subtype ≤ normalizer (P : Set G))
    (hPD : Disjoint P D)
    (horbit : (centralizer ({u} : Set G)).relIndex N = Nat.card Q) :
    Nat.card Q * Nat.card P ∣ D.relIndex M := by
  let S₀ := (S : Subgroup D).map D.subtype
  let C := N ⊓ centralizer ({u} : Set G)
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint P S₀ hSP
    (hPD.mono_right (map_subtype_le _))
  have hd : Nat.card P * Nat.card S ∣ Nat.card C := by
    have hh := card_dvd_of_le (sup_le hPC hSC)
    rw [hprod, card_map_of_injective D.subtype_injective] at hh
    exact hh
  have hN := relIndex_mul_relIndex (⊥ : Subgroup G) C N bot_le inf_le_left
  simp only [relIndex_bot_left] at hN
  have hCi : C.relIndex N = Nat.card Q := (inf_relIndex_left N _).trans horbit
  rw [hCi] at hN
  have ht : (Nat.card Q * Nat.card P) * Nat.card S ∣ Nat.card M := by
    apply dvd_trans _ (card_dvd_of_le hNM)
    rw [← hN]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_dvd_mul_left (Nat.card Q) hd
  obtain ⟨a,ha⟩ := hQ.exists_card_eq
  obtain ⟨b,hb⟩ := hP.exists_card_eq
  rw [ha,hb,← pow_add] at ht ⊢
  exact binary_factor_dvd_relIndex M D hDM S ht

end BenderSuzuki.ZD
