module
public import Theory.SpecificGroups.SL2.SylowNormalizerCard

/-!
# Odd subgroup orders in the actual paired Borel

The prescribed Sylow normalizer in SL₂(F)² has order |F|²(|F|−1)².
Cancelling its two-part bounds every odd subgroup by the square torus order.
This applies to original odd Hall subgroups after their literal quotient map.
Source application: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "D" => SL(2,F)

private theorem normalizer_product {A B : Type*} [Group A] [Group B]
    (P : Subgroup A) (Q : Subgroup B) :
    normalizer (P.prod Q : Set (A × B)) =
      (normalizer (P : Set A)).prod (normalizer (Q : Set B)) := by
  ext g
  simp only [Subgroup.mem_prod, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    exact ⟨fun x => by simpa using h (x,1),fun y => by simpa using h (1,y)⟩
  · rintro ⟨hP,hQ⟩ ⟨x,y⟩
    exact (hP x).and (hQ y)

/-- The full order of the normalizer of the prescribed paired Sylow subgroup. -/
theorem card_pair_sylow_normalizer_even (P : Sylow 2 (D × D)) :
    Nat.card (normalizer ((P : Subgroup (D × D)) : Set (D × D))) =
      Nat.card F ^ 2 * (Nat.card F - 1) ^ 2 := by
  let Q := P.mapSurjective (f := MonoidHom.fst D D) (fun x => ⟨(x,1),rfl⟩)
  let R := P.mapSurjective (f := MonoidHom.snd D D) (fun x => ⟨(1,x),rfl⟩)
  have htwo : IsPGroup 2 ((Q : Subgroup D).prod (R : Subgroup D)) := by
    obtain ⟨a,ha⟩ := Q.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := R.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a+b) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add])
  have hle : (P : Subgroup (D × D)) ≤ (Q : Subgroup D).prod (R : Subgroup D) := by
    intro x hx
    exact ⟨mem_map_of_mem (MonoidHom.fst D D) hx,mem_map_of_mem (MonoidHom.snd D D) hx⟩
  have he : (P : Subgroup (D × D)) = (Q : Subgroup D).prod (R : Subgroup D) :=
    (P.is_maximal' htwo hle).symm
  rw [show ((P : Subgroup (D × D)) : Set (D × D)) = ((Q : Subgroup D).prod (R : Subgroup D) : Set _) from congrArg SetLike.coe he,
    normalizer_product,Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
    card_sylow_normalizer_even,card_sylow_normalizer_even]
  ring

/-- An odd subgroup of the paired Sylow normalizer divides its torus order. -/
theorem odd_card_dvd_pair_torus_order
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (P : Sylow 2 (D × D)) (B : Subgroup (D × D))
    (hBN : B ≤ normalizer ((P : Subgroup (D × D)) : Set (D × D)))
    (hodd : Odd (Nat.card B)) : Nat.card B ∣ (Nat.card F - 1)^2 := by
  have hd := card_dvd_of_le hBN
  rw [card_pair_sylow_normalizer_even] at hd
  have hc : Nat.Coprime (Nat.card B) (Nat.card F ^ 2) := by
    rw [hF]
    exact (hodd.coprime_two_right.pow_right n).pow_right 2
  exact hc.dvd_of_dvd_mul_left hd

end Matrix.SpecialLinearGroup
