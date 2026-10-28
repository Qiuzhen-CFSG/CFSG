module
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# Odd square divisors in paired rank-one Borels

The normalizer of a Sylow two-subgroup in SL₂(F)² is a product of two
rank-one Borels. Its order is |F|²(|F|−1)², so its order contains the
nontrivial odd square used in Aschbacher--Smith 13.6.14, printed p.930.
The argument uses the actual Sylow subgroup, with no chosen coordinates
for its unipotent radicals.
-/

public section
open Subgroup BenderSuzuki.Converse
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "D" => SL(2,F)

private theorem card_rankOne_normalizer (P : Sylow 2 D) :
    Nat.card (normalizer ((P : Subgroup D) : Set D)) = Nat.card F * (Nat.card F - 1) := by
  let Q := P.mapSurjective (f := pi F) (pi_surjective (F := F))
  rw [Nat.card_congr (equivMapOfInjective (normalizer ((P : Subgroup D) : Set D)) (pi F)
    (pi_injective (F := F))).toEquiv]
  rw [map_normalizer_eq_of_bijective (P : Subgroup D)
    ⟨pi_injective (F := F), pi_surjective (F := F)⟩]
  change Nat.card (normalizer ((Q : Subgroup PSL(2,F)) : Set PSL(2,F))) = _
  simpa only [Sylow.coe_coe] using
    (Nat.card_congr (ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F Q).toEquiv).trans
      (ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel F)

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

/-- The actual paired Borel contains the square of the rank-one odd torus order. -/
theorem odd_square_dvd_card_pair_sylow_normalizer (P : Sylow 2 (D × D)) :
    (Nat.card F - 1) ^ 2 ∣ Nat.card (normalizer ((P : Subgroup (D × D)) : Set (D × D))) := by
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
    card_rankOne_normalizer,card_rankOne_normalizer]
  exact ⟨Nat.card F ^ 2,by ring⟩

end Matrix.SpecialLinearGroup
