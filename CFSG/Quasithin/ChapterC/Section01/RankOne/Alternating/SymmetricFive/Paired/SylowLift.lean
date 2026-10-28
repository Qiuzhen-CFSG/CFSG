module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.SylowLift

/-!
# Sylow lifting for one factor of a symmetric-five pair

The actual local and component-product images have orders 96 and 480.
They have the same two-part, so a local Sylow image is already Sylow in
the component product. Saturation in the unchanged kernel lifts this
statement, and the image orders 16 and 32 give the exact index two.

Source: Aschbacher--Smith C.1.24 and E.2.3(3).
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] in
theorem sylowIn_mono {S L K : Subgroup G} (hS : IsPGroup 2 S)
    (hSL : S ≤ L) (hLK : L ≤ K) (hK : IsSylowSubgroupIn S K) :
    IsSylowSubgroupIn S L := by
  obtain ⟨P,hP⟩ := (hS.comap_subtype (K := L)).exists_le_sylow
  have hSP : S ≤ (P : Subgroup L).map L.subtype :=
    fun s hs => ⟨⟨s,hSL hs⟩,hP hs,rfl⟩
  exact ⟨P,sylowIn_maximal hK ((map_subtype_le _).trans hLK)
    (P.isPGroup'.map L.subtype) hSP⟩

omit [Finite G] [Finite H] in
private theorem card_kernel_mul_image (q : G →* H) (A : Subgroup G) :
    Nat.card (q.ker ⊓ A : Subgroup G) * Nat.card (A.map q) = Nat.card A := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ A) A bot_le inf_le_right
  simpa only [relIndex_bot_left,inf_relIndex_right,relIndex_ker] using h

theorem sylow_extension_of_paired_local_image (q : G →* H) (S L I : Subgroup G)
    (hS : IsPGroup 2 S) (hSI : S ≤ I) (hIL : I ≤ L)
    (hScard : Nat.card (S.map q) = 16) (hIcard : Nat.card (I.map q) = 96)
    (hLcard : Nat.card (L.map q) = 480)
    (hk : IsSylowSubgroupIn (S ⊓ q.ker) (L ⊓ q.ker)) :
    ∃ S₁ : Subgroup G, IsSylowSubgroupIn S₁ L ∧ S ≤ S₁ ∧
      (S.subgroupOf S₁).index = 2 ∧ S₁ ≤ I := by
  obtain ⟨P,hP⟩ := (hS.comap_subtype (K := I)).exists_le_sylow
  let S₁ : Subgroup G := (P : Subgroup I).map I.subtype
  have hS₁I : S₁ ≤ I := map_subtype_le _
  have hS₁L := hS₁I.trans hIL
  have hSS₁ : S ≤ S₁ := fun s hs => ⟨⟨s,hSI hs⟩,hP hs,rfl⟩
  have hS₁ : IsPGroup 2 S₁ := P.isPGroup'.map I.subtype
  let Q := P.mapSurjective (f := q.subgroupMap I) (q.subgroupMap_surjective I)
  have hQ : (Q : Subgroup (I.map q)).map (I.map q).subtype = S₁.map q := by
    rw [Sylow.coe_mapSurjective,map_map,map_map]
    rfl
  have hQcard : Nat.card Q = 32 := by
    have h := Q.card_eq_multiplicity
    rw [hIcard,show (96 : ℕ).factorization 2 = 5 by
      rw [show 96 = 2^5*3 by norm_num,Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2∣3)]] at h
    exact h
  have hS₁card : Nat.card (S₁.map q) = 32 := by
    rw [←hQ,card_map_of_injective (I.map q).subtype_injective]
    exact hQcard
  let A := (S₁.map q).subgroupOf (L.map q)
  have hAcard : Nat.card A = 32 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_mono hS₁L)).toEquiv]
    exact hS₁card
  let R : Sylow 2 (L.map q) := Sylow.ofCard A (by
    rw [hAcard,hLcard,show (480 : ℕ).factorization 2 = 5 by
      rw [show 480 = 2^5*15 by norm_num,Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2∣15)]]
    norm_num)
  have hi : IsSylowSubgroupIn (S₁.map q) (L.map q) := by
    refine ⟨R,?_⟩
    change A.map (L.map q).subtype = S₁.map q
    exact map_subgroupOf_eq_of_le (map_mono hS₁L)
  have hkernel : S₁ ⊓ q.ker = S ⊓ q.ker := sylowIn_maximal hk
    (inf_le_inf_right _ hS₁L) (hS₁.to_le inf_le_left) (inf_le_inf_right _ hSS₁)
  have hk₁ : IsSylowSubgroupIn (S₁ ⊓ q.ker) (L ⊓ q.ker) := hkernel ▸ hk
  have hsyl := sylowIn_of_image_and_kernel q S₁ L hS₁L hS₁ hk₁ hi
  refine ⟨S₁,hsyl,hSS₁,?_,hS₁I⟩
  have hcS := card_kernel_mul_image q S
  have hcS₁ := card_kernel_mul_image q S₁
  have hker' : q.ker ⊓ S₁ = q.ker ⊓ S := by simpa only [inf_comm] using hkernel
  rw [hScard] at hcS
  rw [hS₁card,hker'] at hcS₁
  have hrel := relIndex_mul_relIndex (⊥ : Subgroup G) S S₁ bot_le hSS₁
  rw [relIndex_bot_left,relIndex_bot_left,←hcS,←hcS₁] at hrel
  have hn : 0 < Nat.card (q.ker ⊓ S : Subgroup G) := Nat.card_pos
  change S.relIndex S₁ = 2
  nlinarith
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
