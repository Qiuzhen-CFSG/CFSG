module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.LocalGeometry
public import Stellmacher.BaumannNormalizer
import Mathlib.Tactic

/-!
# Lifting the local S₄ image to an index-two Sylow extension

Choose a Sylow subgroup of the actual conjugate span containing the Baumann
subgroup. Its S₄ image has order eight, hence is already Sylow in S₅. Sylow
saturation in the action kernel lifts maximality to the original group. The
unchanged kernel and image orders four and eight give index two.

Source: Aschbacher–Smith, the S₅ argument in 3.1.7, printed pp.575–576.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.SymmetricFive
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem sylowIn_maximal {H S T : Subgroup G}
    (hS : IsSylowSubgroupIn S H) (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hST : S ≤ T) : T = S := by
  obtain ⟨P, hP⟩ := hS
  have hPT : (P : Subgroup H) ≤ T.subgroupOf H := by
    intro x hx
    exact hST (hP ▸ mem_map_of_mem H.subtype hx)
  have he := P.is_maximal' (hT.comap_subtype (K := H)) hPT
  have hm := congrArg (map H.subtype) he
  change (T.subgroupOf H).map H.subtype = (P : Subgroup H).map H.subtype at hm
  rwa [map_subgroupOf_eq_of_le hTH, hP] at hm

omit [Finite G] in
theorem sylowIn_of_image_and_kernel {K : Type*} [Group K]
    (f : G →* K) (S H : Subgroup G) (hSH : S ≤ H) (hS : IsPGroup 2 S)
    (hk : IsSylowSubgroupIn (S ⊓ f.ker) (H ⊓ f.ker))
    (hi : IsSylowSubgroupIn (S.map f) (H.map f)) : IsSylowSubgroupIn S H := by
  obtain ⟨P, hP⟩ := (hS.comap_subtype (K := H)).exists_le_sylow
  let T := (P : Subgroup H).map H.subtype
  have hTH : T ≤ H := map_subtype_le _
  have hT : IsPGroup 2 T := P.isPGroup'.map H.subtype
  have hST : S ≤ T := by
    intro s hs
    exact ⟨⟨s, hSH hs⟩, hP hs, rfl⟩
  have hi_eq : T.map f = S.map f := sylowIn_maximal hi (map_mono hTH)
    (hT.map f) (map_mono hST)
  have hk_eq : T ⊓ f.ker = S ⊓ f.ker := sylowIn_maximal hk
    (inf_le_inf_right _ hTH) (hT.to_le inf_le_left) (inf_le_inf_right _ hST)
  refine ⟨P, le_antisymm ?_ hST⟩
  intro t ht
  obtain ⟨s, hs, hst⟩ := hi_eq ▸ mem_map_of_mem f ht
  have hmem : s⁻¹ * t ∈ T ⊓ f.ker := by
    refine ⟨T.mul_mem (T.inv_mem (hST hs)) ht, ?_⟩
    change f (s⁻¹ * t) = 1
    rw [map_mul, map_inv, hst, inv_mul_cancel]
  have hz : s⁻¹ * t ∈ S := (hk_eq ▸ hmem).1
  simpa using S.mul_mem hs hz


omit [Finite G] in
private theorem card_kernel_mul_image (q : G →* Sym) (A : Subgroup G) :
    Nat.card (q.ker ⊓ A : Subgroup G) * Nat.card (A.map q) = Nat.card A := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (q.ker ⊓ A) A bot_le inf_le_right
  simpa only [relIndex_bot_left, inf_relIndex_right, relIndex_ker] using h

/-- A local point-stabilizer image and Sylow saturation in the kernel supply
an actual index-two Sylow extension inside the specified subgroup. -/
theorem sylow_extension_of_local_image (q : G →* Sym) (S L I : Subgroup G)
    (hS : IsPGroup 2 S) (hSI : S ≤ I) (hIL : I ≤ L)
    (hScard : Nat.card (S.map q) = 4) (hIcard : Nat.card (I.map q) = 24)
    (hk : IsSylowSubgroupIn (S ⊓ q.ker) (L ⊓ q.ker)) :
    ∃ S₁ : Subgroup G, IsSylowSubgroupIn S₁ L ∧ S ≤ S₁ ∧
      (S.subgroupOf S₁).index = 2 ∧ S₁ ≤ I := by
  obtain ⟨P, hP⟩ := (hS.comap_subtype (K := I)).exists_le_sylow
  let S₁ : Subgroup G := (P : Subgroup I).map I.subtype
  have hS₁I : S₁ ≤ I := map_subtype_le _
  have hS₁L := hS₁I.trans hIL
  have hSS₁ : S ≤ S₁ := by
    intro s hs
    exact ⟨⟨s, hSI hs⟩, hP hs, rfl⟩
  have hS₁ : IsPGroup 2 S₁ := P.isPGroup'.map I.subtype
  let Q := P.mapSurjective (f := q.subgroupMap I) (q.subgroupMap_surjective I)
  have hQ : (Q : Subgroup (I.map q)).map (I.map q).subtype = S₁.map q := by
    rw [Sylow.coe_mapSurjective, map_map, map_map]
    rfl
  have hQcard : Nat.card Q = 8 := by
    have h := Q.card_eq_multiplicity
    rw [hIcard, show (24 : ℕ).factorization 2 = 3 by
      rw [show 24 = 2 ^ 3 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]] at h
    exact h
  have hS₁card : Nat.card (S₁.map q) = 8 := by
    rw [← hQ, card_map_of_injective (I.map q).subtype_injective]
    exact hQcard
  have hSym : Nat.card Sym = 120 := by
    norm_num [Sym, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let R : Sylow 2 Sym := Sylow.ofCard (S₁.map q) (by
    rw [hS₁card, hSym]
    rw [show (120 : ℕ).factorization 2 = 3 by
      rw [show 120 = 2 ^ 3 * 15 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 15)]]
    norm_num)
  have hi : IsSylowSubgroupIn (S₁.map q) (L.map q) := by
    have hR : (R : Subgroup Sym) = S₁.map q := rfl
    have hRL : (R : Subgroup Sym) ≤ L.map q := hR ▸ map_mono hS₁L
    refine ⟨R.subtype hRL, ?_⟩
    rw [Sylow.coe_subtype, hR, map_subgroupOf_eq_of_le (map_mono hS₁L)]
  have hkernel : S₁ ⊓ q.ker = S ⊓ q.ker := sylowIn_maximal hk
    (inf_le_inf_right _ hS₁L) (hS₁.to_le inf_le_left) (inf_le_inf_right _ hSS₁)
  have hk₁ : IsSylowSubgroupIn (S₁ ⊓ q.ker) (L ⊓ q.ker) := hkernel ▸ hk
  have hsyl := sylowIn_of_image_and_kernel q S₁ L hS₁L hS₁ hk₁ hi
  refine ⟨S₁, hsyl, hSS₁, ?_, hS₁I⟩
  have hcS := card_kernel_mul_image q S
  have hcS₁ := card_kernel_mul_image q S₁
  have hker' : q.ker ⊓ S₁ = q.ker ⊓ S := by simpa only [inf_comm] using hkernel
  rw [hScard] at hcS
  rw [hS₁card, hker'] at hcS₁
  have hrel := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) S S₁ bot_le hSS₁
  rw [relIndex_bot_left, relIndex_bot_left, ← hcS, ← hcS₁] at hrel
  have hn : 0 < Nat.card (q.ker ⊓ S : Subgroup G) := Nat.card_pos
  change S.relIndex S₁ = 2
  nlinarith
end CFSG.Quasithin.ChapterC.SymmetricFive
