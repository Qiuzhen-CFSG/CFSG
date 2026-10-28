module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.OddNormal
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# The Sylow subgroup and solvability of the prime-to-three core

For a Goldschmidt triple, the local symmetric-three quotients give
`Gᵢ ∩ O₃′(G) ≤ O₂(Gᵢ)`. The common-normal-core argument then identifies
both intersections with `O₂(G)`. Restricting the common Sylow subgroup
to the normal core gives an actual Sylow witness. F.6.8 and extension
closure of solvability prove that the whole prime-to-three core is solvable.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.11(1), printed p.306 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G]

theorem twoCore_le_primeToThreeCore : pCore 2 G ≤ pPrimeCore 3 G := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  rw [hn]
  exact (show Nat.Coprime 3 2 by decide).pow_right n

private theorem symmetricThree_primeToThreeCore_eq_bot :
    pPrimeCore 3 (Equiv.Perm (Fin 3)) = ⊥ := by
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd := (pPrimeCore 3 (Equiv.Perm (Fin 3))).card_subgroup_dvd_card
  rw [hc] at hd
  have hd2 : Nat.card (pPrimeCore 3 (Equiv.Perm (Fin 3))) ∣ 2 :=
    pPrimeCore_coprime_card.symm.dvd_mul_right.mp hd
  have hp : IsPGroup 2 (pPrimeCore 3 (Equiv.Perm (Fin 3))) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by simpa using h1)
    · exact IsPGroup.of_card (n := 1) (by simpa using h2)
  have he : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    simpa using (ker_eq_twoCore_of_surjective_perm_three
      (MonoidHom.id (Equiv.Perm (Fin 3))) Function.surjective_id
      (by rw [MonoidHom.ker_id]; exact IsPGroup.of_bot)).symm
  exact le_bot_iff.mp ((show pPrimeCore 3 (Equiv.Perm (Fin 3)) ≤
    pCore 2 (Equiv.Perm (Fin 3)) from le_sSup ⟨inferInstance, hp⟩).trans he.le)

theorem primeToThreeCore_eq_twoCore_of_symmetric_quotient
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) :
    pPrimeCore 3 G = pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have he : pPrimeCore 3 (G ⧸ pCore 2 G) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pPrimeCore_map_iso, symmetricThree_primeToThreeCore_eq_bot, Subgroup.map_bot]
  have hker : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have h := pPrimeCore_comap_eq_of_surjective_coprime 3 q
    (QuotientGroup.mk'_surjective _) hker
  rw [he] at h
  exact h.symm.trans (QuotientGroup.ker_mk' _)

variable {G₁ G₂ : Subgroup G}

theorem IsGoldschmidtTriple.left_inf_primeToThreeCore_le
    (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ pPrimeCore 3 G ≤ (pCore 2 G₁).map G₁.subtype := by
  obtain ⟨e⟩ := h.quotient_left
  have hn : (pPrimeCore 3 G).subgroupOf G₁ ≤ pPrimeCore 3 G₁ := by
    apply le_sSup
    exact ⟨inferInstance, pPrimeCore_coprime_card.of_dvd_right
      (card_comap_dvd_of_injective _ _ G₁.subtype_injective)⟩
  rw [primeToThreeCore_eq_twoCore_of_symmetric_quotient e] at hn
  rintro x ⟨hx, hX⟩
  exact mem_map.mpr ⟨⟨x, hx⟩, hn hX, rfl⟩

theorem IsGoldschmidtTriple.intersection_inf_primeToThreeCore
    (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁ ⊓ G₂) ⊓ pPrimeCore 3 G = pCore 2 G := by
  exact le_antisymm
    (h.normal_intersection_le_twoCore _ h.left_inf_primeToThreeCore_le
      h.symm.left_inf_primeToThreeCore_le)
    (le_inf h.twoCore_isGreatest.1.1 twoCore_le_primeToThreeCore)

theorem IsGoldschmidtTriple.left_inf_primeToThreeCore
    (h : IsGoldschmidtTriple G₁ G₂) : G₁ ⊓ pPrimeCore 3 G = pCore 2 G := by
  exact ((h.left_intersection_eq_core_intersection _
    h.left_inf_primeToThreeCore_le).1.trans
    (h.left_intersection_eq_core_intersection _ h.left_inf_primeToThreeCore_le).2).trans
    h.intersection_inf_primeToThreeCore

theorem IsGoldschmidtTriple.right_inf_primeToThreeCore
    (h : IsGoldschmidtTriple G₁ G₂) : G₂ ⊓ pPrimeCore 3 G = pCore 2 G :=
  h.symm.left_inf_primeToThreeCore

theorem IsGoldschmidtTriple.primeToThreeCore_sylow
    (h : IsGoldschmidtTriple G₁ G₂) :
    ∃ S : Sylow 2 (pPrimeCore 3 G),
      (S : Subgroup (pPrimeCore 3 G)).map (pPrimeCore 3 G).subtype = pCore 2 G := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal (pPrimeCore 3 G)
  refine ⟨S, ?_⟩
  rw [hS, subgroupOf_map_subtype, ← hT, h.intersection_inf_primeToThreeCore]

theorem IsGoldschmidtTriple.primeToThreeCore_solvable
    (h : IsGoldschmidtTriple G₁ G₂) : Group.IsSolvable (pPrimeCore 3 G) := by
  let X := pPrimeCore 3 G
  let K := (pCore 2 G).subgroupOf X
  let _ : Group.IsNilpotent K :=
    (pCore_isPGroup (p := 2) (G := G)).comap_subtype.isNilpotent
  have hs : Group.IsSolvable (X ⧸ K) := by
    have hs := h.normal_quotient_solvable X h.left_inf_primeToThreeCore_le
      h.symm.left_inf_primeToThreeCore_le
    have hsup : X ⊔ pCore 2 G = X := sup_eq_left.mpr twoCore_le_primeToThreeCore
    rw [hsup] at hs
    exact hs
  exact (Group.isSolvable_iff_subgroup_quotient K).mpr ⟨inferInstance, hs⟩

/-- Lemma F.6.11(1), retaining the Sylow subgroup and its ambient image. -/
theorem IsGoldschmidtTriple.primeToThreeCore_structure
    (h : IsGoldschmidtTriple G₁ G₂) :
    (∃ S : Sylow 2 (pPrimeCore 3 G),
      (S : Subgroup (pPrimeCore 3 G)).map (pPrimeCore 3 G).subtype = pCore 2 G) ∧
      Group.IsSolvable (pPrimeCore 3 G) :=
  ⟨h.primeToThreeCore_sylow, h.primeToThreeCore_solvable⟩

end CFSG.Quasithin.ChapterF
