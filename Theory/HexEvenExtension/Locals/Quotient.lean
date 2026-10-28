module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals.Recognition
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Faithful local vertices in a cubic cover of S₆

Two order-48 subgroups generating a cubic cover of S₆ and containing a
common Sylow of order 16 must each inject into the quotient. Otherwise
one image has order 16 and equals the common Sylow image; generation
would force the whole quotient into the other image of order at most 48.
The surviving images are the original index-three Sylow overgroups.
The established duad/syntheme geometry identifies them with C₂ × S₄.

This argument uses the literal quotient homomorphism and original local
subgroups; it makes no local characteristic-two or splitting assumption.
Source: Aschbacher–Smith, F.6.18(8), printed p.310, and I.5.
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
namespace Theory.HexEvenExtension.Locals
variable {G : Type*} [Group G] [Finite G]

private theorem card_sixteen_or_fortyeight {n : ℕ} (hn : n ∣ 48) (h16 : 16 ∣ n) :
    n = 16 ∨ n = 48 := by
  have hm := Nat.mem_divisors.mpr ⟨hn, by decide⟩
  have hd : (48 : ℕ).divisors = {1,2,3,4,6,8,12,16,24,48} := by decide
  rw [hd] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  obtain ⟨k,hk⟩ := h16
  omega

/-- Both original local subgroups retain order 48 in the actual quotient. -/
theorem vertex_image_cards (f : G →* S6) (hf : Function.Surjective f)
    (hker : Nat.Coprime 2 (Nat.card f.ker)) (T : Sylow 2 G)
    (hT : Nat.card T = 16) (A B : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hA : Nat.card A = 48) (hB : Nat.card B = 48) (hgen : A ⊔ B = ⊤) :
    Nat.card (A.map f) = 48 ∧ Nat.card (B.map f) = 48 := by
  let S := T.mapSurjective hf
  have hS : Nat.card S = 16 :=
    (Nat.card_congr (T.equivOfSurjectiveCoprime f hf hker S).symm.toEquiv).trans hT
  have hSA : (S : Subgroup S6) ≤ A.map f := map_mono hTA
  have hSB : (S : Subgroup S6) ≤ B.map f := map_mono hTB
  have ha : Nat.card (A.map f) = 16 ∨ Nat.card (A.map f) = 48 :=
    card_sixteen_or_fortyeight (hA ▸ A.card_map_dvd f) (hS ▸ card_dvd_of_le hSA)
  have hb : Nat.card (B.map f) = 16 ∨ Nat.card (B.map f) = 48 :=
    card_sixteen_or_fortyeight (hB ▸ B.card_map_dvd f) (hS ▸ card_dvd_of_le hSB)
  have hsup : A.map f ⊔ B.map f = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective f hf]
  have collapse (X Y : Subgroup S6) (hSX : (S : Subgroup S6) ≤ X)
      (hSY : (S : Subgroup S6) ≤ Y) (hc : Nat.card X = 16)
      (hY : Nat.card Y ≤ 48) (hXY : X ⊔ Y = ⊤) : False := by
    have he : (S : Subgroup S6) = X := eq_of_le_of_card_ge hSX (by rw [hS,hc])
    have hy : Y = ⊤ := by simpa only [sup_eq_right.mpr (he ▸ hSY)] using hXY
    rw [hy, card_top] at hY
    have h720 : Nat.card S6 = 720 := by
      simp [S6, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    omega
  constructor
  · exact ha.resolve_left (fun hc => collapse _ _ hSA hSB hc (by omega) hsup)
  · exact hb.resolve_left (fun hc => collapse _ _ hSB hSA hc (by omega) ((sup_comm (B.map f) (A.map f)).trans hsup))

/-- The quotient restricts bijectively to each original vertex image. -/
theorem vertex_quotient_bijective (f : G →* S6) (hf : Function.Surjective f)
    (hker : Nat.Coprime 2 (Nat.card f.ker)) (T : Sylow 2 G)
    (hT : Nat.card T = 16) (A B : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hA : Nat.card A = 48) (hB : Nat.card B = 48) (hgen : A ⊔ B = ⊤) :
    Function.Bijective (f.subgroupMap A) ∧ Function.Bijective (f.subgroupMap B) := by
  obtain ⟨ha,hb⟩ := vertex_image_cards f hf hker T hT A B hTA hTB hA hB hgen
  exact ⟨(f.subgroupMap_surjective A).bijective_of_nat_card_le (by rw [ha,hA]),
    (f.subgroupMap_surjective B).bijective_of_nat_card_le (by rw [hb,hB])⟩

/-- A literal index-three Sylow overgroup in S₆ is C₂ × S₄. -/
theorem local_equiv (S : Sylow 2 S6) (A : Subgroup S6)
    (hSA : (S : Subgroup S6) ≤ A) (hi : (S : Subgroup S6).relIndex A = 3) :
    Nonempty (A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  obtain ⟨hc,hcS,hcA,hd,⟨eA⟩,_⟩ := ComponentLocals.local_structure S A hSA hi
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _
    (hd.mono_right (show A ⊓ A6 ≤ A6 from inf_le_right))
    (hcA.trans (centralizer_le (show A ⊓ A6 ≤ A from inf_le_left)))
  let eC := mulEquivOfPrimeCardEq (p := 2) hc
    (by simp [Nat.card_eq_fintype_card] : Nat.card (Multiplicative (ZMod 2)) = 2)
  exact ⟨((e.trans (MulEquiv.subgroupCongr (ComponentLocals.local_product S A hSA hi))).symm).trans
    (eC.prodCongr eA)⟩

/-- Both original local vertices are C₂ × S₄, through their literal quotient images. -/
theorem vertices_equiv (f : G →* S6) (hf : Function.Surjective f)
    (hker : Nat.Coprime 2 (Nat.card f.ker)) (T : Sylow 2 G)
    (hT : Nat.card T = 16) (A B : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (hA : Nat.card A = 48) (hB : Nat.card B = 48) (hgen : A ⊔ B = ⊤) :
    Nonempty (A ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (B ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) := by
  obtain ⟨ha,hb⟩ := vertex_image_cards f hf hker T hT A B hTA hTB hA hB hgen
  obtain ⟨hia,hib⟩ := vertex_quotient_bijective f hf hker T hT A B hTA hTB hA hB hgen
  let S := T.mapSurjective hf
  have hS : Nat.card S = 16 :=
    (Nat.card_congr (T.equivOfSurjectiveCoprime f hf hker S).symm.toEquiv).trans hT
  have idx (X : Subgroup S6) (hSX : (S : Subgroup S6) ≤ X) (hx : Nat.card X = 48) :
      (S : Subgroup S6).relIndex X = 3 := by
    have hh := ((S : Subgroup S6).subgroupOf X).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hSX).toEquiv, hS, hx] at hh
    change ((S : Subgroup S6).subgroupOf X).index = 3
    omega
  obtain ⟨ea⟩ := local_equiv S (A.map f) (map_mono hTA) (idx _ (map_mono hTA) ha)
  obtain ⟨eb⟩ := local_equiv S (B.map f) (map_mono hTB) (idx _ (map_mono hTB) hb)
  exact ⟨⟨(MulEquiv.ofBijective (f.subgroupMap A) hia).trans ea⟩,
    ⟨(MulEquiv.ofBijective (f.subgroupMap B) hib).trans eb⟩⟩

end Theory.HexEvenExtension.Locals
