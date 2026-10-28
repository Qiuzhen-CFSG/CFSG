module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers.Pairing
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers.Cubic
import Mathlib.Tactic

/-!
# Four-group normalizer geometry in odd PSL₂

The order-eight exhaustion and the recovery of an S₄ overgroup as the
normalizer of its intrinsic normal four-group are unconditional for the
actual odd-field PSL₂ model. The prime-field wrappers below discharge the
remaining normalizer identification and pairing from the explicit matrix
input that each four-group normalizer contains an element of order three.

Self-centrality bounds normalizers by 24; the order-eight overlap and cubic
force equality and the actual S₄ isomorphism. The paired actor is nonnormal
in the selected normalizer, so the two normalizers are distinct. The final
consumer applies `Inner.local_witness_of_symmetric_four` to this literal
normalizer as soon as it escapes the proposed overgroup M. It retains the
literal Sylow intersection, including when T has order greater than eight.

Source: Aschbacher--Smith E.1.2 and E.1.14(6), printed pp.209--210 and 214,
the latter citing Asc82a Lemma 4.10. No four-group conjugacy assertion is used.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
namespace SymmetricNormalizers
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite G] in
private theorem prime_field_cubic
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p)
    (e : G ≃* PSL2 F) (B : Subgroup G) (hB : IsKleinFour B) :
    ∃ x : normalizer (B : Set G), orderOf x = 3 := by
  have hodd : Odd (Nat.card F) := by simpa [hFcard] using hpodd
  let V : Subgroup (PSL2 F) := B.map e.toMonoidHom
  have hV : IsKleinFour V := by
    exact GorensteinWalter.isKleinFour_map_of_injective B hB e.toMonoidHom e.injective
  obtain ⟨y, hy⟩ := Cubic.exists_order_three_of_odd_card hodd V hV
  have hmap : (normalizer (B : Set G)).map e.toMonoidHom =
      normalizer (V : Set (PSL2 F)) := by
    exact Subgroup.map_equiv_normalizer_eq B e
  have hmem : e.symm (y : PSL2 F) ∈ normalizer (B : Set G) := by
    have hpre : e.symm (y : PSL2 F) ∈
        Subgroup.comap e.toMonoidHom ((normalizer (B : Set G)).map e.toMonoidHom) := by
      change e (e.symm (y : PSL2 F)) ∈ (normalizer (B : Set G)).map e.toMonoidHom
      rw [hmap, e.apply_symm_apply]
      exact y.property
    rw [Subgroup.comap_map_eq_self_of_injective e.injective] at hpre
    exact hpre
  have hy' : orderOf (y : PSL2 F) = 3 :=
    (Subgroup.orderOf_mk (y : PSL2 F) y.property).symm.trans hy
  have hxord : orderOf (e.symm (y : PSL2 F)) = 3 :=
    (orderOf_injective e.symm.toMonoidHom e.symm.injective (y : PSL2 F)).trans hy'
  exact ⟨⟨e.symm (y : PSL2 F), hmem⟩, by rw [Subgroup.orderOf_mk]; exact hxord⟩

omit [Field F] [Finite F] in
private theorem prime_field_odd_prime_power
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p) :
    IsOddPrimePower (Nat.card F) :=
  ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hFcard⟩
omit [Finite G] in
private theorem selfCentralizing (hF : IsOddPrimePower (Nat.card F))
    (e : G ≃* PSL2 F) (B : Subgroup G) (hB : IsKleinFour B) :
    centralizer (B : Set G) = B :=
  kleinFour_selfCentralizing_of_embedding hF
    (Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom)
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective) B hB

theorem normalizer_equiv_symmetric_four_of_order_three
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (B : Subgroup G) (hB : IsKleinFour B) (hBT : B ≤ T)
    (hcubic : ∃ x : normalizer (B : Set G), orderOf x = 3) :
    Nonempty (normalizer (B : Set G) ≃* Equiv.Perm (Fin 4)) := by
  let := hB
  exact normalizer_equiv_of_cubic T hT B hBT (selfCentralizing hF e B hB) hcubic

/-- The literal normalizer in an odd prime-field PSL₂ model contains the
order-three element supplied by the matrix calculation, so its faithful
four-point action is the actual S₄ normalizer. -/
theorem normalizer_equiv_symmetric_four_of_prime_field
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (B : Subgroup G) (hB : IsKleinFour B) (hBT : B ≤ T) :
    Nonempty (normalizer (B : Set G) ≃* Equiv.Perm (Fin 4)) := by
  exact normalizer_equiv_symmetric_four_of_order_three
    (prime_field_odd_prime_power hpodd hFcard) e T hT B hB hBT
    (prime_field_cubic hpodd hFcard e B hB)

theorem paired_four_of_order_three_normalizers
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (hcubic : ∀ B : Subgroup G, B ≤ T → IsKleinFour B →
      ∃ x : normalizer (B : Set G), orderOf x = 3)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ T) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup G) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set G) ∧
      ¬ (A.subgroupOf (normalizer (B : Set G))).Normal := by
  let := hA
  exact paired_four_of_normalizers T hT
    (fun B hBT hB => normalizer_equiv_symmetric_four_of_order_three
      hF e T hT B hB hBT (hcubic B hBT hB)) A hAT

theorem paired_four_of_prime_field_normalizers
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ T) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup G) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set G) ∧
      ¬ (A.subgroupOf (normalizer (B : Set G))).Normal := by
  exact paired_four_of_order_three_normalizers
    (prime_field_odd_prime_power hpodd hFcard) e T hT
    (fun B _ hB => prime_field_cubic hpodd hFcard e B hB) A hA hAT

theorem four_groups_exhaust_of_sylow_card_eight
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : Nat.card T = 8)
    (A B : Subgroup G) (hA : IsKleinFour A) (hB : IsKleinFour B)
    (hAT : A ≤ T) (hBT : B ≤ T) (hne : A ≠ B)
    (C : Subgroup G) (hC : IsKleinFour C) (hCT : C ≤ T) : C = A ∨ C = B := by
  obtain ⟨n, _, ⟨eT⟩⟩ := hasDihedralSylowTwo_of_mulEquiv e
    (psl2_odd_hasDihedralSylowTwo_model F hF) T
  have hcard : Nat.card T = 2 * 2 ^ n :=
    (Nat.card_congr eT.toEquiv).trans DihedralGroup.nat_card
  have hn : n = 2 := by
    apply Nat.pow_right_injective (a := 2) (by decide)
    norm_num at hcard ⊢
    omega
  subst n
  obtain ⟨U, V, _, _, _, _, _, hcases⟩ := dihedral_four_four_groups (T : Subgroup G) eT
  rcases hcases C hCT hC with hc | hc <;>
    rcases hcases A hAT hA with ha | ha <;>
      rcases hcases B hBT hB with hb | hb <;> aesop

theorem four_groups_exhaust_of_prime_field_sylow_card_eight
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : Nat.card T = 8)
    (A B : Subgroup G) (hA : IsKleinFour A) (hB : IsKleinFour B)
    (hAT : A ≤ T) (hBT : B ≤ T) (hne : A ≠ B)
    (C : Subgroup G) (hC : IsKleinFour C) (hCT : C ≤ T) : C = A ∨ C = B := by
  exact four_groups_exhaust_of_sylow_card_eight
    (prime_field_odd_prime_power hpodd hFcard) e T hT A B hA hB hAT hBT hne C hC hCT

theorem exists_four_normalizer_eq_symmetric_overgroup
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (eM : M ≃* Equiv.Perm (Fin 4)) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ M = normalizer (B : Set G) := by
  obtain ⟨B, hBT, hB, hMN⟩ := exists_normal_four_le_sylow T M hTM eM
  let := hB
  refine ⟨B, hBT, hB, eq_of_le_of_card_ge hMN ?_⟩
  have hM : Nat.card M = 24 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  rw [hM]
  exact normalizer_card_le B (selfCentralizing hF e B hB)

theorem exists_four_normalizer_eq_symmetric_overgroup_of_prime_field
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (eM : M ≃* Equiv.Perm (Fin 4)) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ M = normalizer (B : Set G) := by
  exact exists_four_normalizer_eq_symmetric_overgroup
    (prime_field_odd_prime_power hpodd hFcard) e T M hTM eM

omit [Finite G] [Field F] [Finite F] in
theorem normalizers_ne_of_nonnormal (A B : Subgroup G)
    (hn : ¬ (A.subgroupOf (normalizer (B : Set G))).Normal) :
    normalizer (A : Set G) ≠ normalizer (B : Set G) := by
  intro he
  apply hn
  rw [← he]
  infer_instance

theorem exists_paired_four_and_local_witness_of_order_three_normalizers
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (hcubic : ∀ B : Subgroup G, B ≤ T → IsKleinFour B →
      ∃ x : normalizer (B : Set G), orderOf x = 3)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ T) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup G) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set G) ∧
      ¬ (A.subgroupOf (normalizer (B : Set G))).Normal ∧
      normalizer (A : Set G) ≠ normalizer (B : Set G) ∧
      ∀ M : Subgroup G, ¬ normalizer (B : Set G) ≤ M →
        ∃ H : Subgroup G, A ≤ H ∧
          (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H) ∧
          LocalModel A H ∧ ¬ H ≤ M := by
  obtain ⟨B, hBT, hB, hBA, h8, hnorm, hnon⟩ :=
    paired_four_of_order_three_normalizers hF e T hT hcubic A hA hAT
  refine ⟨B, hBT, hB, hBA, h8, hnorm, hnon, normalizers_ne_of_nonnormal A B hnon, ?_⟩
  intro M hM
  obtain ⟨eB⟩ := normalizer_equiv_symmetric_four_of_order_three hF e T hT B hB hBT
    (hcubic B hBT hB)
  exact local_witness_of_symmetric_four T A (A ⊔ B) (normalizer (B : Set G)) M
    (le_sup_left.trans hnorm) (sup_le hAT hBT) hnorm h8 eB hnon hM

theorem exists_paired_four_and_local_witness_of_prime_field
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (A : Subgroup G) (hA : IsKleinFour A) (hAT : A ≤ T) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup G) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set G) ∧
      ¬ (A.subgroupOf (normalizer (B : Set G))).Normal ∧
      normalizer (A : Set G) ≠ normalizer (B : Set G) ∧
      ∀ M : Subgroup G, ¬ normalizer (B : Set G) ≤ M →
        ∃ H : Subgroup G, A ≤ H ∧
          (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H) ∧
          LocalModel A H ∧ ¬ H ≤ M := by
  exact exists_paired_four_and_local_witness_of_order_three_normalizers
    (prime_field_odd_prime_power hpodd hFcard) e T hT
    (fun B hBT hB => prime_field_cubic hpodd hFcard e B hB) A hA hAT
end SymmetricNormalizers
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
