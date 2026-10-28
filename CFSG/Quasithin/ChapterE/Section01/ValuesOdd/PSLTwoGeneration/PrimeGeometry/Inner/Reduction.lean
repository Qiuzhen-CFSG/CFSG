module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Actors
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Sylow
public import GorensteinWalter.PSL2DihedralSylow

/-!
# Reductions for the inner prime-field PSL₂ placement calculation

The large elementary actors are four-groups. If a suitable involution of an
actor has centralizer of order at most eight in a proposed proper overgroup,
then a dihedral subgroup of order `4r`, for an odd prime r, in its ambient
centralizer escapes that overgroup. Its Sylow intersection follows from the
actor's order. The S₄ consumer similarly uses an order-eight subgroup in the
ambient Sylow, without requiring the entire Sylow to lie in S₄.

These are conditional geometric reductions. The proper-overgroup calculation,
the torus witnesses for the order-four Sylow case, and the S₄ normalizer
geometry for larger Sylow subgroups still have to be constructed in PSL₂.
No unconditional placement or E-generation theorem is asserted here.

Source: Aschbacher--Smith, E.1.2 and E.1.14(6), printed pp.209--210 and 214,
and the latter's citation of Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

/-- The Sylow orders split into the four-group and larger dihedral cases. -/
theorem sylow_card_cases (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) : Nat.card T = 4 ∨ 8 ≤ Nat.card T := by
  obtain ⟨n, hn, ⟨eT⟩⟩ := hasDihedralSylowTwo_of_mulEquiv e
    (psl2_odd_hasDihedralSylowTwo_model F hF) T
  have hc : Nat.card T = 2 * 2 ^ n := by
    rw [Nat.card_congr eT.toEquiv, DihedralGroup.nat_card]
  by_cases hn1 : n = 1
  · exact Or.inl (by simp [hc, hn1])
  · right
    have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    omega

private theorem dihedral_torus_not_le
    (H M : Subgroup G) (z : G) (hH : H ≤ centralizer ({z} : Set G))
    (hM : Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 8)
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (e : H ≃* DihedralGroup (2 * r)) :
    ¬ H ≤ M := by
  intro hHM
  have hle : H.subgroupOf M ≤ (centralizer ({z} : Set G)).subgroupOf M :=
    fun x hx => hH hx
  have hsmall := (Subgroup.card_le_of_le hle).trans hM
  have hcard : Nat.card (H.subgroupOf M) = 4 * r := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv,
      Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    ring
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    have := hro.not_two_dvd_nat
    omega
  omega

/-- The torus and small-centralizer calculations give a concrete escaping
local model, with its actual Sylow intersection. -/
theorem local_witness_of_involution_torus
    (T : Sylow 2 G) (A M : Subgroup G) (hA : IsKleinFour A)
    (hAT : A ≤ (T : Subgroup G)) (z : G)
    (hM : Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 8)
    (htorus : ∃ (r : ℕ) (H : Subgroup G), r.Prime ∧ Odd r ∧
      A ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
      Nonempty (H ≃* DihedralGroup (2 * r))) :
    ∃ H : Subgroup G, A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H) ∧
      LocalModel A H ∧ ¬ H ≤ M := by
  obtain ⟨r, H, hr, hro, hAH, hHC, ⟨eH⟩⟩ := htorus
  exact ⟨H, hAH, sylow_intersection_dihedral T A H hAT hAH hA hro eH,
    Or.inr ⟨r, hr, hro, ⟨eH⟩⟩, dihedral_torus_not_le H M z hHC hM hr hro eH⟩

omit [Finite G] in
/-- An S₄ normalizer with a nonnormal actor supplies the required local
witness once its order-eight overlap and escape have been constructed. -/
theorem local_witness_of_symmetric_four
    (T : Sylow 2 G) (A D H M : Subgroup G) (hAH : A ≤ H)
    (hDT : D ≤ (T : Subgroup G)) (hDH : D ≤ H) (hD : Nat.card D = 8)
    (eH : H ≃* Equiv.Perm (Fin 4)) (hAn : ¬ (A.subgroupOf H).Normal)
    (hHM : ¬ H ≤ M) :
    ∃ K : Subgroup G, A ≤ K ∧
      (∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K) ∧
      LocalModel A K ∧ ¬ K ≤ M :=
  ⟨H, hAH, sylow_intersection_symmetric_four T D H hDT hDH hD eH,
    Or.inl ⟨⟨eH⟩, hAn⟩, hHM⟩

/-- Conditional assembly of the torus route. The two explicit inputs are
proper-overgroup centralizer bounds and actual dihedral torus witnesses;
they are not consequences of the PSL₂ model proved in this module. -/
theorem concreteLocalGeometryAt_of_involution_tori
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F) (T : Sylow 2 G)
    (hsmall : ∀ A M : Subgroup G, IsKleinFour A → A ≤ M → M ≠ ⊤ →
      ∃ z : G, z ∈ A ∧ z ≠ 1 ∧
        Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 8)
    (htori : ∀ A : Subgroup G, IsKleinFour A → A ≤ (T : Subgroup G) →
      ∀ z : G, z ∈ A → z ≠ 1 →
        ∃ (r : ℕ) (H : Subgroup G), r.Prime ∧ Odd r ∧
          A ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
          Nonempty (H ≃* DihedralGroup (2 * r))) :
    ConcreteLocalGeometryAt T := by
  intro Ω hΩ hlarge M hM hTM hNM
  obtain ⟨A, hAΩ, hAT, hA⟩ :=
    exists_four_group_actor hF e T Ω hΩ hlarge M hM.1 hNM
  obtain ⟨z, hzA, hz, hMz⟩ := hsmall A M hA (hAT.trans hTM) hM.1
  exact ⟨A, hAΩ, hAT, hA,
    local_witness_of_involution_torus T A M hA hAT z hMz (htori A hA hAT z hzA hz)⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
