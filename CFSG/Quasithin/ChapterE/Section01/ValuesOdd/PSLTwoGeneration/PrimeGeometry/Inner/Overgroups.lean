module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups.Classification
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups.Models

/-!
# Prime-field PSL₂ proper overgroups and actor centralizers

Dickson's four possible proper overgroups, combined with the concrete model
bounds, supply a nonidentity actor element whose relative centralizer has order
at most eight. If the overgroup contains a Sylow two-subgroup of order at least
eight, divisibility excludes A₄ and A₅. The final theorem discharges the small
centralizer premise of the inner local-geometry reduction, retaining exactly
its independent torus premise.

These overgroup calculations hold for every odd prime field. The source's
restriction p > 5 is needed by the remaining geometry, and need not be added
to these stronger intermediate results.

Source: Aschbacher--Smith E.1.2 and E.1.14(6), printed pp.209–210 and 214;
Dickson's subgroup classification, Huppert II.8.27. The parent inner-geometry
assembly owns the construction of the torus witnesses and the larger-Sylow
normalizer geometry; this module asserts no unconditional local placement.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

private theorem actor_centralizer_of_model {K : Type*} [Group K] [Finite K]
    (A M : Subgroup G) (hA : IsKleinFour A) (hAM : A ≤ M) (eM : M ≃* K)
    (hbound : ∀ z : K, z ≠ 1 → z ^ 2 = 1 →
      Nat.card (centralizer ({z} : Set K)) ≤ 8) :
    ∃ z : G, z ∈ A ∧ z ≠ 1 ∧
      Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 8 := by
  have hAne : A ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot A).mp (by rw [hA.card_four]; decide)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  let z : M := ⟨a, hAM a.property⟩
  have hz : z ≠ 1 := by
    intro h
    apply ha
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G)) h
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    have hsq := @IsKleinFour.mul_self A _ hA a
    simpa [z, pow_two] using congrArg Subtype.val hsq
  refine ⟨a, a.property, fun h => ha (Subtype.ext h), ?_⟩
  apply (relative_centralizer_card_le M eM.toMonoidHom eM.injective z).trans
  apply hbound
  · exact fun h => hz (eM.injective (h.trans eM.map_one.symm))
  · simpa using congrArg eM hz2

/-- The exact proper-overgroup bound needed by the involution-torus reduction.
The selected actor element is a reflection in the dihedral case. -/
theorem proper_overgroup_actor_centralizer {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : Nat.card F = p) (e : G ≃* PSL2 F)
    (A M : Subgroup G) (hA : IsKleinFour A) (hAM : A ≤ M) (hM : M ≠ ⊤) :
    ∃ z : G, z ∈ A ∧ z ≠ 1 ∧
      Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ≤ 8 := by
  rcases proper_overgroup_models hpodd hF e A M hA hAM hM with hd | h4 | hs | h5
  · obtain ⟨k, hk, ⟨ek⟩⟩ := hd
    obtain ⟨z, hzA, hz, hc⟩ := dihedral_actor_centralizer A M hA hAM hk ek
    exact ⟨z, hzA, hz, hc.trans (by decide)⟩
  · exact actor_centralizer_of_model A M hA hAM h4.some alternating_four_involution_centralizer
  · exact actor_centralizer_of_model A M hA hAM hs.some symmetric_four_involution_centralizer
  · exact actor_centralizer_of_model A M hA hAM h5.some alternating_five_involution_centralizer

/-- An overgroup of a Sylow two-subgroup of order at least eight has only
the dihedral and S₄ alternatives. -/
theorem proper_overgroup_of_large_sylow {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : Nat.card F = p) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (hM : M ≠ ⊤) :
    (∃ k : ℕ, 0 < k ∧ Nonempty (M ≃* DihedralGroup (2 * k))) ∨
      Nonempty (M ≃* Equiv.Perm (Fin 4)) := by
  have hFo : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hF⟩
  obtain ⟨m, hm, ⟨eT⟩⟩ := hasDihedralSylowTwo_of_mulEquiv e
    (psl2_odd_hasDihedralSylowTwo_model F hFo) T
  obtain ⟨A, hAT, hA⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (T : Subgroup G) hm eT
  have h8T : 8 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    have hn3 : 3 ≤ n := by
      by_contra h
      have hn2 : n ≤ 2 := by omega
      rw [hn] at hT
      interval_cases n <;> norm_num at hT
    rw [hn]
    exact pow_dvd_pow 2 hn3
  have h8M : 8 ∣ Nat.card M := h8T.trans (Subgroup.card_dvd_of_le hTM)
  rcases proper_overgroup_models hpodd hF e A M hA (hAT.trans hTM) hM with
    hd | h4 | hs | h5
  · exact Or.inl hd
  · obtain ⟨e4⟩ := h4
    rw [Nat.card_congr e4.toEquiv,
      alternatingGroup.card_of_card_eq_four (by simp)] at h8M
    norm_num at h8M
  · exact Or.inr hs
  · obtain ⟨e5⟩ := h5
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card] at h8M
    norm_num at h8M

/-- Application to the literal torus reduction: only its independently
produced torus premise remains. The proper-overgroup premise is discharged. -/
theorem concreteLocalGeometryAt_of_tori {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hF : Nat.card F = p) (e : G ≃* PSL2 F) (T : Sylow 2 G)
    (htori : ∀ A : Subgroup G, IsKleinFour A → A ≤ (T : Subgroup G) →
      ∀ z : G, z ∈ A → z ≠ 1 →
        ∃ (r : ℕ) (H : Subgroup G), r.Prime ∧ Odd r ∧
          A ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
          Nonempty (H ≃* DihedralGroup (2 * r))) :
    ConcreteLocalGeometryAt T := by
  have hFo : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hpodd, le_rfl, by simpa using hF⟩
  exact concreteLocalGeometryAt_of_involution_tori hFo e T
    (proper_overgroup_actor_centralizer hpodd hF e) htori

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups
