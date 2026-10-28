module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Tori
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers

/-!
# Inner prime-field PSL₂ local geometry

We construct the concrete local witnesses for every large elementary family
in PSL₂ over a prime field of odd order greater than five. When the Sylow
subgroup has order four, prime dihedral tori escape proper overgroups by the
involution-centralizer bound. For larger Sylow subgroups, paired four-groups
provide S₄ normalizers with a nonnormal actor and an order-eight overlap.

Dickson's classification leaves dihedral and S₄ maximal overgroups in the
latter case. An S₄ witness cannot lie in a dihedral group. If it equals the
proposed S₄ overgroup, the two-four-group exhaustion and weak-closure condition
force its normal four-group into the family; pairing again gives an escaping
normalizer. This retains the two four-group classes at p = 7 and requires only
the literal Sylow intersection, not containment of the ambient Sylow in S₄.

The intrinsic E1 verification and the final E-generation assembly belong to
the consumers of this concrete placement theorem.

Source: Aschbacher--Smith, E.1.2 and E.1.14(6), printed pp.209--210 and 214,
citing Aschbacher (1982), Lemma 4.10.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite G] in
private theorem symmetric_card (H : Subgroup G) (eH : H ≃* Equiv.Perm (Fin 4)) :
    Nat.card H = 24 := by
  rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

private theorem sylow_card_eight_of_symmetric_overgroup
    (T : Sylow 2 G) (hT : 8 ≤ Nat.card T) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (eM : M ≃* Equiv.Perm (Fin 4)) :
    Nat.card T = 8 := by
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hdvd : 2 ^ n ∣ 24 := by
    simpa only [hn, symmetric_card M eM] using Subgroup.card_dvd_of_le hTM
  have hn4 : n < 4 := by
    by_contra h
    have h16 : 16 ∣ 24 := (pow_dvd_pow 2 (by omega : 4 ≤ n)).trans hdvd
    norm_num at h16
  rw [hn] at hT ⊢
  interval_cases n <;> norm_num at *

/-- For a Sylow subgroup of order at least eight, paired four-group normalizers
supply an escaping S₄ model. If the first normalizer is the proposed overgroup,
the weak-closure condition forces its normal four-group into the family, and
its paired normalizer escapes instead. -/
theorem concreteLocalGeometryAt_of_large_sylow
    {p : ℕ} [Fact p.Prime] (hpo : Odd p) (hF : Nat.card F = p)
    (e : G ≃* PSL2 F) (T : Sylow 2 G) (hT : 8 ≤ Nat.card T) :
    ConcreteLocalGeometryAt T := by
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hpo, le_rfl, by simpa using hF⟩
  intro Ω hΩ hlarge M hM hTM hNM
  obtain ⟨A, hAΩ, hAT, hA⟩ :=
    exists_four_group_actor hodd e T Ω hΩ hlarge M hM.1 hNM
  obtain ⟨B, hBT, hB, hBA, _, _, _, hNAB, hlocalA⟩ :=
    SymmetricNormalizers.exists_paired_four_and_local_witness_of_prime_field
      hpo hF e T hT A hA hAT
  obtain ⟨eNB⟩ := SymmetricNormalizers.normalizer_equiv_symmetric_four_of_prime_field
    hpo hF e T hT B hB hBT
  rcases Overgroups.proper_overgroup_of_large_sylow hpo hF e T hT M hTM hM.1 with hd | hs
  · obtain ⟨k, _, ⟨eM⟩⟩ := hd
    exact ⟨A, hAΩ, hAT, hA, hlocalA M
      (Overgroups.symmetric_four_not_le_dihedral _ M eNB eM)⟩
  obtain ⟨eM⟩ := hs
  by_cases hNBM : normalizer (B : Set G) ≤ M
  · have hNBeq : normalizer (B : Set G) = M :=
      eq_of_le_of_card_ge hNBM (by rw [symmetric_card _ eNB, symmetric_card M eM])
    have hT8 := sylow_card_eight_of_symmetric_overgroup T hT M hTM eM
    have hBΩ : B ∈ Ω := by
      by_contra hBΩ
      have hWA : weakClosure (T : Subgroup G) Ω = A := by
        apply le_antisymm
        · rw [weakClosure_eq_four_group_family hodd e T Ω hΩ hlarge]
          apply sSup_le
          intro C hC
          rcases SymmetricNormalizers.four_groups_exhaust_of_sylow_card_eight
            hodd e T hT8 A B hA hB hAT hBT (Ne.symm hBA) C hC.1.2 hC.2 with hCA | hCB
          · exact hCA.le
          · exact (hBΩ (hCB ▸ hC.1.1)).elim
        · exact le_sSup ⟨hAΩ, hAT⟩
      rw [hWA] at hNM
      obtain ⟨eNA⟩ := SymmetricNormalizers.normalizer_equiv_symmetric_four_of_prime_field
        hpo hF e T hT A hA hAT
      have hNAeq : normalizer (A : Set G) = M :=
        eq_of_le_of_card_ge hNM (by rw [symmetric_card _ eNA, symmetric_card M eM])
      exact hNAB (hNAeq.trans hNBeq.symm)
    obtain ⟨C, hCT, hC, _, _, _, _, hNBC, hlocalB⟩ :=
      SymmetricNormalizers.exists_paired_four_and_local_witness_of_prime_field
        hpo hF e T hT B hB hBT
    refine ⟨B, hBΩ, hBT, hB, hlocalB M ?_⟩
    intro hNCM
    obtain ⟨eNC⟩ := SymmetricNormalizers.normalizer_equiv_symmetric_four_of_prime_field
      hpo hF e T hT C hC hCT
    have hNCeq : normalizer (C : Set G) = M :=
      eq_of_le_of_card_ge hNCM (by rw [symmetric_card _ eNC, symmetric_card M eM])
    exact hNBC (hNBeq.trans hNCeq.symm)
  · exact ⟨A, hAΩ, hAT, hA, hlocalA M hNBM⟩

/-- Every Sylow two-subgroup of an actual PSL₂ model over a prime field of
odd order greater than five has the concrete local geometry required in the
large-family branch of E.1.14(6). The four-group Sylow case uses prime dihedral
tori; larger Sylow subgroups use paired S₄ normalizers. -/
theorem concreteLocalGeometryAt_of_prime_field
    {p : ℕ} (hp : p.Prime) (hpo : Odd p) (hp5 : 5 < p)
    (hF : Nat.card F = p) (e : G ≃* PSL2 F) (T : Sylow 2 G) :
    ConcreteLocalGeometryAt T := by
  let : Fact p.Prime := ⟨hp⟩
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hpo, le_rfl, by simpa using hF⟩
  rcases sylow_card_cases hodd e T with hT | hT
  · exact concreteLocalGeometryAt_of_sylow_card_four hp hpo hp5 hF e T hT
      (Overgroups.proper_overgroup_actor_centralizer hpo hF e)
  · exact concreteLocalGeometryAt_of_large_sylow hpo hF e T hT

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
