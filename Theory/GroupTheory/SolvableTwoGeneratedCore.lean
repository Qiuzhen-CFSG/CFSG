module

public import Theory.GroupTheory.CharacteristicTwoCoreFour
public import Theory.GroupTheory.ElementaryEightOddKernel
public import Theory.GroupTheory.SolvableFourNormalizerSupplement

/-!
# Normalizer generation in solvable groups

If a Sylow two-subgroup of a finite solvable group contains an elementary
eight, any subgroup containing the normalizers of all subgroups of that Sylow
subgroup containing an elementary four is the whole group.

Coprime fixed-point generation puts the odd core in the given subgroup:
centralizers of fours lie in their normalizers. A four-containing subgroup of
the Sylow subgroup has a normalizer supplementing the odd core, which finishes
the proof. The trivial-odd-core specialization also follows directly from
Fitting self-centralization and the existence of a four in the two-core.

The normalizer condition concerns arbitrary subgroups of the chosen Sylow
subgroup containing an elementary four, as in GLS, Number 2, Section 22.
The structural input is the solvable Fitting argument of
Kurzweil–Stellmacher, 8.3.4.
-/

/-- In a solvable group with trivial odd core, the normalizer condition on
subgroups containing a four-group forces the whole group. -/
public theorem eq_top_of_normalizer_condition_of_solvable_oddCore_eq_bot
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : pPrimeCore 2 G = ⊥)
    (P : Sylow 2 G) (E M : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E ≤ P) (hE : 8 ≤ Nat.card E)
    (hM : ∀ Q : Subgroup G, Q ≤ P →
      (∃ V : Subgroup G, V ≤ Q ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4) →
      Subgroup.normalizer (Q : Set G) ≤ M) : M = ⊤ := by
  obtain ⟨V, hVR, hVe, hVcard⟩ :=
    exists_elementary_four_le_pCore_of_solvable_oddCore_eq_bot hodd P E hEP hE
  have h := hM (pCore 2 G) (pCore_isPGroup.le_sylow_of_normal P)
    ⟨V, hVR, hVe, hVcard⟩
  rw [Subgroup.normalizer_eq_top] at h
  exact top_unique h

/-- In a finite solvable group of elementary two-rank at least three,
normalizers of the four-containing subgroups of a chosen Sylow two-subgroup
generate the whole group. In particular, no separate containment assumption
on the Sylow subgroup in `M` is needed. -/
public theorem eq_top_of_normalizer_condition_of_solvable
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (P : Sylow 2 G) (E M : Subgroup G) [IsElementaryAbelian 2 E]
    (hEP : E ≤ P) (hE : 8 ≤ Nat.card E)
    (hM : ∀ Q : Subgroup G, Q ≤ P →
      (∃ V : Subgroup G, V ≤ Q ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4) →
      Subgroup.normalizer (Q : Set G) ≤ M) : M = ⊤ := by
  obtain ⟨D, hDcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    Nat.prime_two (IsElementaryAbelian.isPGroup 2 E)
    (show 2 ^ 3 ≤ Nat.card E from hE)
  let _ : IsElementaryAbelian 2 D := {
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
      (IsElementaryAbelian.exponent_dvd_p 2 E) }
  let A := D.map E.subtype
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.map_subtype
  have hAcard : Nat.card A = 8 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hDcard]
    rfl
  have hodd : pPrimeCore 2 G ≤ M := by
    apply Subgroup.le_of_odd_normal_elementary_eight_centralizers
      (pPrimeCore 2 G) A M
      (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))) hA hAcard
    intro V hVA hVe hVcard
    exact (Subgroup.centralizer_le_normalizer _).trans
      (hM V (hVA.trans ((Subgroup.map_subtype_le D).trans hEP))
        ⟨V, le_rfl, hVe, hVcard⟩)
  obtain ⟨Q, hQP, hQfour, hsup⟩ :=
    exists_four_containing_normalizer_supplement_of_solvable P E hEP hE
  apply top_unique
  rw [← hsup]
  exact sup_le (hM Q hQP hQfour) hodd
