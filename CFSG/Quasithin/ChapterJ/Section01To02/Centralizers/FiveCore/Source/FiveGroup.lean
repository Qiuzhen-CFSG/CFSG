module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Hyperplanes
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PrimeOrderCentralizerSylow
public import Theory.Quasithin.EvenCharacteristic

/-!
# Five-core recognition, nonconjugacy and the non-Sylow step

After excluding the order-45 branch, the odd core has order five or 125.
Its quaternion supplement makes the full centralizer order prime to three.
Every subgroup of the actual residual L_B centralizes B, of order three,
so no conjugate of B₅ can be a Sylow five-subgroup of L_B. When those
residual Sylow subgroups have order five, Sylow conjugacy makes B₅
non-Sylow in G. The prime-order centralizer theorem then excludes an
odd core of order five. Finally normality identifies the odd core with O₅.

The final theorem is a conditional assembly: the quaternion and inverter
witnesses, the odd-subgroup calculation in H, the order-45 exclusion, and
the residual Sylow order must still be proved by their source producers.
Neither the later triple-cover identification nor either legacy FiveCore
input record is used.

Source: Aschbacher–Smith, J.2.7(5–6), printed p.436 (PDF p.447).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)
  (B5 : Sylow 5 d.toTypeRuSetup.H)
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem CQ_card (q : FiveQuaternionData B5) : Nat.card (CQ B5) = 8 := by
  obtain ⟨e⟩ := q.quaternion
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

include c in
theorem G5_card (hZ : Nat.card d.toTypeRuSetup.Z = 2) (q : FiveQuaternionData B5) :
    Nat.card (G5 B5) = Nat.card (fiveOddPart B5) * 8 := by
  rw [c.G5_eq_fiveOddPart_sup_CQ hZ B5 q,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (inf_le_right.trans (G5_normalizes_fiveOddPart B5))
      (disjoint_of_coprime_natCard (by
        rw [CQ_card B5 q]
        exact (Nat.coprime_two_left.mpr (fiveOddPart_odd B5)).symm.pow_right 3)),
    CQ_card B5 q]

theorem fiveOddPart_eq_fiveCore_of_isPGroup
    (hp : IsPGroup 5 (fiveOddPart B5)) : fiveOddPart B5 = pCoreIn 5 (G5 B5) := by
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes hp (fiveOddPart_le_G5 B5)
      (G5_normalizes_fiveOddPart B5)
  · apply map_mono
    apply le_sSup
    refine ⟨pCore_normal, ?_⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 5) (G := G5 B5)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 5).pow_right n

include c in
theorem notConjToLB_of_not_three_dvd (hB : Nat.card c.B = 3)
    (h3 : ¬ 3 ∣ Nat.card (G5 B5)) : NotConjToLB c B5 := by
  intro S ⟨g, hg⟩
  let SG := (S : Subgroup c.LB).map c.LB.subtype
  have hSG : SG ≤ c.GB := (map_subtype_le _).trans (map_subtype_le _)
  have hBcent : c.B ≤ centralizer (SG : Set G) := by
    intro b hb s hs
    exact (hSG hs b hb).symm
  have hd := card_dvd_of_le hBcent
  have hcard : Nat.card (centralizer (SG : Set G)) = Nat.card (G5 B5) := by
    change (B5Image B5).map (MulAut.conj g).toMonoidHom = SG at hg
    rw [← hg, ← Theory.Quasithin.map_centralizer,
      card_map_of_injective (MulAut.conj g).injective]
  exact h3 (by simpa only [hB, hcard] using hd)

/-- The comparison with a prime-order Sylow subgroup of the actual residual
forces the original B5 not to be an ambient Sylow subgroup. -/
theorem B5Image_not_sylow_of_notConj
    (hZ : Nat.card d.toTypeRuSetup.Z = 2) (hn : NotConjToLB c B5)
    (hLB : ∀ S : Sylow 5 c.LB, Nat.card S = 5) :
    ¬ ∃ T : Sylow 5 G, (T : Subgroup G) = B5Image B5 := by
  rintro ⟨T, hT⟩
  let S : Sylow 5 c.LB := Classical.choice inferInstance
  let SG := (S : Subgroup c.LB).map c.LB.subtype
  obtain ⟨R, hSR⟩ := (S.isPGroup'.map c.LB.subtype).exists_le_sylow
  have hTcard : Nat.card T = 5 := by
    rw [hT, B5Image_card hZ B5]
  have hRcard : Nat.card R = 5 := (Nat.card_congr (R.equiv T).toEquiv).trans hTcard
  have hSGeq : SG = (R : Subgroup G) := eq_of_le_of_card_ge hSR (by
    rw [hRcard, card_map_of_injective c.LB.subtype_injective, hLB S])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T R
  have he := congrArg (fun P : Sylow 5 G => (P : Subgroup G)) hg
  change (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (R : Subgroup G) at he
  rw [hT, ← hSGeq] at he
  exact hn S ⟨g, he⟩

include c in
/-- The prime-order centralizer theorem rules out an odd complement of order five. -/
theorem fiveOddPart_card_ne_five
    (hZ : Nat.card d.toTypeRuSetup.Z = 2) (q : FiveQuaternionData B5)
    (hn : ¬ ∃ T : Sylow 5 G, (T : Subgroup G) = B5Image B5) :
    Nat.card (fiveOddPart B5) ≠ 5 := by
  intro h5
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5
    (show 5 ∣ Nat.card (B5Image B5) from by rw [B5Image_card hZ B5])
  have hbG : orderOf (b : G) = 5 := by simpa only [Subgroup.orderOf_coe] using hb
  have hgen : zpowers (b : G) = B5Image B5 :=
    eq_of_le_of_card_ge (zpowers_le.mpr b.property) (by
      rw [Nat.card_zpowers, hbG, B5Image_card hZ B5])
  have hcent : centralizer ({(b : G)} : Set G) = G5 B5 := by
    change _ = centralizer (B5Image B5 : Set G)
    conv_rhs => rw [← hgen, zpowers_eq_closure, centralizer_closure]
  have hcard : Nat.card (G5 B5) = 40 := by rw [G5_card c B5 hZ q, h5]
  obtain ⟨T, hT⟩ := (B5.isPGroup'.map d.toTypeRuSetup.H.subtype).exists_le_sylow
  have hTcard : Nat.card T = 5 := sylow_card_eq_prime_of_centralizer (b : G) hbG
    (by rw [hcent, hcard]; decide) T
  exact hn ⟨T, (eq_of_le_of_card_ge hT (by rw [hTcard, B5Image_card hZ B5])).symm⟩

/-- Final arithmetic and Sylow assembly. Its three local/model calculations
must be constructed before this is a source proof of J.2.7(5–6). -/
theorem five_core_conclusions_of_calculations
    (hZ : Nat.card d.toTypeRuSetup.Z = 2) (hB : Nat.card c.B = 3)
    (q : FiveQuaternionData B5) (v : FiveInverterData c B5)
    (hoddH : ∀ A : Subgroup G, A ≤ d.toTypeRuSetup.H → Odd (Nat.card A) →
      Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5)
    (h45 : Nat.card (fiveOddPart B5) ≠ 45)
    (hLB : ∀ S : Sylow 5 c.LB, Nat.card S = 5) :
    G5 B5 = pCoreIn 5 (G5 B5) ⊔ CQ B5 ∧
      Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
      Nat.card (pCoreIn 5 (G5 B5)) = 125 ∧ NotConjToLB c B5 := by
  have hcases : Nat.card (fiveOddPart B5) = 5 ∨ Nat.card (fiveOddPart B5) = 125 := by
    rcases v.oddPart_card_cases c B5 hZ q hoddH with h5 | h | h125
    · exact Or.inl h5
    · exact (h45 h).elim
    · exact Or.inr h125
  have h3 : ¬ 3 ∣ Nat.card (G5 B5) := by
    rw [G5_card c B5 hZ q]
    rcases hcases with h5 | h125
    · rw [h5]; decide
    · rw [h125]; decide
  have hn := c.notConjToLB_of_not_three_dvd B5 hB h3
  have hnotSylow := c.B5Image_not_sylow_of_notConj B5 hZ hn hLB
  have h125 : Nat.card (fiveOddPart B5) = 125 :=
    hcases.resolve_left (c.fiveOddPart_card_ne_five B5 hZ q hnotSylow)
  have hp : IsPGroup 5 (fiveOddPart B5) := IsPGroup.of_card (n := 3) h125
  have he := fiveOddPart_eq_fiveCore_of_isPGroup B5 hp
  exact ⟨he ▸ c.G5_eq_fiveOddPart_sup_CQ hZ B5 q, q.quaternion, he ▸ h125, hn⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
