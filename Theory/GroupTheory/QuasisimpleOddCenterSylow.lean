module

public import ABG.ChapterII.Section1.WreathedDefs
public import Theory.GroupTheory.BrauerSuzuki
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Odd-center quasisimple groups have no quaternion Sylow subgroup

An odd central kernel preserves Sylow two-subgroups. The simple central
quotient therefore would have a generalized quaternion Sylow subgroup.
Its odd core and center are both trivial, contradicting the proved
Brauer--Suzuki theorem. No classification of the simple quotient is used.

Source: Suzuki, Group Theory II, VI.2.2 Example 3; the component exclusion
in Aschbacher--Smith F.6.18, printed p.310.
-/

public noncomputable section
open Subgroup ABG
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem not_quaternion_sylow_of_quasisimple_odd_center [IsQuasisimple G] (hZ : Odd (Nat.card (center G))) :
    ¬ HasGeneralizedQuaternionSylowTwo G := by
  rintro ⟨S, n, hn, ⟨a⟩⟩
  let Q := G ⧸ center G
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center G))
  let P : Sylow 2 Q := default
  let e := Sylow.equivOfSurjectiveCoprime (QuotientGroup.mk' (center G))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact Nat.coprime_two_left.mpr hZ) S P
  let b := e.symm.trans a
  have htwo : 2 ∣ Nat.card Q := by
    have hh : 2 ∣ Nat.card P := by
      rw [Nat.card_congr b.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      exact ⟨2 * 2 ^ n, by ring⟩
    exact hh.trans (P : Subgroup Q).card_subgroup_dvd_card
  have hcore : pPrimeCore 2 Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 Q) inferInstance with h | h
    · exact h
    · have hc := pPrimeCore_coprime_card (p := 2) (G := Q)
      rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv] at hc
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hc htwo).elim
  have hcenter : center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) inferInstance with h | h
    · exact h
    · have hc := center_eq_top_iff.mp h
      exact (Group.IsPerfect.not_isSolvable Q
        (Group.isSolvable_of_comm (isMulCommutative_iff.mp hc))).elim
  have hh := even_card_center_quotient_pPrimeCore_of_quaternion_sylow
    P (n := n+2) (by omega) (by
      have he : n + 2 - 2 = n := by omega
      rw [he]
      exact ⟨b⟩)
  let c : Q ⧸ pPrimeCore 2 Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  rw [Nat.card_congr (centerCongr c).toEquiv, hcenter] at hh
  simp at hh

end Theory.GroupTheory
