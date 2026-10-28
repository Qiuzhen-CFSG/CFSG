module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition.CubicQuotient
public import Theory.GroupTheory.PResidual.CentralModuleFixed
public import Theory.GroupAction.CoprimeCentralizerLift

/-!
# Removing central errors from a cubic residual layer

Let A be two-perfect with A/O₂(A) of order three. Suppose D lies in O₂(A)
and is normalized by A, and U is an abelian A-invariant subgroup of D.
If A centralizes D/U and O₂(A) centralizes D modulo an A-central layer,
then C_D(A) supplements U. In particular D > U supplies an actual
A-central element outside U.

A cubic supplement to O₂(A) lifts fixed cosets through U by coprime action.
Its fixed subgroup centralizes A modulo the central layer; two-perfect
commutator idempotence removes that error.

Source application: Aschbacher–Smith 14.7.24–25, printed pp.1051–1052,
refs/quasithin.pdf. The literal original-group application is in
LocalReduction.ExtraspecialCentralSubgroup.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A central error below a cubic residual can be removed from an actual
fixed coset. This produces a central element outside the prescribed layer. -/
theorem cubic_central_layer_lift (A D U Z : Subgroup G)
    [IsMulCommutative U]
    (hA : IsPPerfect 2 A) (hcard : Nat.card (A ⧸ pCore 2 A) = 3)
    (hDP : D ≤ A.pCoreIn 2) (hUD : U ≤ D) (hDU : ¬ D ≤ U)
    (hAD : A ≤ normalizer (D : Set G))
    (hAU : A ≤ normalizer (U : Set G))
    (hZC : Z ≤ centralizer (A : Set G))
    (hm : ⁅D,A⁆ ≤ U) (hp : ⁅D,A.pCoreIn 2⁆ ≤ Z) :
    ¬ D ⊓ centralizer (A : Set G) ≤ U := by
  have h3 : 3 ∣ Nat.card A := hcard ▸ (Subgroup.card_quotient_dvd_card (pCore 2 A))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h3
  have hz3 : orderOf (z : G) = 3 := (Subgroup.orderOf_coe z).trans hz
  let J := zpowers (z : G)
  have hJA : J ≤ A := zpowers_le.mpr z.property
  have hgen : A.pCoreIn 2 ⊔ J = A :=
    pCoreIn_sup_zpowers_eq_of_quotient_card_three hcard z.property hz3
  have hDZ : D ≤ normalizer (Z : Set G) :=
    (hDP.trans (pCoreIn_le 2 A)).trans
      ((le_centralizer_iff.mp hZC).trans (centralizer_le_normalizer _))
  have hAZ : A ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp hZC).trans (centralizer_le_normalizer _)
  let C := D ⊓ centralizer (J : Set G)
  have hCA : ⁅C,A⁆ ≤ Z := by
    have hle : A ≤ commutatorPreimage A C Z := by
      conv_lhs => rw [←hgen]
      apply sup_le
      · apply le_commutatorPreimage (pCoreIn_le 2 A)
        rw [commutator_comm]
        exact (commutator_mono inf_le_left le_rfl).trans hp
      · apply le_commutatorPreimage hJA
        rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr
          (show C ≤ centralizer (J : Set G) from inf_le_right)]
        exact bot_le
    rw [commutator_comm]
    exact (commutator_mono hle le_rfl).trans (commutator_commutatorPreimage_le A C Z hAZ)
  have hCC : C ≤ centralizer (A : Set G) :=
    centralizes_of_isPPerfect_central_displacement A D C Z hA
      ((isPGroup_pCoreIn 2 A).to_le hDP) hAD hDZ hZC inf_le_left hCA
  have hcop : Nat.Coprime (Nat.card J) (Nat.card U) := by
    have hJ : IsPGroup 3 J := IsPGroup.of_card (n := 1) (by
      rw [show Nat.card J = orderOf (z : G) from Nat.card_zpowers _,hz3,pow_one])
    exact IsPGroup.coprime_card_of_ne 3 2 (by decide) J U hJ
      ((isPGroup_pCoreIn 2 A).to_le (hUD.trans hDP))
  let : (U.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((hDP.trans (pCoreIn_le 2 A)).trans hAU)
  intro hc
  apply hDU
  intro x hx
  have hm' : ∀ j ∈ J, MulAut.conj j x / x ∈ U := by
    intro j hj
    simpa only [MulAut.conj_apply,div_eq_mul_inv,commutatorElement_def] using
      (commutator_le.mp (commutator_comm D A ▸ hm)) j (hJA hj) x hx
  have hh := mem_centralizer_sup_of_coprime_fixed_coset D U J hUD
    (hJA.trans hAD) (hJA.trans hAU) hcop x hx hm'
  have hCU : C ≤ U := fun _ hx => hc ⟨hx.1,hCC hx⟩
  exact (show C ⊔ U ≤ U from sup_le hCU le_rfl) hh
end Subgroup
