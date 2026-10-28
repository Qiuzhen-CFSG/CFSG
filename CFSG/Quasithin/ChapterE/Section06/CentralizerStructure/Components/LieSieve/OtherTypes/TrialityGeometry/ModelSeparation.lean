module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Normalization
public import Theory.SpecificGroups.Triality.ModelSeparation.TwoSubgroup
public import Theory.SpecificGroups.Triality.ModelSeparation.LeviObstructions
public import Theory.SpecificGroups.Triality.ModelSeparation.Core
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Genuine triality is absent from the nonnormal C-component list

For a finite quasisimple group isomorphic to the genuine graph-field carrier
³D₄(2^f), its two-core is trivial. The actual positive fixed-root subgroup is
nonabelian and a two-group, excluding binary PSL₂. The cubic arm root subgroup
has order at least eight, excluding odd-prime PSL₂ with its dihedral Sylow
subgroups. Finally the arm Levi forces divisibility by nine, whereas Suzuki
orders are prime to three and the certified J₁ order is not divisible by nine.
All constructions include f = 1 and inherit quasisimplicity from the input.

This discharges exactly the model-exclusion premise of
`normalizes_of_source_1_2_1`. Relative normalization and the final E.6.8
parabolic argument are owned by the importing triality geometry development.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.2.1(3), printed p.504/PDF p.521, and the proof of E.6.8,
printed p.247/PDF p.258 (`refs/quasithin.pdf`).
-/

public section

open Subgroup Theory.GroupTheory Triality.Standard
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
open Chapter1.Section02

/-- Genuine binary triality excludes all four actual quotient models in
1.2.1(3), with no additional order, simplicity, or root-geometry premise. -/
theorem not_nonnormalCComponentModel {A : Type*} [Group A] [Finite A]
    [IsQuasisimple A] {f : ℕ} (hf : 1 ≤ f)
    (htriality : IsTrialityGroupAt (2 ^ f) A) :
    ¬ NonnormalCComponentModel (A ⧸ pCore 2 A) := by
  obtain ⟨et⟩ := (isTrialityGroupAt_binary_iff A f hf).mp htriality
  have hcore := ModelSeparation.twoCore_eq_bot hf htriality
  let e : (A ⧸ pCore 2 A) ≃* BinaryCarrier f hf :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot.trans et)
  intro hm
  cases hm with
  | linear_even n hn iso =>
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := iso
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact ModelSeparation.not_equiv_binary_psl2 f hf F (e.symm.trans eF)
  | suzuki m hm iso =>
    obtain ⟨eS⟩ := iso
    have hd := ModelSeparation.nine_dvd_card f hf
    rw [Nat.card_congr (e.symm.trans eS).toEquiv] at hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm
      ((by decide : 3 ∣ 9).trans hd)
  | linear_prime p hp ho iso =>
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := iso
    exact ModelSeparation.not_equiv_odd_psl2 f hf F
      ⟨p, 1, hp, ho, by decide, by simpa only [pow_one] using hF⟩ (e.symm.trans eF)
  | janko iso =>
    obtain ⟨eJ⟩ := iso
    have hd := ModelSeparation.nine_dvd_card f hf
    rw [Nat.card_congr (e.symm.trans eJ).toEquiv, Janko1.card_model] at hd
    norm_num at hd

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
