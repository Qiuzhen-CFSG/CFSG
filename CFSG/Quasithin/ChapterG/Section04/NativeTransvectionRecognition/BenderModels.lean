module
public import Theory.SpecificGroups.SU3.EvenInvolutionTwoGroupExclusion
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# The rank-one rows in the native one-centralizer inspection

The actual binary PSU₃ carrier has no involution with a two-group
centralizer. Removing precisely this row from the Bender list leaves the
PSL₂ and Suzuki carriers, with their original positive field parameters.
This is the rank-one part of the single-centralizer inspection in
Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
open ClassificationModels
variable {H : Type*} [Group H]

/-- The actual one-centralizer hypothesis removes the binary unitary row. -/
theorem bender_linear_or_suzuki (hm : IsBenderModel H)
    (t : H) (ht : orderOf t=2) (hc : IsPGroup 2 (centralizer ({t} : Set H))) :
    (∃ f : ℕ, 2≤f ∧ ClassicalGroup.IsPSL H 2 (2^f)) ∨
      (∃ m : ℕ, 1≤m ∧ Nonempty (H ≃* SuzukiMatrixGroup m)) := by
  cases hm with
  | linear f hf iso => exact .inl ⟨f,hf,iso⟩
  | suzuki m hm iso => exact .inr ⟨m,hm,iso⟩
  | unitary f hf iso =>
    obtain ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩ := iso
    letI := Fintype.ofFinite E
    letI : CharP E 2 := charP_of_card_eq_prime_pow (p:=2) (f:=f*2) (by
      simpa only [pow_mul, Nat.card_eq_fintype_card] using hcard)
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f
      (by omega) hcard hconj
    exact False.elim (HermitianForm.EvenInvolutionTwoGroup.involution_centralizer_not_twoGroup
      J hf hcard hfixed (e t) ((e.orderOf_eq t).trans ht)
      (hc.of_equiv (Matrix.SU3.InnerThreeRank.centralizerEquiv e t)))
end CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition
