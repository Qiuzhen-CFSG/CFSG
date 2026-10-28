module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.Trace
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport
public import Theory.GroupTheory.SingleInvolutionClassSylow

/-!
# Odd index of the full projective involution centralizer in PSU₄(3)

A Sylow two-subgroup centralizes some involution. The checked trace and
unitary eigenbasis theorems identify its full projective centralizer with
the standard one, including the anticommuting SU representatives. These
centralizers have the same order and hence the same index. Thus the
standard centralizer has odd index, without using an ambient order formula
or confusing full-unitary conjugation with conjugation inside PSU.

This supplies the local transfer subgroup for the two-primary estimate in
Aschbacher--Smith I.1.4(5), printed p.408 of `refs/quasithin.pdf`.
-/

public section
open Subgroup
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary

/-- The literal full centralizer is an odd-index subgroup of the actual PSU image. -/
theorem standardCentralizer_not_two_dvd_index : ¬ 2 ∣ standardCentralizer.index := by
  let T : Sylow 2 (Carrier 4) := Classical.choice inferInstance
  obtain ⟨z, hz, hT⟩ := T.exists_central_involution
    (standardInvolution_orderOf ▸ orderOf_dvd_natCard standardInvolution)
  obtain ⟨e⟩ := centralizer_models_of_trace_zero
    ElementaryLocal.InvolutionCentralizer.trace_eq_zero_of_projective_involution z hz
  have hc : Nat.card (centralizer ({z} : Set (Carrier 4))) = Nat.card standardCentralizer :=
    Nat.card_congr e.toEquiv
  have hi : (centralizer ({z} : Set (Carrier 4))).index = standardCentralizer.index := by
    have h₁ := (centralizer ({z} : Set (Carrier 4))).card_mul_index
    have h₂ := standardCentralizer.card_mul_index
    rw [hc] at h₁
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h₁.trans h₂.symm)
  intro hd
  apply T.not_dvd_index
  exact (hi ▸ hd).trans (index_dvd_of_le hT)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.TwoPrimary
