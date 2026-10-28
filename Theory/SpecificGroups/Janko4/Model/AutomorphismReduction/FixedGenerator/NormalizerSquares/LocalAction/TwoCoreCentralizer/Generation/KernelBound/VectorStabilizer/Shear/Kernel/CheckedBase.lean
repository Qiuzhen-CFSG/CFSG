module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.Reduction

/-!
# Kernel checks for CheckedBase

Every finite identity below is checked by ordinary kernel reduction in bounded
batches. The witnesses come from Kernel/source/generate.py. No external
computation result is accepted as a proof.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate

set_option maxHeartbeats 5000000 in
theorem baseChecks : BaseChecks := by
  constructor
  · have h : ∀ (t : Fin 2) (i : Fin 50),
        (OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.mulRows
          (OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.transRows 50
            OrbitCoverCoordinates.LinearMembership.pairingInverseRows)
          (testIURows.get t)).get i = (twistedRows t).get i := by
      simp only [OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.mulRows,
        OrbitCoverCoordinates.LinearMembership.FiniteAlgebra.transRows,
        GeneratorCertificates.get_ofFn]
      decide +kernel
    intro t
    apply Vector.ext
    intro i hi
    exact h t ⟨i, hi⟩
  · decide +kernel

set_option maxHeartbeats 5000000 in
private theorem secondChecks0 : ∀ j : Fin 31,
    SecondChecks ⟨0 + j.val, by omega⟩ := by
  unfold SecondChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem secondChecks1 : ∀ j : Fin 31,
    SecondChecks ⟨31 + j.val, by omega⟩ := by
  unfold SecondChecks
  decide +kernel

theorem secondChecks (i : Fin 62) : SecondChecks i := by
  have h : ∀ b : Fin 2, ∀ j : Fin 31,
      SecondChecks ⟨31 * b.val + j.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact secondChecks0
    · exact secondChecks1
  have hb : i.val / 31 < 2 := by omega
  have hm : i.val % 31 < 31 := Nat.mod_lt _ (by decide)
  have hx := h ⟨i.val / 31, hb⟩ ⟨i.val % 31, hm⟩
  have heq : (⟨31 * (i.val / 31) + i.val % 31, by omega⟩ : Fin 62) = i :=
    Fin.ext (Nat.div_add_mod i.val 31)
  exact heq ▸ hx

set_option maxHeartbeats 5000000 in
private theorem secondRecoveryChecks0 : ∀ j : Fin 21,
    SecondRecoveryChecks ⟨0 + j.val, by omega⟩ := by
  unfold SecondRecoveryChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem secondRecoveryChecks1 : ∀ j : Fin 21,
    SecondRecoveryChecks ⟨21 + j.val, by omega⟩ := by
  unfold SecondRecoveryChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem secondRecoveryChecks2 : ∀ j : Fin 21,
    SecondRecoveryChecks ⟨42 + j.val, by omega⟩ := by
  unfold SecondRecoveryChecks
  decide +kernel

theorem secondRecoveryChecks (i : Fin 63) : SecondRecoveryChecks i := by
  have h : ∀ b : Fin 3, ∀ j : Fin 21,
      SecondRecoveryChecks ⟨21 * b.val + j.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact secondRecoveryChecks0
    · exact secondRecoveryChecks1
    · exact secondRecoveryChecks2
  have hb : i.val / 21 < 3 := by omega
  have hm : i.val % 21 < 21 := Nat.mod_lt _ (by decide)
  have hx := h ⟨i.val / 21, hb⟩ ⟨i.val % 21, hm⟩
  have heq : (⟨21 * (i.val / 21) + i.val % 21, by omega⟩ : Fin 63) = i :=
    Fin.ext (Nat.div_add_mod i.val 21)
  exact heq ▸ hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
