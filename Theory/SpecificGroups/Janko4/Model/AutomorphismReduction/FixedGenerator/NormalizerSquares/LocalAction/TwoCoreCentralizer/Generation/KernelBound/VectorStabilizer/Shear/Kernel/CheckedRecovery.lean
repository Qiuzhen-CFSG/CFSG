module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.Reduction

/-!
# Kernel checks for CheckedRecovery

Every finite identity below is checked by ordinary kernel reduction in bounded
batches. The witnesses come from Kernel/source/generate.py. No external
computation result is accepted as a proof.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks0 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨0 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks1 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨25 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks2 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨50 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks3 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨75 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks4 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨100 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks5 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨125 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks6 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨150 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks7 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨175 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks8 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨200 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks9 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨225 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks10 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨250 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks11 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨275 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks12 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨300 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks13 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨325 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks14 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨350 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks15 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨375 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks16 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨400 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks17 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨425 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks18 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨450 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks19 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨475 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks20 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨500 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks21 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨525 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks22 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨550 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks23 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨575 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks24 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨600 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks25 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨625 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks26 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨650 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks27 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨675 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks28 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨700 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks29 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨725 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks30 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨750 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks31 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨775 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks32 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨800 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks33 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨825 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks34 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨850 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks35 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨875 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks36 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨900 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks37 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨925 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks38 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨950 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks39 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨975 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks40 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1000 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks41 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1025 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks42 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1050 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks43 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1075 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks44 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1100 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks45 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1125 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks46 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1150 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks47 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1175 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks48 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1200 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks49 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1225 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstRecoveryChecks50 : ∀ j : Fin 25,
    FirstRecoveryChecks ⟨1250 + j.val, by omega⟩ := by
  unfold FirstRecoveryChecks
  simp only [firstUnitRows, Vector.toList_ofFn]
  decide +kernel

theorem firstRecoveryChecks (i : Fin 1275) : FirstRecoveryChecks i := by
  have h : ∀ b : Fin 51, ∀ j : Fin 25,
      FirstRecoveryChecks ⟨25 * b.val + j.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact firstRecoveryChecks0
    · exact firstRecoveryChecks1
    · exact firstRecoveryChecks2
    · exact firstRecoveryChecks3
    · exact firstRecoveryChecks4
    · exact firstRecoveryChecks5
    · exact firstRecoveryChecks6
    · exact firstRecoveryChecks7
    · exact firstRecoveryChecks8
    · exact firstRecoveryChecks9
    · exact firstRecoveryChecks10
    · exact firstRecoveryChecks11
    · exact firstRecoveryChecks12
    · exact firstRecoveryChecks13
    · exact firstRecoveryChecks14
    · exact firstRecoveryChecks15
    · exact firstRecoveryChecks16
    · exact firstRecoveryChecks17
    · exact firstRecoveryChecks18
    · exact firstRecoveryChecks19
    · exact firstRecoveryChecks20
    · exact firstRecoveryChecks21
    · exact firstRecoveryChecks22
    · exact firstRecoveryChecks23
    · exact firstRecoveryChecks24
    · exact firstRecoveryChecks25
    · exact firstRecoveryChecks26
    · exact firstRecoveryChecks27
    · exact firstRecoveryChecks28
    · exact firstRecoveryChecks29
    · exact firstRecoveryChecks30
    · exact firstRecoveryChecks31
    · exact firstRecoveryChecks32
    · exact firstRecoveryChecks33
    · exact firstRecoveryChecks34
    · exact firstRecoveryChecks35
    · exact firstRecoveryChecks36
    · exact firstRecoveryChecks37
    · exact firstRecoveryChecks38
    · exact firstRecoveryChecks39
    · exact firstRecoveryChecks40
    · exact firstRecoveryChecks41
    · exact firstRecoveryChecks42
    · exact firstRecoveryChecks43
    · exact firstRecoveryChecks44
    · exact firstRecoveryChecks45
    · exact firstRecoveryChecks46
    · exact firstRecoveryChecks47
    · exact firstRecoveryChecks48
    · exact firstRecoveryChecks49
    · exact firstRecoveryChecks50
  have hb : i.val / 25 < 51 := by omega
  have hm : i.val % 25 < 25 := Nat.mod_lt _ (by decide)
  have hx := h ⟨i.val / 25, hb⟩ ⟨i.val % 25, hm⟩
  have heq : (⟨25 * (i.val / 25) + i.val % 25, by omega⟩ : Fin 1275) = i :=
    Fin.ext (Nat.div_add_mod i.val 25)
  exact heq ▸ hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
