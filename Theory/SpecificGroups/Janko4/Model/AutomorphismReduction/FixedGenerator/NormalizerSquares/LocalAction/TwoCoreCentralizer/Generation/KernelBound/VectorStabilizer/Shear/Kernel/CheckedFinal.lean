module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.Reduction

/-!
# Kernel checks for CheckedFinal

Every finite identity below is checked by ordinary kernel reduction in bounded
batches. The witnesses come from Kernel/source/generate.py. No external
computation result is accepted as a proof.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate

set_option maxHeartbeats 5000000 in
private theorem finalChecks0 : ∀ j : Fin 25,
    FinalChecks ⟨0 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks1 : ∀ j : Fin 25,
    FinalChecks ⟨25 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks2 : ∀ j : Fin 25,
    FinalChecks ⟨50 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks3 : ∀ j : Fin 25,
    FinalChecks ⟨75 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks4 : ∀ j : Fin 25,
    FinalChecks ⟨100 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks5 : ∀ j : Fin 25,
    FinalChecks ⟨125 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks6 : ∀ j : Fin 25,
    FinalChecks ⟨150 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks7 : ∀ j : Fin 25,
    FinalChecks ⟨175 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks8 : ∀ j : Fin 25,
    FinalChecks ⟨200 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks9 : ∀ j : Fin 25,
    FinalChecks ⟨225 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks10 : ∀ j : Fin 25,
    FinalChecks ⟨250 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks11 : ∀ j : Fin 25,
    FinalChecks ⟨275 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks12 : ∀ j : Fin 25,
    FinalChecks ⟨300 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks13 : ∀ j : Fin 25,
    FinalChecks ⟨325 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks14 : ∀ j : Fin 25,
    FinalChecks ⟨350 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks15 : ∀ j : Fin 25,
    FinalChecks ⟨375 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks16 : ∀ j : Fin 25,
    FinalChecks ⟨400 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks17 : ∀ j : Fin 25,
    FinalChecks ⟨425 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks18 : ∀ j : Fin 25,
    FinalChecks ⟨450 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks19 : ∀ j : Fin 25,
    FinalChecks ⟨475 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks20 : ∀ j : Fin 25,
    FinalChecks ⟨500 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks21 : ∀ j : Fin 25,
    FinalChecks ⟨525 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks22 : ∀ j : Fin 25,
    FinalChecks ⟨550 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks23 : ∀ j : Fin 25,
    FinalChecks ⟨575 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks24 : ∀ j : Fin 25,
    FinalChecks ⟨600 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks25 : ∀ j : Fin 25,
    FinalChecks ⟨625 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks26 : ∀ j : Fin 25,
    FinalChecks ⟨650 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks27 : ∀ j : Fin 25,
    FinalChecks ⟨675 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks28 : ∀ j : Fin 25,
    FinalChecks ⟨700 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks29 : ∀ j : Fin 25,
    FinalChecks ⟨725 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks30 : ∀ j : Fin 25,
    FinalChecks ⟨750 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks31 : ∀ j : Fin 25,
    FinalChecks ⟨775 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks32 : ∀ j : Fin 25,
    FinalChecks ⟨800 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks33 : ∀ j : Fin 25,
    FinalChecks ⟨825 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks34 : ∀ j : Fin 25,
    FinalChecks ⟨850 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks35 : ∀ j : Fin 25,
    FinalChecks ⟨875 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks36 : ∀ j : Fin 25,
    FinalChecks ⟨900 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks37 : ∀ j : Fin 25,
    FinalChecks ⟨925 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks38 : ∀ j : Fin 25,
    FinalChecks ⟨950 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks39 : ∀ j : Fin 25,
    FinalChecks ⟨975 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks40 : ∀ j : Fin 25,
    FinalChecks ⟨1000 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks41 : ∀ j : Fin 25,
    FinalChecks ⟨1025 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks42 : ∀ j : Fin 25,
    FinalChecks ⟨1050 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks43 : ∀ j : Fin 25,
    FinalChecks ⟨1075 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks44 : ∀ j : Fin 25,
    FinalChecks ⟨1100 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks45 : ∀ j : Fin 25,
    FinalChecks ⟨1125 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks46 : ∀ j : Fin 25,
    FinalChecks ⟨1150 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks47 : ∀ j : Fin 25,
    FinalChecks ⟨1175 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks48 : ∀ j : Fin 25,
    FinalChecks ⟨1200 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks49 : ∀ j : Fin 25,
    FinalChecks ⟨1225 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem finalChecks50 : ∀ j : Fin 25,
    FinalChecks ⟨1250 + j.val, by omega⟩ := by
  unfold FinalChecks
  decide +kernel

theorem finalChecks (i : Fin 1275) : FinalChecks i := by
  have h : ∀ b : Fin 51, ∀ j : Fin 25,
      FinalChecks ⟨25 * b.val + j.val, by omega⟩ := by
    intro b
    fin_cases b
    · exact finalChecks0
    · exact finalChecks1
    · exact finalChecks2
    · exact finalChecks3
    · exact finalChecks4
    · exact finalChecks5
    · exact finalChecks6
    · exact finalChecks7
    · exact finalChecks8
    · exact finalChecks9
    · exact finalChecks10
    · exact finalChecks11
    · exact finalChecks12
    · exact finalChecks13
    · exact finalChecks14
    · exact finalChecks15
    · exact finalChecks16
    · exact finalChecks17
    · exact finalChecks18
    · exact finalChecks19
    · exact finalChecks20
    · exact finalChecks21
    · exact finalChecks22
    · exact finalChecks23
    · exact finalChecks24
    · exact finalChecks25
    · exact finalChecks26
    · exact finalChecks27
    · exact finalChecks28
    · exact finalChecks29
    · exact finalChecks30
    · exact finalChecks31
    · exact finalChecks32
    · exact finalChecks33
    · exact finalChecks34
    · exact finalChecks35
    · exact finalChecks36
    · exact finalChecks37
    · exact finalChecks38
    · exact finalChecks39
    · exact finalChecks40
    · exact finalChecks41
    · exact finalChecks42
    · exact finalChecks43
    · exact finalChecks44
    · exact finalChecks45
    · exact finalChecks46
    · exact finalChecks47
    · exact finalChecks48
    · exact finalChecks49
    · exact finalChecks50
  have hb : i.val / 25 < 51 := by omega
  have hm : i.val % 25 < 25 := Nat.mod_lt _ (by decide)
  have hx := h ⟨i.val / 25, hb⟩ ⟨i.val % 25, hm⟩
  have heq : (⟨25 * (i.val / 25) + i.val % 25, by omega⟩ : Fin 1275) = i :=
    Fin.ext (Nat.div_add_mod i.val 25)
  exact heq ▸ hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
