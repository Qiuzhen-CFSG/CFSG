module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Kernel.Reduction

/-!
# Kernel checks for CheckedFirst

Every finite identity below is checked by ordinary kernel reduction in bounded
batches. The witnesses come from Kernel/source/generate.py. No external
computation result is accepted as a proof.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate

set_option maxHeartbeats 5000000 in
private theorem firstChecks0 : ∀ j : Fin 25,
    FirstChecks ⟨0 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks1 : ∀ j : Fin 25,
    FirstChecks ⟨25 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks2 : ∀ j : Fin 25,
    FirstChecks ⟨50 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks3 : ∀ j : Fin 25,
    FirstChecks ⟨75 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks4 : ∀ j : Fin 25,
    FirstChecks ⟨100 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks5 : ∀ j : Fin 25,
    FirstChecks ⟨125 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks6 : ∀ j : Fin 25,
    FirstChecks ⟨150 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks7 : ∀ j : Fin 25,
    FirstChecks ⟨175 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks8 : ∀ j : Fin 25,
    FirstChecks ⟨200 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks9 : ∀ j : Fin 25,
    FirstChecks ⟨225 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks10 : ∀ j : Fin 25,
    FirstChecks ⟨250 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks11 : ∀ j : Fin 25,
    FirstChecks ⟨275 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks12 : ∀ j : Fin 25,
    FirstChecks ⟨300 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks13 : ∀ j : Fin 25,
    FirstChecks ⟨325 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks14 : ∀ j : Fin 25,
    FirstChecks ⟨350 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks15 : ∀ j : Fin 25,
    FirstChecks ⟨375 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks16 : ∀ j : Fin 25,
    FirstChecks ⟨400 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks17 : ∀ j : Fin 25,
    FirstChecks ⟨425 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks18 : ∀ j : Fin 25,
    FirstChecks ⟨450 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks19 : ∀ j : Fin 25,
    FirstChecks ⟨475 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks20 : ∀ j : Fin 25,
    FirstChecks ⟨500 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks21 : ∀ j : Fin 25,
    FirstChecks ⟨525 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks22 : ∀ j : Fin 25,
    FirstChecks ⟨550 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks23 : ∀ j : Fin 25,
    FirstChecks ⟨575 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks24 : ∀ j : Fin 25,
    FirstChecks ⟨600 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks25 : ∀ j : Fin 25,
    FirstChecks ⟨625 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks26 : ∀ j : Fin 25,
    FirstChecks ⟨650 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks27 : ∀ j : Fin 25,
    FirstChecks ⟨675 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks28 : ∀ j : Fin 25,
    FirstChecks ⟨700 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks29 : ∀ j : Fin 25,
    FirstChecks ⟨725 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks30 : ∀ j : Fin 25,
    FirstChecks ⟨750 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks31 : ∀ j : Fin 25,
    FirstChecks ⟨775 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks32 : ∀ j : Fin 25,
    FirstChecks ⟨800 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks33 : ∀ j : Fin 25,
    FirstChecks ⟨825 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks34 : ∀ j : Fin 25,
    FirstChecks ⟨850 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks35 : ∀ j : Fin 25,
    FirstChecks ⟨875 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks36 : ∀ j : Fin 25,
    FirstChecks ⟨900 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks37 : ∀ j : Fin 25,
    FirstChecks ⟨925 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks38 : ∀ j : Fin 25,
    FirstChecks ⟨950 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks39 : ∀ j : Fin 25,
    FirstChecks ⟨975 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks40 : ∀ j : Fin 25,
    FirstChecks ⟨1000 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks41 : ∀ j : Fin 25,
    FirstChecks ⟨1025 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks42 : ∀ j : Fin 25,
    FirstChecks ⟨1050 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks43 : ∀ j : Fin 25,
    FirstChecks ⟨1075 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks44 : ∀ j : Fin 25,
    FirstChecks ⟨1100 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks45 : ∀ j : Fin 25,
    FirstChecks ⟨1125 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks46 : ∀ j : Fin 25,
    FirstChecks ⟨1150 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks47 : ∀ j : Fin 25,
    FirstChecks ⟨1175 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

set_option maxHeartbeats 5000000 in
private theorem firstChecks48 : ∀ j : Fin 12,
    FirstChecks ⟨1200 + j.val, by omega⟩ := by
  unfold FirstChecks
  decide +kernel

theorem firstChecks (i : Fin 1212) : FirstChecks i := by
  by_cases hi : i.val < 1200
  · have h : ∀ b : Fin 48, ∀ j : Fin 25,
        FirstChecks ⟨25 * b.val + j.val, by omega⟩ := by
      intro b
      fin_cases b
      · exact firstChecks0
      · exact firstChecks1
      · exact firstChecks2
      · exact firstChecks3
      · exact firstChecks4
      · exact firstChecks5
      · exact firstChecks6
      · exact firstChecks7
      · exact firstChecks8
      · exact firstChecks9
      · exact firstChecks10
      · exact firstChecks11
      · exact firstChecks12
      · exact firstChecks13
      · exact firstChecks14
      · exact firstChecks15
      · exact firstChecks16
      · exact firstChecks17
      · exact firstChecks18
      · exact firstChecks19
      · exact firstChecks20
      · exact firstChecks21
      · exact firstChecks22
      · exact firstChecks23
      · exact firstChecks24
      · exact firstChecks25
      · exact firstChecks26
      · exact firstChecks27
      · exact firstChecks28
      · exact firstChecks29
      · exact firstChecks30
      · exact firstChecks31
      · exact firstChecks32
      · exact firstChecks33
      · exact firstChecks34
      · exact firstChecks35
      · exact firstChecks36
      · exact firstChecks37
      · exact firstChecks38
      · exact firstChecks39
      · exact firstChecks40
      · exact firstChecks41
      · exact firstChecks42
      · exact firstChecks43
      · exact firstChecks44
      · exact firstChecks45
      · exact firstChecks46
      · exact firstChecks47
    have hb : i.val / 25 < 48 := by omega
    have hm : i.val % 25 < 25 := Nat.mod_lt _ (by decide)
    have hx := h ⟨i.val / 25, hb⟩ ⟨i.val % 25, hm⟩
    have heq : (⟨25 * (i.val / 25) + i.val % 25, by omega⟩ : Fin 1212) = i :=
      Fin.ext (Nat.div_add_mod i.val 25)
    exact heq ▸ hx
  · have ht : i.val - 1200 < 12 := by omega
    have hx := firstChecks48 ⟨i.val - 1200, ht⟩
    have heq : (⟨1200 + (i.val - 1200), by omega⟩ : Fin 1212) = i :=
      Fin.ext (by change 1200 + (i.val - 1200) = i.val; omega)
    exact heq ▸ hx

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear.KernelCertificate
