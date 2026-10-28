module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Maps
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Checks
import Mathlib.Tactic.FinCases
/-!
# Two permutation relations for the Fi₂₃ elementary eight

The second source generator has cube one. The certified centralizer
involution commutes with its conjugate by that generator. Balanced checks
cover every letter of the literal 31671-point action; all calculations use
the existing source-compared lookup maps.
Source: ATLAS F23G1-p31671B0; Aschbacher–Smith A.2.12, printed p.36.
-/
public section
namespace Sporadic.Fischer.Fi23.TwoRank.Checks
open CentralizerSection.CandidateCertificate
set_option Elab.async false
private def test (i : Nat) : Bool := if h : i < 31671 then
  let x : Fin 31671 := ⟨i,h⟩
  decide (bMap (bMap (bMap x)) = x ∧
    cMap (bMap (bMap (cMap (bMap x)))) = bMap (bMap (cMap (bMap (cMap x)))))
  else true
private theorem block0 : checkRange test 10 0 = true := by decide +kernel
private theorem block1 : checkRange test 10 1024 = true := by decide +kernel
private theorem block2 : checkRange test 10 2048 = true := by decide +kernel
private theorem block3 : checkRange test 10 3072 = true := by decide +kernel
private theorem block4 : checkRange test 10 4096 = true := by decide +kernel
private theorem block5 : checkRange test 10 5120 = true := by decide +kernel
private theorem block6 : checkRange test 10 6144 = true := by decide +kernel
private theorem block7 : checkRange test 10 7168 = true := by decide +kernel
private theorem block8 : checkRange test 10 8192 = true := by decide +kernel
private theorem block9 : checkRange test 10 9216 = true := by decide +kernel
private theorem block10 : checkRange test 10 10240 = true := by decide +kernel
private theorem block11 : checkRange test 10 11264 = true := by decide +kernel
private theorem block12 : checkRange test 10 12288 = true := by decide +kernel
private theorem block13 : checkRange test 10 13312 = true := by decide +kernel
private theorem block14 : checkRange test 10 14336 = true := by decide +kernel
private theorem block15 : checkRange test 10 15360 = true := by decide +kernel
private theorem block16 : checkRange test 10 16384 = true := by decide +kernel
private theorem block17 : checkRange test 10 17408 = true := by decide +kernel
private theorem block18 : checkRange test 10 18432 = true := by decide +kernel
private theorem block19 : checkRange test 10 19456 = true := by decide +kernel
private theorem block20 : checkRange test 10 20480 = true := by decide +kernel
private theorem block21 : checkRange test 10 21504 = true := by decide +kernel
private theorem block22 : checkRange test 10 22528 = true := by decide +kernel
private theorem block23 : checkRange test 10 23552 = true := by decide +kernel
private theorem block24 : checkRange test 10 24576 = true := by decide +kernel
private theorem block25 : checkRange test 10 25600 = true := by decide +kernel
private theorem block26 : checkRange test 10 26624 = true := by decide +kernel
private theorem block27 : checkRange test 10 27648 = true := by decide +kernel
private theorem block28 : checkRange test 10 28672 = true := by decide +kernel
private theorem block29 : checkRange test 10 29696 = true := by decide +kernel
private theorem block30 : checkRange test 10 30720 = true := by decide +kernel
private theorem blocks (k : Fin 31) : checkRange test 10 (1024*k.val) = true := by
  fin_cases k
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7
  · exact block8
  · exact block9
  · exact block10
  · exact block11
  · exact block12
  · exact block13
  · exact block14
  · exact block15
  · exact block16
  · exact block17
  · exact block18
  · exact block19
  · exact block20
  · exact block21
  · exact block22
  · exact block23
  · exact block24
  · exact block25
  · exact block26
  · exact block27
  · exact block28
  · exact block29
  · exact block30
private theorem checked (i : Fin 31671) :
    bMap (bMap (bMap i)) = i ∧
      cMap (bMap (bMap (cMap (bMap i)))) = bMap (bMap (cMap (bMap (cMap i)))) := by
  have hk : i.val / 1024 < 31 := by omega
  have hh := (checkRange_spec test 10 (1024 * (i.val / 1024))).mp
    (blocks ⟨i.val / 1024,hk⟩) i.val (by omega) (by norm_num; omega)
  simpa only [test, dif_pos i.isLt, decide_eq_true_eq] using hh
/-- The actual second-generator lookup has cube one. -/
theorem b_cube (i : Fin 31671) : bMap (bMap (bMap i)) = i := (checked i).1
/-- The centralizer involution commutes with its first conjugate. -/
theorem commute (i : Fin 31671) :
    cMap (bMap (bMap (cMap (bMap i)))) = bMap (bMap (cMap (bMap (cMap i)))) := (checked i).2
end Sporadic.Fischer.Fi23.TwoRank.Checks
