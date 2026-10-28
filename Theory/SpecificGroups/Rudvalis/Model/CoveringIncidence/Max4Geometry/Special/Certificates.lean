module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Data

/-!
# Checked relations for the Rudvalis special-core words

Only the three marked-basis comparisons use the degree-4060 representation.
Every square and swap is checked by at most 460 structural collection steps
in the certified fourteen-letter Sylow presentation. Splitting the finite
swap table into rows and checking declarations sequentially bounds kernel
memory; no native evaluation or external computation is trusted.
Source: Aschbacher--Smith I.2.2(7), pp.412--413; GLS3 Table 5.3r, pp.291--292.
-/

namespace Rudvalis.CoveringIncidence.Max4Special.Certificate
open SylowOvergroups.RadicalCoverage.LocalCover.CatalogueCertificate Collection
set_option Elab.async false

set_option maxRecDepth 30000 in
public theorem center_word_permutation : ∀ i : Fin 3,
    ((centerWord i).map pcPermutation).prod =
      elementaryPermutation i.castSucc.castSucc.castSucc := by
  intro i
  fin_cases i <;> apply Equiv.ext <;> apply Rudvalis.OrderCertificate.allFin <;> decide +kernel


set_option maxRecDepth 6000 in
public theorem square_check : ∀ i : Fin 11,
    collect 460 (word i ++ word i) = collect 460 (centralWord (squareCode i)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_0 : ∀ j : Fin 11,
    collect 460 (word 0 ++ word j) =
      collect 460 (centralWord (commutatorCode 0 j) ++ (word j ++ word 0)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_1 : ∀ j : Fin 11,
    collect 460 (word 1 ++ word j) =
      collect 460 (centralWord (commutatorCode 1 j) ++ (word j ++ word 1)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_2 : ∀ j : Fin 11,
    collect 460 (word 2 ++ word j) =
      collect 460 (centralWord (commutatorCode 2 j) ++ (word j ++ word 2)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_3 : ∀ j : Fin 11,
    collect 460 (word 3 ++ word j) =
      collect 460 (centralWord (commutatorCode 3 j) ++ (word j ++ word 3)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_4 : ∀ j : Fin 11,
    collect 460 (word 4 ++ word j) =
      collect 460 (centralWord (commutatorCode 4 j) ++ (word j ++ word 4)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_5 : ∀ j : Fin 11,
    collect 460 (word 5 ++ word j) =
      collect 460 (centralWord (commutatorCode 5 j) ++ (word j ++ word 5)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_6 : ∀ j : Fin 11,
    collect 460 (word 6 ++ word j) =
      collect 460 (centralWord (commutatorCode 6 j) ++ (word j ++ word 6)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_7 : ∀ j : Fin 11,
    collect 460 (word 7 ++ word j) =
      collect 460 (centralWord (commutatorCode 7 j) ++ (word j ++ word 7)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_8 : ∀ j : Fin 11,
    collect 460 (word 8 ++ word j) =
      collect 460 (centralWord (commutatorCode 8 j) ++ (word j ++ word 8)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_9 : ∀ j : Fin 11,
    collect 460 (word 9 ++ word j) =
      collect 460 (centralWord (commutatorCode 9 j) ++ (word j ++ word 9)) := by
  decide +kernel

set_option maxRecDepth 6000 in
private theorem swap_check_10 : ∀ j : Fin 11,
    collect 460 (word 10 ++ word j) =
      collect 460 (centralWord (commutatorCode 10 j) ++ (word j ++ word 10)) := by
  decide +kernel

public theorem swap_check (i j : Fin 11) :
    collect 460 (word i ++ word j) =
      collect 460 (centralWord (commutatorCode i j) ++ (word j ++ word i)) := by
  fin_cases i
  · exact swap_check_0 j
  · exact swap_check_1 j
  · exact swap_check_2 j
  · exact swap_check_3 j
  · exact swap_check_4 j
  · exact swap_check_5 j
  · exact swap_check_6 j
  · exact swap_check_7 j
  · exact swap_check_8 j
  · exact swap_check_9 j
  · exact swap_check_10 j

end Rudvalis.CoveringIncidence.Max4Special.Certificate
