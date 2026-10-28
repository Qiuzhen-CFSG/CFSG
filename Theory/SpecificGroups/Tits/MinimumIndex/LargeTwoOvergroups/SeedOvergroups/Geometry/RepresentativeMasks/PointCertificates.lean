module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks.PointData
import Mathlib.Tactic.FinCases

/-!
# Certification of the reusable point tables

Each table is checked on all 1600 points against its literal packed word.
For inverse conjugators, a right-inverse check and the already identified
forward permutation suffice. Declarations are checked sequentially to bound
memory. Source: Parrott (1972), p.683; the tables are generated from Packed.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks
set_option Elab.async false

set_option maxRecDepth 10000 in
private theorem conj_0 : ∀ p : Fin 1600, tableMap (conjData 0) p = fastConjugator 0 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_1 : ∀ p : Fin 1600, tableMap (conjData 1) p = fastConjugator 1 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_2 : ∀ p : Fin 1600, tableMap (conjData 2) p = fastConjugator 2 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_3 : ∀ p : Fin 1600, tableMap (conjData 3) p = fastConjugator 3 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_4 : ∀ p : Fin 1600, tableMap (conjData 4) p = fastConjugator 4 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_5 : ∀ p : Fin 1600, tableMap (conjData 5) p = fastConjugator 5 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_6 : ∀ p : Fin 1600, tableMap (conjData 6) p = fastConjugator 6 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_7 : ∀ p : Fin 1600, tableMap (conjData 7) p = fastConjugator 7 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_8 : ∀ p : Fin 1600, tableMap (conjData 8) p = fastConjugator 8 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_9 : ∀ p : Fin 1600, tableMap (conjData 9) p = fastConjugator 9 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_10 : ∀ p : Fin 1600, tableMap (conjData 10) p = fastConjugator 10 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_11 : ∀ p : Fin 1600, tableMap (conjData 11) p = fastConjugator 11 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_12 : ∀ p : Fin 1600, tableMap (conjData 12) p = fastConjugator 12 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_13 : ∀ p : Fin 1600, tableMap (conjData 13) p = fastConjugator 13 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_14 : ∀ p : Fin 1600, tableMap (conjData 14) p = fastConjugator 14 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_15 : ∀ p : Fin 1600, tableMap (conjData 15) p = fastConjugator 15 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_16 : ∀ p : Fin 1600, tableMap (conjData 16) p = fastConjugator 16 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_17 : ∀ p : Fin 1600, tableMap (conjData 17) p = fastConjugator 17 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_18 : ∀ p : Fin 1600, tableMap (conjData 18) p = fastConjugator 18 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_19 : ∀ p : Fin 1600, tableMap (conjData 19) p = fastConjugator 19 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_20 : ∀ p : Fin 1600, tableMap (conjData 20) p = fastConjugator 20 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_21 : ∀ p : Fin 1600, tableMap (conjData 21) p = fastConjugator 21 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_22 : ∀ p : Fin 1600, tableMap (conjData 22) p = fastConjugator 22 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_23 : ∀ p : Fin 1600, tableMap (conjData 23) p = fastConjugator 23 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_24 : ∀ p : Fin 1600, tableMap (conjData 24) p = fastConjugator 24 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_25 : ∀ p : Fin 1600, tableMap (conjData 25) p = fastConjugator 25 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_26 : ∀ p : Fin 1600, tableMap (conjData 26) p = fastConjugator 26 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_27 : ∀ p : Fin 1600, tableMap (conjData 27) p = fastConjugator 27 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_28 : ∀ p : Fin 1600, tableMap (conjData 28) p = fastConjugator 28 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_29 : ∀ p : Fin 1600, tableMap (conjData 29) p = fastConjugator 29 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_30 : ∀ p : Fin 1600, tableMap (conjData 30) p = fastConjugator 30 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_31 : ∀ p : Fin 1600, tableMap (conjData 31) p = fastConjugator 31 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_32 : ∀ p : Fin 1600, tableMap (conjData 32) p = fastConjugator 32 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_33 : ∀ p : Fin 1600, tableMap (conjData 33) p = fastConjugator 33 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_34 : ∀ p : Fin 1600, tableMap (conjData 34) p = fastConjugator 34 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_35 : ∀ p : Fin 1600, tableMap (conjData 35) p = fastConjugator 35 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_36 : ∀ p : Fin 1600, tableMap (conjData 36) p = fastConjugator 36 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem conj_37 : ∀ p : Fin 1600, tableMap (conjData 37) p = fastConjugator 37 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem conj_correct (j : Fin 38) (p : Fin 1600) :
    tableMap (conjData j.val) p = fastConjugator j p := by
  fin_cases j
  · exact conj_0 p
  · exact conj_1 p
  · exact conj_2 p
  · exact conj_3 p
  · exact conj_4 p
  · exact conj_5 p
  · exact conj_6 p
  · exact conj_7 p
  · exact conj_8 p
  · exact conj_9 p
  · exact conj_10 p
  · exact conj_11 p
  · exact conj_12 p
  · exact conj_13 p
  · exact conj_14 p
  · exact conj_15 p
  · exact conj_16 p
  · exact conj_17 p
  · exact conj_18 p
  · exact conj_19 p
  · exact conj_20 p
  · exact conj_21 p
  · exact conj_22 p
  · exact conj_23 p
  · exact conj_24 p
  · exact conj_25 p
  · exact conj_26 p
  · exact conj_27 p
  · exact conj_28 p
  · exact conj_29 p
  · exact conj_30 p
  · exact conj_31 p
  · exact conj_32 p
  · exact conj_33 p
  · exact conj_34 p
  · exact conj_35 p
  · exact conj_36 p
  · exact conj_37 p

set_option maxRecDepth 10000 in
private theorem inv_0 : ∀ p : Fin 1600, tableMap (conjData 0) (tableMap (invConjData 0) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_1 : ∀ p : Fin 1600, tableMap (conjData 1) (tableMap (invConjData 1) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_2 : ∀ p : Fin 1600, tableMap (conjData 2) (tableMap (invConjData 2) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_3 : ∀ p : Fin 1600, tableMap (conjData 3) (tableMap (invConjData 3) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_4 : ∀ p : Fin 1600, tableMap (conjData 4) (tableMap (invConjData 4) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_5 : ∀ p : Fin 1600, tableMap (conjData 5) (tableMap (invConjData 5) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_6 : ∀ p : Fin 1600, tableMap (conjData 6) (tableMap (invConjData 6) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_7 : ∀ p : Fin 1600, tableMap (conjData 7) (tableMap (invConjData 7) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_8 : ∀ p : Fin 1600, tableMap (conjData 8) (tableMap (invConjData 8) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_9 : ∀ p : Fin 1600, tableMap (conjData 9) (tableMap (invConjData 9) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_10 : ∀ p : Fin 1600, tableMap (conjData 10) (tableMap (invConjData 10) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_11 : ∀ p : Fin 1600, tableMap (conjData 11) (tableMap (invConjData 11) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_12 : ∀ p : Fin 1600, tableMap (conjData 12) (tableMap (invConjData 12) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_13 : ∀ p : Fin 1600, tableMap (conjData 13) (tableMap (invConjData 13) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_14 : ∀ p : Fin 1600, tableMap (conjData 14) (tableMap (invConjData 14) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_15 : ∀ p : Fin 1600, tableMap (conjData 15) (tableMap (invConjData 15) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_16 : ∀ p : Fin 1600, tableMap (conjData 16) (tableMap (invConjData 16) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_17 : ∀ p : Fin 1600, tableMap (conjData 17) (tableMap (invConjData 17) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_18 : ∀ p : Fin 1600, tableMap (conjData 18) (tableMap (invConjData 18) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_19 : ∀ p : Fin 1600, tableMap (conjData 19) (tableMap (invConjData 19) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_20 : ∀ p : Fin 1600, tableMap (conjData 20) (tableMap (invConjData 20) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_21 : ∀ p : Fin 1600, tableMap (conjData 21) (tableMap (invConjData 21) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_22 : ∀ p : Fin 1600, tableMap (conjData 22) (tableMap (invConjData 22) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_23 : ∀ p : Fin 1600, tableMap (conjData 23) (tableMap (invConjData 23) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_24 : ∀ p : Fin 1600, tableMap (conjData 24) (tableMap (invConjData 24) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_25 : ∀ p : Fin 1600, tableMap (conjData 25) (tableMap (invConjData 25) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_26 : ∀ p : Fin 1600, tableMap (conjData 26) (tableMap (invConjData 26) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_27 : ∀ p : Fin 1600, tableMap (conjData 27) (tableMap (invConjData 27) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_28 : ∀ p : Fin 1600, tableMap (conjData 28) (tableMap (invConjData 28) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_29 : ∀ p : Fin 1600, tableMap (conjData 29) (tableMap (invConjData 29) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_30 : ∀ p : Fin 1600, tableMap (conjData 30) (tableMap (invConjData 30) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_31 : ∀ p : Fin 1600, tableMap (conjData 31) (tableMap (invConjData 31) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_32 : ∀ p : Fin 1600, tableMap (conjData 32) (tableMap (invConjData 32) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_33 : ∀ p : Fin 1600, tableMap (conjData 33) (tableMap (invConjData 33) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_34 : ∀ p : Fin 1600, tableMap (conjData 34) (tableMap (invConjData 34) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_35 : ∀ p : Fin 1600, tableMap (conjData 35) (tableMap (invConjData 35) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_36 : ∀ p : Fin 1600, tableMap (conjData 36) (tableMap (invConjData 36) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem inv_37 : ∀ p : Fin 1600, tableMap (conjData 37) (tableMap (invConjData 37) p) = p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem inv_correct (j : Fin 38) (p : Fin 1600) :
    tableMap (conjData j.val) (tableMap (invConjData j.val) p) = p := by
  fin_cases j
  · exact inv_0 p
  · exact inv_1 p
  · exact inv_2 p
  · exact inv_3 p
  · exact inv_4 p
  · exact inv_5 p
  · exact inv_6 p
  · exact inv_7 p
  · exact inv_8 p
  · exact inv_9 p
  · exact inv_10 p
  · exact inv_11 p
  · exact inv_12 p
  · exact inv_13 p
  · exact inv_14 p
  · exact inv_15 p
  · exact inv_16 p
  · exact inv_17 p
  · exact inv_18 p
  · exact inv_19 p
  · exact inv_20 p
  · exact inv_21 p
  · exact inv_22 p
  · exact inv_23 p
  · exact inv_24 p
  · exact inv_25 p
  · exact inv_26 p
  · exact inv_27 p
  · exact inv_28 p
  · exact inv_29 p
  · exact inv_30 p
  · exact inv_31 p
  · exact inv_32 p
  · exact inv_33 p
  · exact inv_34 p
  · exact inv_35 p
  · exact inv_36 p
  · exact inv_37 p

set_option maxRecDepth 10000 in
private theorem low_0 : ∀ p : Fin 1600, tableMap (lowData 0) p = fastNormalForm 0 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_1 : ∀ p : Fin 1600, tableMap (lowData 1) p = fastNormalForm 1 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_2 : ∀ p : Fin 1600, tableMap (lowData 2) p = fastNormalForm 2 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_3 : ∀ p : Fin 1600, tableMap (lowData 3) p = fastNormalForm 3 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_4 : ∀ p : Fin 1600, tableMap (lowData 4) p = fastNormalForm 4 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_5 : ∀ p : Fin 1600, tableMap (lowData 5) p = fastNormalForm 5 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_6 : ∀ p : Fin 1600, tableMap (lowData 6) p = fastNormalForm 6 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_7 : ∀ p : Fin 1600, tableMap (lowData 7) p = fastNormalForm 7 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_8 : ∀ p : Fin 1600, tableMap (lowData 8) p = fastNormalForm 8 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_9 : ∀ p : Fin 1600, tableMap (lowData 9) p = fastNormalForm 9 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_10 : ∀ p : Fin 1600, tableMap (lowData 10) p = fastNormalForm 10 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_11 : ∀ p : Fin 1600, tableMap (lowData 11) p = fastNormalForm 11 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_12 : ∀ p : Fin 1600, tableMap (lowData 12) p = fastNormalForm 12 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_13 : ∀ p : Fin 1600, tableMap (lowData 13) p = fastNormalForm 13 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_14 : ∀ p : Fin 1600, tableMap (lowData 14) p = fastNormalForm 14 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_15 : ∀ p : Fin 1600, tableMap (lowData 15) p = fastNormalForm 15 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_16 : ∀ p : Fin 1600, tableMap (lowData 16) p = fastNormalForm 16 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_17 : ∀ p : Fin 1600, tableMap (lowData 17) p = fastNormalForm 17 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_18 : ∀ p : Fin 1600, tableMap (lowData 18) p = fastNormalForm 18 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_19 : ∀ p : Fin 1600, tableMap (lowData 19) p = fastNormalForm 19 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_20 : ∀ p : Fin 1600, tableMap (lowData 20) p = fastNormalForm 20 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_21 : ∀ p : Fin 1600, tableMap (lowData 21) p = fastNormalForm 21 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_22 : ∀ p : Fin 1600, tableMap (lowData 22) p = fastNormalForm 22 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_23 : ∀ p : Fin 1600, tableMap (lowData 23) p = fastNormalForm 23 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_24 : ∀ p : Fin 1600, tableMap (lowData 24) p = fastNormalForm 24 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_25 : ∀ p : Fin 1600, tableMap (lowData 25) p = fastNormalForm 25 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_26 : ∀ p : Fin 1600, tableMap (lowData 26) p = fastNormalForm 26 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_27 : ∀ p : Fin 1600, tableMap (lowData 27) p = fastNormalForm 27 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_28 : ∀ p : Fin 1600, tableMap (lowData 28) p = fastNormalForm 28 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_29 : ∀ p : Fin 1600, tableMap (lowData 29) p = fastNormalForm 29 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_30 : ∀ p : Fin 1600, tableMap (lowData 30) p = fastNormalForm 30 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem low_31 : ∀ p : Fin 1600, tableMap (lowData 31) p = fastNormalForm 31 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem low_correct (j : Fin 32) (p : Fin 1600) :
    tableMap (lowData j.val) p = fastNormalForm ⟨j.val, by omega⟩ p := by
  fin_cases j
  · exact low_0 p
  · exact low_1 p
  · exact low_2 p
  · exact low_3 p
  · exact low_4 p
  · exact low_5 p
  · exact low_6 p
  · exact low_7 p
  · exact low_8 p
  · exact low_9 p
  · exact low_10 p
  · exact low_11 p
  · exact low_12 p
  · exact low_13 p
  · exact low_14 p
  · exact low_15 p
  · exact low_16 p
  · exact low_17 p
  · exact low_18 p
  · exact low_19 p
  · exact low_20 p
  · exact low_21 p
  · exact low_22 p
  · exact low_23 p
  · exact low_24 p
  · exact low_25 p
  · exact low_26 p
  · exact low_27 p
  · exact low_28 p
  · exact low_29 p
  · exact low_30 p
  · exact low_31 p

set_option maxRecDepth 10000 in
private theorem high_0 : ∀ p : Fin 1600, tableMap (highData 0) p = fastNormalForm 0 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_1 : ∀ p : Fin 1600, tableMap (highData 1) p = fastNormalForm 32 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_2 : ∀ p : Fin 1600, tableMap (highData 2) p = fastNormalForm 64 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_3 : ∀ p : Fin 1600, tableMap (highData 3) p = fastNormalForm 96 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_4 : ∀ p : Fin 1600, tableMap (highData 4) p = fastNormalForm 128 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_5 : ∀ p : Fin 1600, tableMap (highData 5) p = fastNormalForm 160 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_6 : ∀ p : Fin 1600, tableMap (highData 6) p = fastNormalForm 192 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_7 : ∀ p : Fin 1600, tableMap (highData 7) p = fastNormalForm 224 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_8 : ∀ p : Fin 1600, tableMap (highData 8) p = fastNormalForm 256 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_9 : ∀ p : Fin 1600, tableMap (highData 9) p = fastNormalForm 288 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_10 : ∀ p : Fin 1600, tableMap (highData 10) p = fastNormalForm 320 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_11 : ∀ p : Fin 1600, tableMap (highData 11) p = fastNormalForm 352 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_12 : ∀ p : Fin 1600, tableMap (highData 12) p = fastNormalForm 384 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_13 : ∀ p : Fin 1600, tableMap (highData 13) p = fastNormalForm 416 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_14 : ∀ p : Fin 1600, tableMap (highData 14) p = fastNormalForm 448 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_15 : ∀ p : Fin 1600, tableMap (highData 15) p = fastNormalForm 480 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_16 : ∀ p : Fin 1600, tableMap (highData 16) p = fastNormalForm 512 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_17 : ∀ p : Fin 1600, tableMap (highData 17) p = fastNormalForm 544 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_18 : ∀ p : Fin 1600, tableMap (highData 18) p = fastNormalForm 576 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_19 : ∀ p : Fin 1600, tableMap (highData 19) p = fastNormalForm 608 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_20 : ∀ p : Fin 1600, tableMap (highData 20) p = fastNormalForm 640 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_21 : ∀ p : Fin 1600, tableMap (highData 21) p = fastNormalForm 672 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_22 : ∀ p : Fin 1600, tableMap (highData 22) p = fastNormalForm 704 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_23 : ∀ p : Fin 1600, tableMap (highData 23) p = fastNormalForm 736 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_24 : ∀ p : Fin 1600, tableMap (highData 24) p = fastNormalForm 768 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_25 : ∀ p : Fin 1600, tableMap (highData 25) p = fastNormalForm 800 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_26 : ∀ p : Fin 1600, tableMap (highData 26) p = fastNormalForm 832 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_27 : ∀ p : Fin 1600, tableMap (highData 27) p = fastNormalForm 864 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_28 : ∀ p : Fin 1600, tableMap (highData 28) p = fastNormalForm 896 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_29 : ∀ p : Fin 1600, tableMap (highData 29) p = fastNormalForm 928 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_30 : ∀ p : Fin 1600, tableMap (highData 30) p = fastNormalForm 960 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_31 : ∀ p : Fin 1600, tableMap (highData 31) p = fastNormalForm 992 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_32 : ∀ p : Fin 1600, tableMap (highData 32) p = fastNormalForm 1024 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_33 : ∀ p : Fin 1600, tableMap (highData 33) p = fastNormalForm 1056 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_34 : ∀ p : Fin 1600, tableMap (highData 34) p = fastNormalForm 1088 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_35 : ∀ p : Fin 1600, tableMap (highData 35) p = fastNormalForm 1120 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_36 : ∀ p : Fin 1600, tableMap (highData 36) p = fastNormalForm 1152 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_37 : ∀ p : Fin 1600, tableMap (highData 37) p = fastNormalForm 1184 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_38 : ∀ p : Fin 1600, tableMap (highData 38) p = fastNormalForm 1216 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_39 : ∀ p : Fin 1600, tableMap (highData 39) p = fastNormalForm 1248 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_40 : ∀ p : Fin 1600, tableMap (highData 40) p = fastNormalForm 1280 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_41 : ∀ p : Fin 1600, tableMap (highData 41) p = fastNormalForm 1312 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_42 : ∀ p : Fin 1600, tableMap (highData 42) p = fastNormalForm 1344 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_43 : ∀ p : Fin 1600, tableMap (highData 43) p = fastNormalForm 1376 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_44 : ∀ p : Fin 1600, tableMap (highData 44) p = fastNormalForm 1408 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_45 : ∀ p : Fin 1600, tableMap (highData 45) p = fastNormalForm 1440 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_46 : ∀ p : Fin 1600, tableMap (highData 46) p = fastNormalForm 1472 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_47 : ∀ p : Fin 1600, tableMap (highData 47) p = fastNormalForm 1504 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_48 : ∀ p : Fin 1600, tableMap (highData 48) p = fastNormalForm 1536 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_49 : ∀ p : Fin 1600, tableMap (highData 49) p = fastNormalForm 1568 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_50 : ∀ p : Fin 1600, tableMap (highData 50) p = fastNormalForm 1600 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_51 : ∀ p : Fin 1600, tableMap (highData 51) p = fastNormalForm 1632 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_52 : ∀ p : Fin 1600, tableMap (highData 52) p = fastNormalForm 1664 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_53 : ∀ p : Fin 1600, tableMap (highData 53) p = fastNormalForm 1696 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_54 : ∀ p : Fin 1600, tableMap (highData 54) p = fastNormalForm 1728 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_55 : ∀ p : Fin 1600, tableMap (highData 55) p = fastNormalForm 1760 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_56 : ∀ p : Fin 1600, tableMap (highData 56) p = fastNormalForm 1792 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_57 : ∀ p : Fin 1600, tableMap (highData 57) p = fastNormalForm 1824 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_58 : ∀ p : Fin 1600, tableMap (highData 58) p = fastNormalForm 1856 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_59 : ∀ p : Fin 1600, tableMap (highData 59) p = fastNormalForm 1888 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_60 : ∀ p : Fin 1600, tableMap (highData 60) p = fastNormalForm 1920 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_61 : ∀ p : Fin 1600, tableMap (highData 61) p = fastNormalForm 1952 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_62 : ∀ p : Fin 1600, tableMap (highData 62) p = fastNormalForm 1984 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem high_63 : ∀ p : Fin 1600, tableMap (highData 63) p = fastNormalForm 2016 p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem high_correct (j : Fin 64) (p : Fin 1600) :
    tableMap (highData j.val) p = fastNormalForm ⟨32 * j.val, by omega⟩ p := by
  fin_cases j
  · exact high_0 p
  · exact high_1 p
  · exact high_2 p
  · exact high_3 p
  · exact high_4 p
  · exact high_5 p
  · exact high_6 p
  · exact high_7 p
  · exact high_8 p
  · exact high_9 p
  · exact high_10 p
  · exact high_11 p
  · exact high_12 p
  · exact high_13 p
  · exact high_14 p
  · exact high_15 p
  · exact high_16 p
  · exact high_17 p
  · exact high_18 p
  · exact high_19 p
  · exact high_20 p
  · exact high_21 p
  · exact high_22 p
  · exact high_23 p
  · exact high_24 p
  · exact high_25 p
  · exact high_26 p
  · exact high_27 p
  · exact high_28 p
  · exact high_29 p
  · exact high_30 p
  · exact high_31 p
  · exact high_32 p
  · exact high_33 p
  · exact high_34 p
  · exact high_35 p
  · exact high_36 p
  · exact high_37 p
  · exact high_38 p
  · exact high_39 p
  · exact high_40 p
  · exact high_41 p
  · exact high_42 p
  · exact high_43 p
  · exact high_44 p
  · exact high_45 p
  · exact high_46 p
  · exact high_47 p
  · exact high_48 p
  · exact high_49 p
  · exact high_50 p
  · exact high_51 p
  · exact high_52 p
  · exact high_53 p
  · exact high_54 p
  · exact high_55 p
  · exact high_56 p
  · exact high_57 p
  · exact high_58 p
  · exact high_59 p
  · exact high_60 p
  · exact high_61 p
  · exact high_62 p
  · exact high_63 p

set_option maxRecDepth 10000 in
private theorem center_0 : ∀ p : Fin 1600, tableMap (centerData 0) p = centralPerm p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

set_option maxRecDepth 10000 in
private theorem center_1 : ∀ p : Fin 1600, tableMap (centerData 1) p = matePerm p := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

public theorem central_correct (p : Fin 1600) :
    tableMap (centerData 0) p = centralPerm p := center_0 p

public theorem mate_correct (p : Fin 1600) :
    tableMap (centerData 1) p = matePerm p := center_1 p

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.Geometry.RepresentativeMasks
