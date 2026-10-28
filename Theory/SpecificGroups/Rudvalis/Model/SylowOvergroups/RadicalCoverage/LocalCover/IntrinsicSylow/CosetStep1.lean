module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetData
import Mathlib.Tactic.FinCases

/-!
# Coset transitions for max4 generator 1

Witnesses from `source/GenerateCosets.g` and `source/GenerateCosets.py`.
The computation uses the unchanged ATLAS max4 and local words; see
`SylowOvergroups.Definitions` for attribution. GAP output is not trusted: all
permutation identities and separating points are checked by Lean.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
open Theory.GroupTheory Rudvalis.OrderCertificate
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem step1_0 :
    rep 0 * Main.gen 1 = evalWord P.L0.gen (factor 1 0) * rep (act 1 0) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_1 :
    rep 1 * Main.gen 1 = evalWord P.L0.gen (factor 1 1) * rep (act 1 1) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_2 :
    rep 2 * Main.gen 1 = evalWord P.L0.gen (factor 1 2) * rep (act 1 2) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_3 :
    rep 3 * Main.gen 1 = evalWord P.L0.gen (factor 1 3) * rep (act 1 3) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_4 :
    rep 4 * Main.gen 1 = evalWord P.L0.gen (factor 1 4) * rep (act 1 4) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_5 :
    rep 5 * Main.gen 1 = evalWord P.L0.gen (factor 1 5) * rep (act 1 5) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_6 :
    rep 6 * Main.gen 1 = evalWord P.L0.gen (factor 1 6) * rep (act 1 6) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_7 :
    rep 7 * Main.gen 1 = evalWord P.L0.gen (factor 1 7) * rep (act 1 7) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_8 :
    rep 8 * Main.gen 1 = evalWord P.L0.gen (factor 1 8) * rep (act 1 8) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_9 :
    rep 9 * Main.gen 1 = evalWord P.L0.gen (factor 1 9) * rep (act 1 9) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_10 :
    rep 10 * Main.gen 1 = evalWord P.L0.gen (factor 1 10) * rep (act 1 10) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_11 :
    rep 11 * Main.gen 1 = evalWord P.L0.gen (factor 1 11) * rep (act 1 11) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_12 :
    rep 12 * Main.gen 1 = evalWord P.L0.gen (factor 1 12) * rep (act 1 12) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_13 :
    rep 13 * Main.gen 1 = evalWord P.L0.gen (factor 1 13) * rep (act 1 13) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_14 :
    rep 14 * Main.gen 1 = evalWord P.L0.gen (factor 1 14) * rep (act 1 14) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_15 :
    rep 15 * Main.gen 1 = evalWord P.L0.gen (factor 1 15) * rep (act 1 15) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_16 :
    rep 16 * Main.gen 1 = evalWord P.L0.gen (factor 1 16) * rep (act 1 16) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_17 :
    rep 17 * Main.gen 1 = evalWord P.L0.gen (factor 1 17) * rep (act 1 17) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_18 :
    rep 18 * Main.gen 1 = evalWord P.L0.gen (factor 1 18) * rep (act 1 18) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_19 :
    rep 19 * Main.gen 1 = evalWord P.L0.gen (factor 1 19) * rep (act 1 19) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step1_20 :
    rep 20 * Main.gen 1 = evalWord P.L0.gen (factor 1 20) * rep (act 1 20) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem step1 (r : Fin 21) :
    rep r * Main.gen 1 = evalWord P.L0.gen (factor 1 r) * rep (act 1 r) := by
  fin_cases r
  · exact step1_0
  · exact step1_1
  · exact step1_2
  · exact step1_3
  · exact step1_4
  · exact step1_5
  · exact step1_6
  · exact step1_7
  · exact step1_8
  · exact step1_9
  · exact step1_10
  · exact step1_11
  · exact step1_12
  · exact step1_13
  · exact step1_14
  · exact step1_15
  · exact step1_16
  · exact step1_17
  · exact step1_18
  · exact step1_19
  · exact step1_20

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
