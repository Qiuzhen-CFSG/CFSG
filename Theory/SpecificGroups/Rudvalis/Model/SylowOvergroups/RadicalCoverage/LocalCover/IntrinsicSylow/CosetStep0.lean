module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetData
import Mathlib.Tactic.FinCases

/-!
# Coset transitions for max4 generator 0

Witnesses from `source/GenerateCosets.g` and `source/GenerateCosets.py`.
The computation uses the unchanged ATLAS max4 and local words; see
`SylowOvergroups.Definitions` for attribution. GAP output is not trusted: all
permutation identities and separating points are checked by Lean.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
open Theory.GroupTheory Rudvalis.OrderCertificate
set_option Elab.async false

set_option maxRecDepth 30000 in
private theorem step0_0 :
    rep 0 * Main.gen 0 = evalWord P.L0.gen (factor 0 0) * rep (act 0 0) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_1 :
    rep 1 * Main.gen 0 = evalWord P.L0.gen (factor 0 1) * rep (act 0 1) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_2 :
    rep 2 * Main.gen 0 = evalWord P.L0.gen (factor 0 2) * rep (act 0 2) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_3 :
    rep 3 * Main.gen 0 = evalWord P.L0.gen (factor 0 3) * rep (act 0 3) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_4 :
    rep 4 * Main.gen 0 = evalWord P.L0.gen (factor 0 4) * rep (act 0 4) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_5 :
    rep 5 * Main.gen 0 = evalWord P.L0.gen (factor 0 5) * rep (act 0 5) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_6 :
    rep 6 * Main.gen 0 = evalWord P.L0.gen (factor 0 6) * rep (act 0 6) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_7 :
    rep 7 * Main.gen 0 = evalWord P.L0.gen (factor 0 7) * rep (act 0 7) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_8 :
    rep 8 * Main.gen 0 = evalWord P.L0.gen (factor 0 8) * rep (act 0 8) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_9 :
    rep 9 * Main.gen 0 = evalWord P.L0.gen (factor 0 9) * rep (act 0 9) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_10 :
    rep 10 * Main.gen 0 = evalWord P.L0.gen (factor 0 10) * rep (act 0 10) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_11 :
    rep 11 * Main.gen 0 = evalWord P.L0.gen (factor 0 11) * rep (act 0 11) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_12 :
    rep 12 * Main.gen 0 = evalWord P.L0.gen (factor 0 12) * rep (act 0 12) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_13 :
    rep 13 * Main.gen 0 = evalWord P.L0.gen (factor 0 13) * rep (act 0 13) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_14 :
    rep 14 * Main.gen 0 = evalWord P.L0.gen (factor 0 14) * rep (act 0 14) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_15 :
    rep 15 * Main.gen 0 = evalWord P.L0.gen (factor 0 15) * rep (act 0 15) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_16 :
    rep 16 * Main.gen 0 = evalWord P.L0.gen (factor 0 16) * rep (act 0 16) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_17 :
    rep 17 * Main.gen 0 = evalWord P.L0.gen (factor 0 17) * rep (act 0 17) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_18 :
    rep 18 * Main.gen 0 = evalWord P.L0.gen (factor 0 18) * rep (act 0 18) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_19 :
    rep 19 * Main.gen 0 = evalWord P.L0.gen (factor 0 19) * rep (act 0 19) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

set_option maxRecDepth 30000 in
private theorem step0_20 :
    rep 20 * Main.gen 0 = evalWord P.L0.gen (factor 0 20) * rep (act 0 20) := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem step0 (r : Fin 21) :
    rep r * Main.gen 0 = evalWord P.L0.gen (factor 0 r) * rep (act 0 r) := by
  fin_cases r
  · exact step0_0
  · exact step0_1
  · exact step0_2
  · exact step0_3
  · exact step0_4
  · exact step0_5
  · exact step0_6
  · exact step0_7
  · exact step0_8
  · exact step0_9
  · exact step0_10
  · exact step0_11
  · exact step0_12
  · exact step0_13
  · exact step0_14
  · exact step0_15
  · exact step0_16
  · exact step0_17
  · exact step0_18
  · exact step0_19
  · exact step0_20

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
