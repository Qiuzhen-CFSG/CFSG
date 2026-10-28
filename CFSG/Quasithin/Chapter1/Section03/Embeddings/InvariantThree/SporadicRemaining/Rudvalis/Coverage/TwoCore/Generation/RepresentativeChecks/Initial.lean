module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.RepresentativeChecks.Base

/-!
# Initial Rudvalis recovery certificates

For representatives 6 through 61, the displayed words recover the standard
generator a on the certified five-point base. Base.recovery_of_a supplies a
word for b, giving the exact two-word alternative. GAP only discovered the
words retained in source/recovery-*.json; every equality below is checked
by Lean's kernel using the original point-action convention.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. See Base and Representatives for ATLAS attribution.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
open Representatives

@[expose] public def recoveryWord6 : List (Fin 30) :=
  [29]

set_option maxRecDepth 8192 in
public theorem recovers_a_6 : extensionWord (representative 6) recoveryWord6 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord7 : List (Fin 30) :=
  [15, 21, 16, 22, 17, 15, 14, 26, 17, 15, 17, 28, 29, 18, 16, 19, 16, 19, 17, 20, 14, 26, 17, 15, 17, 28, 29, 18, 16, 19, 22, 14, 19, 15, 23, 19, 29, 24, 15, 14, 26, 17, 15, 17, 28, 29, 18, 17, 20, 15, 16, 18, 21, 29, 24, 19, 15, 18]

set_option maxRecDepth 8192 in
public theorem recovers_a_7 : extensionWord (representative 7) recoveryWord7 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord8 : List (Fin 30) :=
  [23, 15, 21, 3, 4, 10, 7, 15, 16, 19, 29, 16, 29, 19, 25, 29, 28, 29, 29, 16, 29, 19, 25, 29, 28, 29, 1, 29, 25, 14, 20, 29, 16, 29, 19, 3, 4, 10, 7, 15, 16, 19, 29, 16, 29, 19, 25, 29, 28, 29, 29, 16, 29, 19, 25, 29, 28, 29, 1, 29, 25, 14, 20, 29, 16, 29, 19, 23, 3, 4, 10, 7, 15, 16, 19, 29, 16, 29, 19, 25, 29, 28, 29, 29, 16, 29, 19, 25, 29, 28, 29, 1, 29, 25, 14, 20, 29, 16, 29, 19, 17, 17, 15, 21, 1, 17, 9, 19, 18, 29, 16, 29, 19, 25, 29, 28, 29, 16, 19, 15, 29, 23, 7]

set_option maxRecDepth 8192 in
public theorem recovers_a_8 : extensionWord (representative 8) recoveryWord8 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord9 : List (Fin 30) :=
  [21, 2, 9, 3, 29, 26, 16, 20, 29, 25, 29, 26, 16, 20, 29, 25, 16, 19, 16, 19, 29, 26, 20, 27, 29, 17, 19, 29, 26, 16, 20, 29, 25, 16, 18, 29, 26, 16, 20, 29, 25, 16, 18, 21, 29, 16, 9]

set_option maxRecDepth 8192 in
public theorem recovers_a_9 : extensionWord (representative 9) recoveryWord9 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord10 : List (Fin 30) :=
  [23, 15, 21, 19, 18, 20, 15, 29, 6, 29, 16, 19, 17, 20, 22, 25, 1, 29, 25, 2, 20, 28, 29, 21, 24, 1, 29, 6, 29, 16, 18, 16, 19, 16, 19, 1, 29, 13, 21, 28, 29, 1, 29, 13, 21, 28, 29, 2, 29, 3, 6, 28]

set_option maxRecDepth 8192 in
public theorem recovers_a_10 : extensionWord (representative 10) recoveryWord10 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord11 : List (Fin 30) :=
  [28, 19, 18, 17, 20, 7, 14, 13, 19, 27, 29, 16, 20, 16, 19, 7, 14, 13, 19, 27, 29, 16, 20, 23, 7, 14, 13, 19, 27, 29, 16, 20, 22, 14, 28, 17, 17, 19, 27, 29, 16, 20, 25, 20, 19, 7, 14, 13, 19, 27, 29, 16, 20, 7, 14, 13, 19, 27, 29, 16, 20, 16, 18, 16, 18, 1, 14, 6, 7]

set_option maxRecDepth 8192 in
public theorem recovers_a_11 : extensionWord (representative 11) recoveryWord11 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord12 : List (Fin 30) :=
  [23, 15, 21, 2, 4, 5, 11, 16, 29, 17, 16, 26, 27, 15, 29, 29, 17, 29, 26, 15, 17, 25, 29, 18, 23, 16, 16, 15, 2, 4, 5, 11, 16, 29, 17, 16, 26, 27, 15, 29, 29, 17, 29, 26, 15, 17, 25, 29, 18, 2, 4, 5, 11, 16, 29, 17, 16, 26, 27, 15, 29, 29, 17, 29, 26, 15, 17, 25, 29, 18, 25, 18, 17, 15, 29, 17, 16, 26, 27, 15, 29, 16, 19, 1, 14, 2, 4]

set_option maxRecDepth 8192 in
public theorem recovers_a_12 : extensionWord (representative 12) recoveryWord12 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord13 : List (Fin 30) :=
  [23, 15, 20, 9, 22, 17, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 21, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 15, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 23, 17, 29, 16, 15, 17, 29, 18, 16, 15, 29, 19, 17, 20, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 17, 20, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 16, 18, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 22, 25, 7, 29, 12, 29, 19, 23, 26, 29, 29, 24, 3, 4, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 21, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 15, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 23, 17, 29, 16, 15, 17, 29, 18, 16, 15, 29, 19, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 21, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 15, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 23, 17, 29, 16, 15, 17, 29, 18, 16, 15, 29, 19, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 15, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 17, 20, 1, 29, 3, 8, 29, 22, 26, 29, 29, 24, 16, 18, 29, 22, 29, 25]

set_option maxRecDepth 8192 in
public theorem recovers_a_13 : extensionWord (representative 13) recoveryWord13 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord14 : List (Fin 30) :=
  [15, 1, 3, 25, 14, 17, 18, 29, 16, 17, 15, 16, 19, 22, 14, 17, 18, 29, 16, 17, 23, 22, 25, 29, 22, 17, 26, 20, 26, 25, 15, 24, 29, 1, 2, 4, 5, 22, 25, 22, 14, 17, 18, 29, 16, 17, 22, 14, 17, 18, 29, 16, 17, 15, 22, 14, 17, 18, 29, 16, 17, 16, 18, 22, 29, 22, 19, 18, 28, 25, 29, 25, 26, 22, 14, 17, 18, 29, 16, 17, 22, 25, 22, 14, 17, 18, 29, 16, 17, 21, 22, 25, 22, 14, 17, 18, 29, 16, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_14 : extensionWord (representative 14) recoveryWord14 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord15 : List (Fin 30) :=
  [15, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 21, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 28, 28, 15, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 23, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 28, 28, 15, 3, 4, 22, 25, 15, 1, 14, 25, 7, 21, 25, 16, 27, 29, 16, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 21, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 28, 28, 15, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 16, 17, 10, 15, 14, 18, 19, 16, 17, 21, 25, 16, 27, 29, 16, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 28, 28, 15, 21, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 2, 3, 7, 29, 16, 19, 15, 28, 29, 26, 25, 25, 7, 15, 14, 23, 29, 16, 25, 16, 27, 29, 16, 14, 24, 16, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_15 : extensionWord (representative 15) recoveryWord15 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord16 : List (Fin 30) :=
  [15, 21, 26, 20, 17, 15, 17, 20, 14, 17, 21, 29, 16, 19, 17, 20, 16, 18, 16, 18, 1, 29, 22, 2, 23, 29, 15, 21, 17, 21, 29, 15, 14, 17, 21, 29, 21, 16, 19, 22, 25, 14, 22, 20, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_16 : extensionWord (representative 16) recoveryWord16 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord17 : List (Fin 30) :=
  [20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 21, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 28, 28, 15, 3, 4, 13, 7, 14, 25, 25, 28, 19, 29, 16, 23, 20, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 21, 28, 28, 15, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 23, 28, 28, 15, 27, 26, 14, 16, 20, 17, 25, 29, 16, 20, 17, 25, 29, 29, 29, 29, 24, 17, 28, 19, 20, 29, 21, 28, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 21, 20, 17, 14, 16, 20, 17, 25, 29, 29, 16, 18, 14, 16, 20, 17, 25, 29, 29, 22, 29, 23, 17, 28, 17, 25, 29, 29, 1, 2, 25, 14, 16, 20, 17, 25, 29, 27, 24, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_17 : extensionWord (representative 17) recoveryWord17 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord18 : List (Fin 30) :=
  [2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 21, 2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 28, 28, 15, 21, 2, 1, 9, 14, 22, 23, 24, 16, 29, 22, 15, 14, 22, 25, 15, 21, 26, 15, 24, 16, 29, 22, 2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 2, 3, 5, 11, 16, 14, 22, 23, 24, 16, 29, 22, 14, 15, 22, 15, 24, 16, 29, 22, 4, 5, 9, 14, 22, 23, 24, 16, 29, 22, 15, 1, 14, 2, 4]

set_option maxRecDepth 8192 in
public theorem recovers_a_18 : extensionWord (representative 18) recoveryWord18 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord19 : List (Fin 30) :=
  [15, 21, 4, 2, 10, 14, 21, 9, 27, 24, 29, 1, 29, 22, 24, 29, 27, 24, 29, 21, 21, 15, 21, 4, 2, 10, 14, 21, 9, 27, 24, 29, 1, 29, 22, 24, 29, 27, 24, 29, 21, 15, 21, 21, 4, 2, 10, 14, 21, 9, 27, 24, 29, 1, 29, 22, 24, 29, 27, 24, 29, 23, 3, 5, 24, 14, 26, 21, 16, 21, 23, 16, 29, 15, 15, 4, 2, 10, 14, 21, 9, 27, 24, 29, 1, 29, 22, 24, 29, 27, 24, 29, 23, 4, 2, 10, 14, 21, 9, 27, 24, 29, 1, 29, 22, 24, 29, 27, 24, 29, 21, 4, 2, 10, 14, 21, 9, 27, 24, 29, 1, 29, 22, 24, 29, 27, 24, 29, 21, 4, 2, 25, 14, 21, 9, 27, 24, 29, 16, 18, 1, 14, 22, 10]

set_option maxRecDepth 8192 in
public theorem recovers_a_19 : extensionWord (representative 19) recoveryWord19 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord20 : List (Fin 30) :=
  [23, 15, 21, 1, 0, 2, 4, 3, 14, 15, 18, 20, 18, 15, 29, 15, 16, 19, 17, 20, 14, 15, 18, 20, 18, 15, 29, 17, 20, 29, 25, 21, 29, 25]

set_option maxRecDepth 8192 in
public theorem recovers_a_20 : extensionWord (representative 20) recoveryWord20 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord21 : List (Fin 30) :=
  [15, 1, 17, 9, 19, 18, 29, 18, 17, 24, 29, 29, 15, 2, 14, 6, 26, 29, 16, 24, 16, 16, 15, 1, 17, 9, 19, 18, 29, 18, 17, 24, 29, 29, 15, 2, 14, 6, 26, 29, 16, 24, 10, 24, 29, 18, 17, 24, 29, 29, 15, 14, 10, 15, 16, 25, 24, 29, 29, 1, 17, 9, 19, 18, 29, 18, 17, 24, 29, 29, 15, 2, 14, 6, 26, 29, 16, 24, 21, 1, 17, 9, 19, 18, 29, 18, 17, 24, 29, 29, 15, 2, 14, 6, 26, 29, 16, 24, 16, 16, 15, 1, 17, 9, 19, 18, 29, 18, 17, 24, 29, 29, 15, 2, 14, 6, 26, 29, 16, 24, 21, 16, 22, 17, 15, 29, 18, 17, 24, 29, 29, 29, 24, 21, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_21 : extensionWord (representative 21) recoveryWord21 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord22 : List (Fin 30) :=
  [2, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 17, 21, 19, 16, 16, 19, 15, 2, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 17, 21, 23, 2, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 17, 23, 1, 26, 18, 20, 17, 14, 23, 22, 16, 22, 18, 23, 22, 16, 22, 18, 29, 22, 29, 22, 22, 27, 29, 20, 25, 21, 16, 22, 2, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 17, 19, 16, 16, 19, 15, 2, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 17, 23, 2, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 10, 4, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 25, 21, 15, 17, 24, 24, 16, 29, 17, 21, 28, 26, 14, 23, 22, 16, 22, 18, 29, 16, 18, 14, 14, 25]

set_option maxRecDepth 8192 in
public theorem recovers_a_22 : extensionWord (representative 22) recoveryWord22 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord23 : List (Fin 30) :=
  [18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 21, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 21, 23, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 27, 27, 15, 25, 7, 15, 29, 7, 17, 23, 29, 25, 29, 7, 17, 23, 29, 25, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 21, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 21, 23, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 27, 27, 15, 25, 7, 15, 29, 7, 17, 23, 29, 25, 29, 7, 17, 23, 29, 25, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 21, 23, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 18, 23, 19, 15, 29, 7, 17, 23, 29, 25, 14, 23, 17, 26, 29, 21, 26, 19, 18, 15, 1, 14, 1, 8]

set_option maxRecDepth 8192 in
public theorem recovers_a_23 : extensionWord (representative 23) recoveryWord23 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord24 : List (Fin 30) :=
  [1, 4, 6, 14, 17, 29, 23, 16, 18, 14, 26, 21, 27, 17, 29, 20, 17, 6, 14, 17, 29, 23, 16, 18, 14, 26, 21, 27, 17, 29, 16, 19, 14, 17, 29, 22, 25, 14, 17, 29, 17, 20, 14, 24, 14, 17]

set_option maxRecDepth 8192 in
public theorem recovers_a_24 : extensionWord (representative 24) recoveryWord24 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord25 : List (Fin 30) :=
  [22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 17, 17, 15, 22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 23, 17, 17, 15, 22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 23, 22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 24, 16, 17, 15, 29, 23, 24, 16, 29, 29, 24, 29, 21, 22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 22, 18, 20, 14, 18, 16, 29, 24, 29, 15, 14, 9, 29, 16, 17, 19, 29, 17, 17, 17, 15, 21, 3, 4, 8, 14, 18, 16, 29, 24, 29, 15, 16, 29, 26, 15, 23]

set_option maxRecDepth 8192 in
public theorem recovers_a_25 : extensionWord (representative 25) recoveryWord25 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord26 : List (Fin 30) :=
  [23, 15, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 7, 9, 22, 24, 15, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 23, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 21, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 23, 18, 17, 16, 17, 16, 29, 19, 15, 23, 28, 29, 26, 29, 21, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 23, 7, 9, 22, 24, 15, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 21, 9, 16, 17, 15, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 24, 20, 16, 17, 14, 20, 15, 21, 20, 29, 20, 16, 18, 1, 29, 22, 10]

set_option maxRecDepth 8192 in
public theorem recovers_a_26 : extensionWord (representative 26) recoveryWord26 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord27 : List (Fin 30) :=
  [23, 15, 21, 2, 5, 7, 24, 14, 15, 18, 20, 28, 29, 17, 20, 16, 19, 21, 22, 29, 21, 25, 26]

set_option maxRecDepth 8192 in
public theorem recovers_a_27 : extensionWord (representative 27) recoveryWord27 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord28 : List (Fin 30) :=
  [15, 21, 1, 2, 6, 24, 29, 18, 22, 28, 25, 28, 29, 22, 17, 20, 29, 18, 22, 28, 25, 28, 29, 22, 29, 18, 22, 28, 25, 28, 29, 22, 17, 20, 16, 19, 1, 29, 11, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_28 : extensionWord (representative 28) recoveryWord28 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord29 : List (Fin 30) :=
  [23, 22, 19, 17, 14, 14, 28, 16, 21, 26, 25, 29, 16, 18, 29, 26, 16, 29, 17, 21, 26, 25, 29, 23, 22, 19, 17, 14, 14, 28, 16, 21, 26, 25, 29, 16, 18, 29, 26, 16, 29, 17, 21, 26, 25, 29, 21, 22, 19, 17, 14, 14, 28, 16, 21, 26, 25, 29, 16, 18, 29, 26, 16, 29, 17, 21, 26, 25, 29, 1, 0, 3, 4, 5, 14, 14, 28, 16, 21, 26, 25, 20, 19, 16, 28, 26, 20, 19, 29, 16, 18, 26, 23, 22, 19, 17, 14, 14, 28, 16, 21, 26, 25, 29, 16, 18, 29, 26, 16, 29, 17, 21, 26, 25, 29, 21, 23, 22, 19, 17, 14, 14, 28, 16, 21, 26, 25, 29, 16, 18, 29, 26, 16, 29, 17, 21, 26, 25, 29, 17, 17, 15, 9, 19, 17, 14, 14, 28, 16, 21, 26, 25, 29, 15, 14, 14, 28, 16, 21, 26, 25, 29, 1, 29, 1, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_29 : extensionWord (representative 29) recoveryWord29 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord30 : List (Fin 30) :=
  [15, 21, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 21, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 15, 19, 18, 23, 15, 22, 29, 17, 15, 17, 28, 27, 29, 29, 29, 21, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 21, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 15, 19, 18, 23, 15, 22, 29, 17, 15, 17, 28, 27, 29, 29, 29, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 15, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 23, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 15, 21, 1, 22, 2, 27, 20, 17, 29, 21, 16, 25, 27, 29, 23, 21, 1, 29, 11, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_30 : extensionWord (representative 30) recoveryWord30 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord31 : List (Fin 30) :=
  [2, 24, 3, 22, 14, 17, 15, 18, 16, 29, 16, 19, 23, 22, 14, 17, 15, 18, 16, 29, 1, 29, 2, 3, 22, 25, 28, 17, 29, 19, 16, 10, 16, 17, 15, 22, 14, 17, 15, 18, 16, 29, 16, 18, 16, 19, 23, 16, 18, 16, 14, 15, 25, 25, 29, 23, 18, 17, 25, 19, 22, 14, 17, 15, 18, 16, 29, 17, 25, 19, 15, 17, 25, 19, 16, 19, 29, 16, 17, 16, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_31 : extensionWord (representative 31) recoveryWord31 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord32 : List (Fin 30) :=
  [23, 15, 1, 2, 6, 9, 14, 19, 24, 29, 26, 29, 16, 18, 16, 18, 14, 19, 24, 29, 26, 29, 15, 1, 29, 12, 29, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_32 : extensionWord (representative 32) recoveryWord32 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord33 : List (Fin 30) :=
  [23, 15, 21, 2, 1, 7, 29, 16, 17, 24, 26, 23, 29, 15, 29, 16, 17, 24, 26, 23, 29, 16, 18, 15, 29, 27, 19, 17]

set_option maxRecDepth 8192 in
public theorem recovers_a_33 : extensionWord (representative 33) recoveryWord33 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord34 : List (Fin 30) :=
  [23, 21, 28, 22, 19, 17, 29, 28, 19, 27, 20, 27, 29, 23, 17, 20, 16, 19, 14, 10, 22, 27, 20, 27, 29, 2, 4, 5, 13, 16, 28, 22, 19, 17, 29, 28, 19, 27, 20, 27, 29, 23, 17, 20, 16, 19, 14, 10, 22, 27, 20, 27, 29, 29, 28, 19, 27, 20, 27, 29, 16, 18, 17, 20, 23, 29, 28, 19, 27, 20, 27, 29, 1, 29, 13, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_34 : extensionWord (representative 34) recoveryWord34 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord35 : List (Fin 30) :=
  [23, 1, 19, 7, 18, 17, 16, 18, 14, 23, 24, 27, 24, 29, 15, 16, 19, 14, 23, 24, 27, 24, 29, 16, 19, 14, 23, 24, 27, 24, 29, 16, 18, 22, 25, 1, 14, 4, 23, 20, 29, 16, 14, 23, 24, 27, 24, 29, 16, 18, 14, 23, 24, 27, 24, 29, 17, 20, 16, 18, 14, 23, 24, 27, 24, 29, 16, 18, 14, 23, 24, 27, 24, 29, 16, 18, 14, 23, 24, 27, 29, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_35 : extensionWord (representative 35) recoveryWord35 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord36 : List (Fin 30) :=
  [23, 15, 21, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 21, 23, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 21, 1, 9, 18, 17, 16, 14, 25, 17, 23, 22, 27, 28, 21, 15, 24, 19, 22, 15, 29, 15, 21, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 23, 18, 17, 24, 15, 29, 16, 18, 22, 29, 16, 20, 29, 22, 23, 22, 27, 29, 21, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 1, 9, 18, 17, 16, 14, 25, 17, 23, 22, 27, 28, 21, 15, 24, 19, 22, 15, 29, 15, 21, 1, 9, 18, 17, 16, 14, 25, 17, 23, 22, 27, 28, 21, 15, 24, 19, 22, 15, 29, 15, 21, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 25, 22, 19, 18, 1, 14, 9, 14, 15, 25, 29, 29, 22, 22, 24, 21, 2, 3, 7, 2, 29, 0, 22, 17, 28]

set_option maxRecDepth 8192 in
public theorem recovers_a_36 : extensionWord (representative 36) recoveryWord36 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord37 : List (Fin 30) :=
  [23, 21, 1, 0, 25, 3, 14, 24, 22, 16, 23, 19, 18, 29, 15, 21, 16, 19, 15, 14, 24, 22, 16, 23, 19, 18, 29, 29, 15, 29, 23, 29, 19, 27, 29, 15, 25, 16, 18, 14, 24, 22, 16, 23, 19, 18, 29, 15, 22, 25, 16, 18, 14, 24, 22, 16, 23, 19, 18, 29, 17, 20, 2, 14, 1, 9, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_37 : extensionWord (representative 37) recoveryWord37 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord38 : List (Fin 30) :=
  [15, 2, 5, 1, 3, 14, 23, 17, 18, 28, 29, 15, 17, 20, 23, 15, 16, 18, 2, 14, 5, 13, 18, 28, 15, 29, 22, 19, 27, 22, 17, 16, 14, 23, 17, 18, 28, 29, 16, 18, 23, 17, 20, 16, 18, 2, 14, 1, 5, 22, 17, 29, 19, 16, 17, 14, 23, 17, 18, 28, 29, 16, 18, 16, 18, 22, 25, 29, 18, 19, 17, 29]

set_option maxRecDepth 8192 in
public theorem recovers_a_38 : extensionWord (representative 38) recoveryWord38 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord39 : List (Fin 30) :=
  [23, 1, 4, 8, 7, 29, 11, 16, 22, 29, 22, 16, 18, 16, 19, 7, 29, 11, 16, 22, 29, 22, 15, 2, 29, 24, 29, 20, 25, 15, 21, 20, 29, 16, 3, 4, 13, 17, 20, 7, 29, 11, 16, 22, 29, 22, 17, 20, 7, 29, 11, 16, 22, 29, 22, 16, 19, 22, 25, 17, 20, 1, 29, 13, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_39 : extensionWord (representative 39) recoveryWord39 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord40 : List (Fin 30) :=
  [15, 21, 20, 24, 18, 14, 26, 17, 27, 29, 16, 19, 16, 18, 14, 26, 17, 27, 29, 16, 18, 22, 25, 29, 27, 17, 16, 22]

set_option maxRecDepth 8192 in
public theorem recovers_a_40 : extensionWord (representative 40) recoveryWord40 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord41 : List (Fin 30) :=
  [23, 15, 21, 25, 7, 19, 18, 14, 15, 29, 15, 16, 18, 15, 14, 15, 29, 23, 29, 15, 18, 23, 24]

set_option maxRecDepth 8192 in
public theorem recovers_a_41 : extensionWord (representative 41) recoveryWord41 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord42 : List (Fin 30) :=
  [23, 15, 2, 3, 4, 9, 16, 14, 15, 21, 27, 22, 29, 21, 16, 18, 23, 14, 15, 21, 27, 22, 29, 15, 14, 7, 15, 28, 24, 29, 15, 16, 18, 14, 15, 21, 27, 22, 29, 21, 16, 18, 23, 14, 15, 21, 27, 22, 29, 15, 14, 28, 20, 15, 22, 19, 27, 22, 29, 2, 5, 22, 24, 15, 14, 15, 21, 27, 22, 29, 15, 14, 15, 21, 27, 22, 29, 15, 16, 18, 29, 22, 17, 26]

set_option maxRecDepth 8192 in
public theorem recovers_a_42 : extensionWord (representative 42) recoveryWord42 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord43 : List (Fin 30) :=
  [15, 21, 1, 24, 8, 2, 29, 27, 19, 15, 26, 20, 26, 15, 29, 16, 18, 15, 22, 25, 16, 19, 16, 18, 29, 16, 21, 28, 26, 22, 29, 23, 21, 29, 27, 19, 15, 26, 20, 26, 15, 29, 15, 22, 25, 22, 25, 29, 27, 19, 15, 26, 20, 26, 15, 29, 23, 29, 18, 25, 28, 29]

set_option maxRecDepth 8192 in
public theorem recovers_a_43 : extensionWord (representative 43) recoveryWord43 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord44 : List (Fin 30) :=
  [23, 15, 26, 20, 17, 15, 17, 20, 22, 25, 29, 26, 17, 15, 24, 20, 18, 29, 16, 18, 17, 20, 16, 18, 29, 26, 17, 15, 24, 20, 18, 29, 17, 29, 23, 16, 20]

set_option maxRecDepth 8192 in
public theorem recovers_a_44 : extensionWord (representative 44) recoveryWord44 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord45 : List (Fin 30) :=
  [23, 21, 28, 20, 17, 15, 1, 29, 8, 29, 19, 17, 16, 29, 21, 21, 15, 1, 29, 8, 29, 19, 17, 16, 29, 21, 16, 18, 16, 19, 14, 18, 16, 25, 22, 29, 29, 18, 18, 1, 29, 8, 29, 19, 17, 16, 29, 21, 21, 15, 1, 29, 8, 29, 19, 17, 16, 29, 21, 16, 18, 16, 19, 14, 18, 16, 25, 22, 29, 29, 18, 18, 1, 29, 8, 29, 19, 17, 16, 29, 21, 21, 1, 29, 8, 29, 19, 17, 16, 29, 21, 23, 15, 16, 18, 1, 29, 11, 14]

set_option maxRecDepth 8192 in
public theorem recovers_a_45 : extensionWord (representative 45) recoveryWord45 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord46 : List (Fin 30) :=
  [15, 3, 4, 25, 7, 15, 29, 20, 18, 23, 21, 26, 29, 25, 29, 20, 18, 23, 21, 26, 29, 25, 29, 9, 19, 25, 28, 29, 27, 23, 3, 4, 25, 7, 15, 29, 20, 18, 23, 21, 26, 29, 25, 29, 20, 18, 23, 21, 26, 29, 25, 29, 9, 19, 25, 28, 29, 27, 20, 17, 17, 20, 15, 21, 25, 24, 20, 17, 29, 9, 19, 15, 24, 28, 15, 29, 23, 21, 3, 4, 25, 7, 15, 29, 20, 18, 23, 21, 26, 29, 25, 29, 20, 18, 23, 21, 26, 29, 25, 29, 9, 19, 25, 28, 29, 27, 3, 4, 25, 7, 15, 29, 20, 18, 23, 21, 26, 29, 25, 29, 20, 18, 23, 21, 26, 29, 25, 29, 9, 19, 25, 28, 29, 27, 20, 17, 17, 20, 15, 10, 16, 17, 15, 29, 20, 18, 23, 21, 26, 29, 25, 15, 29, 20, 18, 23, 21, 26, 29, 25, 14, 26, 18]

set_option maxRecDepth 8192 in
public theorem recovers_a_46 : extensionWord (representative 46) recoveryWord46 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord47 : List (Fin 30) :=
  [15, 21, 18, 16, 15, 1, 29, 8, 17, 29, 29, 20, 15, 16, 19, 1, 29, 8, 17, 29, 29, 20, 15, 14, 25, 22]

set_option maxRecDepth 8192 in
public theorem recovers_a_47 : extensionWord (representative 47) recoveryWord47 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord48 : List (Fin 30) :=
  [15, 26, 20, 17, 15, 17, 20, 14, 14, 22, 20, 19, 15, 29, 21, 16, 19, 15, 14, 14, 22, 20, 19, 15, 9, 7, 15, 17, 27, 29, 23, 15, 25, 25, 22, 14, 14, 22, 20, 19, 15, 29, 16, 19, 23, 16, 19, 29, 17, 9, 27, 26, 15, 29, 26, 16, 18, 14, 14, 22, 20, 19, 15, 29, 15, 16, 18, 15, 14, 14, 22, 20, 19, 15, 14, 22, 20, 19, 15, 29, 22, 29, 19, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_48 : extensionWord (representative 48) recoveryWord48 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord49 : List (Fin 30) :=
  [21, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 26, 26, 15, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 21, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 21, 2, 4, 9, 14, 21, 20, 22, 20, 29, 16, 19, 14, 26, 19, 27, 22, 20, 29, 23, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 21, 1, 9, 18, 17, 16, 14, 21, 20, 22, 20, 29, 1, 14, 22, 23, 22, 29, 18, 26, 26, 15, 1, 21, 20, 19, 17, 14, 21, 20, 22, 20, 29, 23, 29, 22, 10, 17]

set_option maxRecDepth 8192 in
public theorem recovers_a_49 : extensionWord (representative 49) recoveryWord49 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord50 : List (Fin 30) :=
  [23, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 23, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 21, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 4, 2, 9, 29, 16, 19, 26, 29, 21, 21, 26, 25, 21, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 21, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 20, 17, 15, 14, 24, 16, 24, 26, 29, 15, 23, 1, 14, 20, 19, 29, 16, 21, 23, 26, 10, 24, 14, 24, 16, 24, 26, 29, 15, 14, 25, 23]

set_option maxRecDepth 8192 in
public theorem recovers_a_50 : extensionWord (representative 50) recoveryWord50 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord51 : List (Fin 30) :=
  [23, 15, 22, 17, 19, 29, 17, 24, 25, 20, 16, 29, 15, 16, 18, 16, 18, 16, 18, 16, 29, 25, 16, 29, 23, 25, 20, 16, 29, 2, 5, 3, 4, 15, 29, 17, 24, 25, 20, 16, 29, 16, 19, 22, 25, 16, 18, 14, 10, 23, 17, 23, 25, 20, 16, 29, 29, 17, 24, 25, 20, 16, 29, 17, 20, 15, 23, 29, 17, 24, 25, 20, 16, 29, 29, 18, 24, 17]

set_option maxRecDepth 8192 in
public theorem recovers_a_51 : extensionWord (representative 51) recoveryWord51 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord52 : List (Fin 30) :=
  [15, 9, 17, 29, 4, 13, 29, 29, 22, 29, 22, 1, 29, 4, 13, 29, 29, 22, 29, 22, 16, 18, 1, 29, 12, 29, 24, 23, 25, 19, 29, 1, 29, 4, 13, 29, 29, 22, 29, 22, 23, 1, 29, 4, 13, 29, 29, 22, 29, 22, 1, 29, 3, 5, 22]

set_option maxRecDepth 8192 in
public theorem recovers_a_52 : extensionWord (representative 52) recoveryWord52 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord53 : List (Fin 30) :=
  [18, 20, 19, 15, 16, 29, 21, 17, 15, 25, 29, 24, 20, 29, 16, 18, 17, 20, 29, 21, 17, 15, 25, 29, 24, 20, 29, 17, 20, 2, 29, 29, 25, 23, 29, 24, 20, 29, 29, 21, 17, 15, 25, 29, 24, 20, 29, 29, 21, 17, 15, 25, 29, 24, 20, 29, 15, 29, 21, 17, 15, 25, 29, 24, 20, 10, 14, 15]

set_option maxRecDepth 8192 in
public theorem recovers_a_53 : extensionWord (representative 53) recoveryWord53 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord54 : List (Fin 30) :=
  [23, 15, 1, 10, 18, 19, 17, 29, 16, 20, 15, 24, 19, 29, 23, 20, 16, 19, 16, 18, 23, 15, 16, 18, 29, 9, 15, 17, 27]

set_option maxRecDepth 8192 in
public theorem recovers_a_54 : extensionWord (representative 54) recoveryWord54 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord55 : List (Fin 30) :=
  [19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 15, 19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 15, 19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 23, 19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 7, 25, 18, 16, 14, 25, 23, 16, 26, 16, 24, 29, 27, 23, 21, 19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 15, 21, 19, 27, 16, 17, 14, 14, 15, 18, 29, 21, 29, 15, 16, 18, 14, 7, 17, 24, 18, 29, 27, 26, 21, 23, 2, 3, 11, 5, 16, 15, 17, 14, 14, 15, 18, 29, 21, 29, 15, 23, 16, 18, 2, 14, 25, 22]

set_option maxRecDepth 8192 in
public theorem recovers_a_55 : extensionWord (representative 55) recoveryWord55 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord56 : List (Fin 30) :=
  [23, 15, 7, 20, 16, 15, 2, 14, 2, 18, 29, 17, 15, 16, 18, 2, 14, 2, 18, 29, 17, 16, 18, 2, 14, 2, 18, 29, 17, 29, 18, 23, 15, 20, 18, 29, 19, 17, 20, 2, 14, 2, 18, 29, 17, 15, 2, 14, 2, 18, 29, 17, 15, 2, 14, 2, 18, 29, 17, 15, 23, 2, 14, 0, 7, 20]

set_option maxRecDepth 8192 in
public theorem recovers_a_56 : extensionWord (representative 56) recoveryWord56 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord57 : List (Fin 30) :=
  [21, 28, 18, 16, 15, 14, 20, 29, 15, 17, 20, 14, 17, 20, 17, 29, 17, 20, 1, 29, 7, 29, 29, 17, 19, 29, 15, 14, 20, 29, 16, 19, 14, 17, 20, 17, 29, 16, 19, 14, 17, 20, 17, 29, 16, 18, 22, 29, 22, 29]

set_option maxRecDepth 8192 in
public theorem recovers_a_57 : extensionWord (representative 57) recoveryWord57 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord58 : List (Fin 30) :=
  [21, 1, 3, 6, 14, 17, 18, 29, 28, 15, 14, 17, 18, 29, 28, 15, 14, 17, 18, 29, 28, 16, 19, 15, 16, 19, 15, 1, 14, 10, 22, 28, 18, 29, 26, 16, 2, 3, 24, 14, 17, 18, 29, 28, 15, 16, 19, 14, 17, 18, 29, 28, 15, 14, 17, 18, 29, 28, 15, 16, 19, 14, 26, 27, 18, 29, 28, 14, 17, 18, 29, 28, 15, 14, 17, 18, 29, 28, 15, 14, 17, 18, 29, 28, 23, 17, 20, 15, 29, 15, 29, 22, 27]

set_option maxRecDepth 8192 in
public theorem recovers_a_58 : extensionWord (representative 58) recoveryWord58 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord59 : List (Fin 30) :=
  [22, 19, 17, 14, 10, 18, 21, 25, 29, 17, 20, 21, 15, 22, 25, 17, 29, 10, 17, 23, 21, 18, 21, 25, 29, 15, 17, 20, 14, 10, 18, 21, 25, 29, 16, 18, 22, 25, 29, 18, 24, 17]

set_option maxRecDepth 8192 in
public theorem recovers_a_59 : extensionWord (representative 59) recoveryWord59 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord60 : List (Fin 30) :=
  [21, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 21, 23, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 21, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 23, 28, 28, 15, 3, 4, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 29, 24, 16, 23, 21, 22, 26, 29, 18, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 23, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 23, 1, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 23, 7, 25, 18, 25, 19, 18, 17, 14, 14, 22, 21, 22, 26, 29, 18, 21, 29, 27, 18, 17]

set_option maxRecDepth 8192 in
public theorem recovers_a_60 : extensionWord (representative 60) recoveryWord60 = a := by
  apply recovers_a_of_five
  decide +kernel

@[expose] public def recoveryWord61 : List (Fin 30) :=
  [19, 27, 16, 17, 20, 1, 29, 25, 3, 15, 18, 22, 25, 29, 15, 1, 29, 25, 3, 15, 18, 22, 25, 29, 17, 20, 16, 19, 1, 29, 25, 3, 15, 18, 22, 25, 29, 29, 25, 7, 15, 20, 18, 29, 19, 27, 15, 18, 16, 18, 1, 29, 25, 3, 15, 18, 22, 25, 29, 15, 1, 29, 25, 3, 15, 18, 22, 25, 29, 17, 20, 16, 19, 1, 29, 25, 3, 15, 18, 22, 25, 29, 29, 25, 22, 15, 27, 20, 18, 29, 19, 27, 15, 18, 1, 0, 3, 10, 1, 29, 25, 3, 15, 18, 22, 25, 29, 15, 1, 29, 25, 3, 15, 18, 22, 25, 29, 17, 20, 16, 19, 1, 29, 25, 3, 15, 18, 22, 25, 29, 29, 25, 7, 15, 20, 18, 29, 19, 27, 15, 18, 1, 29, 25, 3, 15, 18, 22, 25, 29, 15, 1, 29, 25, 3, 15, 18, 22, 25, 29, 17, 20, 16, 19, 1, 29, 25, 3, 15, 18, 22, 25, 29, 29, 25, 7, 15, 20, 18, 29, 19, 27, 15, 18, 1, 29, 25, 3, 15, 18, 22, 25, 29, 16, 18, 15, 17, 20, 1, 29, 25, 3, 15, 18, 22, 25, 29, 1, 14, 11]

set_option maxRecDepth 8192 in
public theorem recovers_a_61 : extensionWord (representative 61) recoveryWord61 = a := by
  apply recovers_a_of_five
  decide +kernel

public theorem initial_recovery (i : Index) (hlo : 6 ≤ i.val) (hhi : i.val < 62) :
    Alternative i := by
  have hall : ∀ j : Fin 56, Alternative ⟨j.val + 6, by omega⟩ := by
    intro j
    fin_cases j
    · exact alternative_of_recovers_a 6 recoveryWord6 recovers_a_6
    · exact alternative_of_recovers_a 7 recoveryWord7 recovers_a_7
    · exact alternative_of_recovers_a 8 recoveryWord8 recovers_a_8
    · exact alternative_of_recovers_a 9 recoveryWord9 recovers_a_9
    · exact alternative_of_recovers_a 10 recoveryWord10 recovers_a_10
    · exact alternative_of_recovers_a 11 recoveryWord11 recovers_a_11
    · exact alternative_of_recovers_a 12 recoveryWord12 recovers_a_12
    · exact alternative_of_recovers_a 13 recoveryWord13 recovers_a_13
    · exact alternative_of_recovers_a 14 recoveryWord14 recovers_a_14
    · exact alternative_of_recovers_a 15 recoveryWord15 recovers_a_15
    · exact alternative_of_recovers_a 16 recoveryWord16 recovers_a_16
    · exact alternative_of_recovers_a 17 recoveryWord17 recovers_a_17
    · exact alternative_of_recovers_a 18 recoveryWord18 recovers_a_18
    · exact alternative_of_recovers_a 19 recoveryWord19 recovers_a_19
    · exact alternative_of_recovers_a 20 recoveryWord20 recovers_a_20
    · exact alternative_of_recovers_a 21 recoveryWord21 recovers_a_21
    · exact alternative_of_recovers_a 22 recoveryWord22 recovers_a_22
    · exact alternative_of_recovers_a 23 recoveryWord23 recovers_a_23
    · exact alternative_of_recovers_a 24 recoveryWord24 recovers_a_24
    · exact alternative_of_recovers_a 25 recoveryWord25 recovers_a_25
    · exact alternative_of_recovers_a 26 recoveryWord26 recovers_a_26
    · exact alternative_of_recovers_a 27 recoveryWord27 recovers_a_27
    · exact alternative_of_recovers_a 28 recoveryWord28 recovers_a_28
    · exact alternative_of_recovers_a 29 recoveryWord29 recovers_a_29
    · exact alternative_of_recovers_a 30 recoveryWord30 recovers_a_30
    · exact alternative_of_recovers_a 31 recoveryWord31 recovers_a_31
    · exact alternative_of_recovers_a 32 recoveryWord32 recovers_a_32
    · exact alternative_of_recovers_a 33 recoveryWord33 recovers_a_33
    · exact alternative_of_recovers_a 34 recoveryWord34 recovers_a_34
    · exact alternative_of_recovers_a 35 recoveryWord35 recovers_a_35
    · exact alternative_of_recovers_a 36 recoveryWord36 recovers_a_36
    · exact alternative_of_recovers_a 37 recoveryWord37 recovers_a_37
    · exact alternative_of_recovers_a 38 recoveryWord38 recovers_a_38
    · exact alternative_of_recovers_a 39 recoveryWord39 recovers_a_39
    · exact alternative_of_recovers_a 40 recoveryWord40 recovers_a_40
    · exact alternative_of_recovers_a 41 recoveryWord41 recovers_a_41
    · exact alternative_of_recovers_a 42 recoveryWord42 recovers_a_42
    · exact alternative_of_recovers_a 43 recoveryWord43 recovers_a_43
    · exact alternative_of_recovers_a 44 recoveryWord44 recovers_a_44
    · exact alternative_of_recovers_a 45 recoveryWord45 recovers_a_45
    · exact alternative_of_recovers_a 46 recoveryWord46 recovers_a_46
    · exact alternative_of_recovers_a 47 recoveryWord47 recovers_a_47
    · exact alternative_of_recovers_a 48 recoveryWord48 recovers_a_48
    · exact alternative_of_recovers_a 49 recoveryWord49 recovers_a_49
    · exact alternative_of_recovers_a 50 recoveryWord50 recovers_a_50
    · exact alternative_of_recovers_a 51 recoveryWord51 recovers_a_51
    · exact alternative_of_recovers_a 52 recoveryWord52 recovers_a_52
    · exact alternative_of_recovers_a 53 recoveryWord53 recovers_a_53
    · exact alternative_of_recovers_a 54 recoveryWord54 recovers_a_54
    · exact alternative_of_recovers_a 55 recoveryWord55 recovers_a_55
    · exact alternative_of_recovers_a 56 recoveryWord56 recovers_a_56
    · exact alternative_of_recovers_a 57 recoveryWord57 recovers_a_57
    · exact alternative_of_recovers_a 58 recoveryWord58 recovers_a_58
    · exact alternative_of_recovers_a 59 recoveryWord59 recovers_a_59
    · exact alternative_of_recovers_a 60 recoveryWord60 recovers_a_60
    · exact alternative_of_recovers_a 61 recoveryWord61 recovers_a_61
  let j : Fin 56 := ⟨i.val - 6, by omega⟩
  have hj : (⟨j.val + 6, by omega⟩ : Index) = i := Fin.ext (by dsimp [j]; omega)
  exact hj ▸ hall j

end Rudvalis.SylowOvergroups.TwoCore.Generation.RepresentativeChecks
