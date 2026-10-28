module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 36

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets36
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 975) (.leaf 1002)) (.branch 7 (.leaf 1029) (.leaf 1056)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1083) (.leaf 1110)) (.branch 11 (.leaf 1137) (.leaf 1164))) (.branch 14 (.branch 13 (.leaf 1191) (.leaf 1548)) (.branch 15 (.leaf 1575) (.leaf 1602))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1707) (.leaf 1734)) (.branch 19 (.leaf 1761) (.leaf 1788))) (.branch 22 (.branch 21 (.leaf 1815) (.leaf 1842)) (.branch 23 (.leaf 1869) (.leaf 1896)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 1923) (.leaf 2304)) (.branch 27 (.leaf 2459) (.leaf 2486))) (.branch 30 (.branch 29 (.leaf 2513) (.leaf 2540)) (.branch 31 (.leaf 2567) (.leaf 2594))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 2621) (.leaf 2648)) (.branch 3 (.leaf 3161) (.leaf 3188))) (.branch 6 (.branch 5 (.leaf 3215) (.leaf 3242)) (.branch 7 (.leaf 3269) (.leaf 3296)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 3323) (.leaf 3350)) (.branch 11 (.leaf 3377) (.leaf 3890))) (.branch 14 (.branch 13 (.leaf 3917) (.leaf 3944)) (.branch 15 (.leaf 3971) (.leaf 3998))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 4025) (.leaf 4052)) (.branch 19 (.leaf 4079) (.leaf 4106))) (.branch 22 (.branch 21 (.leaf 4581) (.leaf 4618)) (.branch 23 (.leaf 4645) (.leaf 4672)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 4699) (.leaf 4726)) (.branch 27 (.leaf 4753) (.leaf 4780))) (.branch 30 (.branch 29 (.leaf 4807) (.leaf 4834)) (.branch 31 (.leaf 5347) (.leaf 5374))))))

@[expose] public def codeBlock2 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 5401) (.leaf 5428)) (.branch 3 (.leaf 5455) (.leaf 5482))) (.branch 6 (.branch 5 (.leaf 5509) (.leaf 5536)) (.branch 7 (.leaf 5563) (.leaf 6076)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 6103) (.leaf 6130)) (.branch 11 (.leaf 6157) (.leaf 6184))) (.branch 14 (.branch 13 (.leaf 6211) (.leaf 6238)) (.branch 15 (.leaf 6265) (.leaf 6292))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 6837) (.leaf 6886)) (.branch 19 (.leaf 6913) (.leaf 6940))) (.branch 22 (.branch 21 (.leaf 7615) (.leaf 7642)) (.branch 23 (.leaf 7669) (.leaf 8344)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 8371) (.leaf 8398)) (.branch 27 (.leaf 9105) (.leaf 11373))) (.branch 30 (.branch 29 (.leaf 13638) (.leaf 13691)) (.branch 31 (.leaf 13718) (.leaf 13745))))))

@[expose] public def codeBlock3 : Lean.RArray (MatrixCode) := (.branch 4 (.branch 2 (.branch 1 (.leaf 14420) (.leaf 14447)) (.branch 3 (.leaf 14474) (.leaf 15149))) (.branch 6 (.branch 5 (.leaf 15176) (.leaf 15203)) (.branch 7 (.leaf 15906) (.leaf 18174))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 0, 4, 0]) (.leaf ![4, 25, 0, 13])) (.branch 3 (.leaf ![80, 2, 28, 2]) (.leaf ![16, 14, 31, 52]))) (.branch 6 (.branch 5 (.leaf ![0, 34, 1, 62]) (.leaf ![81, 38, 25, 69])) (.branch 7 (.leaf ![53, 42, 13, 67]) (.leaf ![34, 37, 26, 65])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![82, 41, 29, 63]) (.leaf ![71, 36, 32, 70])) (.branch 11 (.leaf ![43, 40, 33, 68]) (.leaf ![83, 35, 30, 66]))) (.branch 14 (.branch 13 (.leaf ![62, 39, 27, 64]) (.leaf ![6, 1, 53, 25])) (.branch 15 (.leaf ![17, 52, 56, 3]) (.leaf ![92, 15, 59, 15]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![31, 71, 3, 43]) (.leaf ![56, 75, 14, 50])) (.branch 19 (.leaf ![93, 79, 52, 48]) (.leaf ![42, 74, 54, 46]))) (.branch 22 (.branch 21 (.leaf ![75, 78, 57, 44]) (.leaf ![94, 73, 60, 51])) (.branch 23 (.leaf ![50, 77, 58, 49]) (.leaf ![67, 72, 55, 47])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![95, 76, 61, 45]) (.leaf ![5, 13, 81, 1])) (.branch 27 (.leaf ![7, 29, 34, 32]) (.leaf ![12, 33, 62, 30]))) (.branch 30 (.branch 29 (.leaf ![2, 28, 80, 28]) (.leaf ![8, 32, 82, 26])) (.branch 31 (.leaf ![11, 27, 83, 33]) (.leaf ![3, 31, 16, 31]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![9, 26, 71, 29]) (.leaf ![10, 30, 43, 27])) (.branch 3 (.leaf ![26, 62, 7, 4]) (.leaf ![84, 66, 37, 11]))) (.branch 6 (.branch 5 (.leaf ![72, 70, 65, 9]) (.leaf ![35, 65, 84, 7])) (.branch 7 (.leaf ![85, 69, 90, 5]) (.leaf ![63, 64, 87, 12])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![44, 68, 74, 10]) (.leaf ![86, 63, 46, 8])) (.branch 11 (.leaf ![54, 67, 19, 6]) (.leaf ![33, 16, 10, 71]))) (.branch 14 (.branch 13 (.leaf ![74, 20, 40, 78]) (.leaf ![96, 24, 68, 76])) (.branch 15 (.leaf ![41, 19, 86, 74]) (.leaf ![66, 23, 88, 72]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![97, 18, 91, 79]) (.leaf ![49, 22, 49, 77])) (.branch 19 (.leaf ![58, 17, 22, 75]) (.leaf ![98, 21, 77, 73]))) (.branch 22 (.branch 21 (.leaf ![18, 3, 93, 14]) (.leaf ![13, 53, 6, 53])) (.branch 23 (.leaf ![19, 57, 42, 60]) (.leaf ![23, 61, 67, 58])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![14, 56, 17, 56]) (.leaf ![20, 60, 75, 54])) (.branch 27 (.leaf ![22, 55, 50, 61]) (.leaf ![15, 59, 92, 59]))) (.branch 30 (.branch 29 (.leaf ![21, 54, 94, 57]) (.leaf ![24, 58, 95, 55])) (.branch 31 (.leaf ![27, 4, 12, 34]) (.leaf ![87, 8, 39, 41]))))))

@[expose] public def nextBlock2 : Lean.RArray (Fin 4 → Fin 104) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![64, 12, 64, 39]) (.leaf ![36, 7, 72, 37])) (.branch 3 (.leaf ![88, 11, 47, 35]) (.leaf ![55, 6, 23, 42]))) (.branch 6 (.branch 5 (.leaf ![45, 10, 96, 40]) (.leaf ![89, 5, 102, 38])) (.branch 7 (.leaf ![73, 9, 99, 36]) (.leaf ![32, 43, 9, 16])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![65, 47, 36, 23]) (.leaf ![99, 51, 70, 21])) (.branch 11 (.leaf ![40, 46, 44, 19]) (.leaf ![57, 50, 20, 17]))) (.branch 14 (.branch 13 (.leaf ![100, 45, 78, 24]) (.leaf ![51, 49, 98, 22])) (.branch 15 (.leaf ![76, 44, 100, 20]) (.leaf ![101, 48, 103, 18]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![28, 82, 2, 83]) (.leaf ![25, 81, 5, 81])) (.branch 19 (.leaf ![29, 83, 8, 80]) (.leaf ![30, 80, 11, 82]))) (.branch 22 (.branch 21 (.leaf ![37, 90, 35, 87]) (.leaf ![90, 85, 38, 85])) (.branch 23 (.leaf ![46, 88, 41, 91]) (.leaf ![39, 84, 63, 90])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![47, 91, 66, 86]) (.leaf ![102, 89, 69, 89])) (.branch 27 (.leaf ![38, 87, 85, 84]) (.leaf ![48, 86, 97, 88]))) (.branch 30 (.branch 29 (.leaf ![59, 94, 15, 95]) (.leaf ![52, 93, 18, 93])) (.branch 31 (.leaf ![60, 95, 21, 92]) (.leaf ![61, 92, 24, 94]))))))

@[expose] public def nextBlock3 : Lean.RArray (Fin 4 → Fin 104) := (.branch 4 (.branch 2 (.branch 1 (.leaf ![68, 102, 45, 99]) (.leaf ![91, 97, 48, 97])) (.branch 3 (.leaf ![77, 100, 51, 103]) (.leaf ![70, 96, 73, 102]))) (.branch 6 (.branch 5 (.leaf ![78, 103, 76, 98]) (.leaf ![103, 101, 79, 101])) (.branch 7 (.leaf ![69, 99, 89, 96]) (.leaf ![79, 98, 101, 100]))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![19, 2, 0, 3]) (.leaf ![19, 19, 19, 1])) (.branch 3 (.leaf ![0, 10, 0, 13]) (.leaf ![10, 19, 0, 10]))) (.branch 6 (.branch 5 (.leaf ![0, 30, 19, 31]) (.leaf ![0, 30, 0, 31])) (.branch 7 (.leaf ![10, 30, 10, 31]) (.leaf ![19, 30, 2, 31])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![0, 30, 37, 31]) (.leaf ![10, 30, 36, 31])) (.branch 11 (.leaf ![19, 30, 4, 31]) (.leaf ![0, 30, 24, 31]))) (.branch 14 (.branch 13 (.leaf ![10, 30, 33, 31]) (.leaf ![13, 1, 0, 13])) (.branch 15 (.leaf ![1, 1, 0, 19]) (.leaf ![0, 13, 0, 10]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![13, 30, 13, 31]) (.leaf ![1, 30, 1, 31])) (.branch 19 (.leaf ![0, 30, 0, 31]) (.leaf ![13, 30, 3, 31]))) (.branch 22 (.branch 21 (.leaf ![1, 30, 35, 31]) (.leaf ![0, 30, 40, 31])) (.branch 23 (.leaf ![13, 30, 14, 31]) (.leaf ![1, 30, 12, 31])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 30, 17, 31]) (.leaf ![0, 10, 0, 19])) (.branch 27 (.leaf ![3, 31, 21, 30]) (.leaf ![14, 31, 7, 30]))) (.branch 30 (.branch 29 (.leaf ![0, 31, 0, 30]) (.leaf ![40, 31, 40, 30])) (.branch 31 (.leaf ![17, 31, 17, 30]) (.leaf ![0, 31, 10, 30]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![35, 31, 23, 30]) (.leaf ![12, 31, 8, 30])) (.branch 3 (.leaf ![20, 30, 19, 31]) (.leaf ![31, 30, 21, 31]))) (.branch 6 (.branch 5 (.leaf ![32, 30, 7, 31]) (.leaf ![20, 30, 27, 31])) (.branch 7 (.leaf ![31, 30, 0, 31]) (.leaf ![32, 30, 22, 31])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![20, 30, 23, 31]) (.leaf ![31, 30, 8, 31])) (.branch 11 (.leaf ![32, 30, 10, 31]) (.leaf ![11, 30, 19, 31]))) (.branch 14 (.branch 13 (.leaf ![42, 30, 21, 31]) (.leaf ![30, 30, 7, 31])) (.branch 15 (.leaf ![11, 30, 6, 31]) (.leaf ![42, 30, 28, 31]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![30, 30, 0, 31]) (.leaf ![11, 30, 8, 31])) (.branch 19 (.leaf ![42, 30, 10, 31]) (.leaf ![30, 30, 23, 31]))) (.branch 22 (.branch 21 (.leaf ![0, 13, 0, 1]) (.leaf ![0, 31, 13, 30])) (.branch 23 (.leaf ![2, 31, 25, 30]) (.leaf ![4, 31, 16, 30])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![0, 31, 1, 30]) (.leaf ![36, 31, 38, 30])) (.branch 27 (.leaf ![33, 31, 39, 30]) (.leaf ![0, 31, 0, 30]))) (.branch 30 (.branch 29 (.leaf ![37, 31, 37, 30]) (.leaf ![24, 31, 24, 30])) (.branch 31 (.leaf ![5, 30, 13, 31]) (.leaf ![30, 30, 25, 31]))))))

@[expose] public def factorBlock2 : Lean.RArray (Fin 4 → Fin 43) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![18, 30, 16, 31]) (.leaf ![5, 30, 38, 31])) (.branch 3 (.leaf ![30, 30, 39, 31]) (.leaf ![18, 30, 1, 31]))) (.branch 6 (.branch 5 (.leaf ![5, 30, 15, 31]) (.leaf ![30, 30, 0, 31])) (.branch 7 (.leaf ![18, 30, 9, 31]) (.leaf ![26, 30, 13, 31])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![41, 30, 25, 31]) (.leaf ![31, 30, 16, 31])) (.branch 11 (.leaf ![26, 30, 39, 31]) (.leaf ![41, 30, 1, 31]))) (.branch 14 (.branch 13 (.leaf ![31, 30, 38, 31]) (.leaf ![26, 30, 29, 31])) (.branch 15 (.leaf ![41, 30, 34, 31]) (.leaf ![31, 30, 0, 31]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![0, 40, 0, 17]) (.leaf ![0, 37, 0, 40])) (.branch 19 (.leaf ![37, 24, 0, 37]) (.leaf ![24, 24, 0, 17]))) (.branch 22 (.branch 21 (.leaf ![15, 15, 30, 28]) (.leaf ![30, 9, 30, 6])) (.branch 23 (.leaf ![9, 15, 30, 9]) (.leaf ![29, 34, 31, 29])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![34, 34, 31, 27]) (.leaf ![31, 29, 31, 22])) (.branch 27 (.leaf ![0, 22, 31, 27]) (.leaf ![0, 6, 30, 28]))) (.branch 30 (.branch 29 (.leaf ![0, 37, 0, 24]) (.leaf ![0, 40, 0, 37])) (.branch 31 (.leaf ![40, 17, 0, 40]) (.leaf ![17, 17, 0, 24]))))))

@[expose] public def factorBlock3 : Lean.RArray (Fin 4 → Fin 43) := (.branch 4 (.branch 2 (.branch 1 (.leaf ![27, 27, 31, 34]) (.leaf ![31, 22, 31, 29])) (.branch 3 (.leaf ![22, 27, 31, 22]) (.leaf ![6, 28, 30, 6]))) (.branch 6 (.branch 5 (.leaf ![28, 28, 30, 15]) (.leaf ![30, 6, 30, 9])) (.branch 7 (.leaf ![0, 9, 30, 15]) (.leaf ![0, 29, 31, 34]))))
@[expose] public def codes : Fin 104 → MatrixCode := fun j =>
  ((.branch 2 (.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) (.branch 3 (.leaf codeBlock2) (.leaf codeBlock3))) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 104, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem detCheck_1 : checkRange detCheck 64 40 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 104)
    (fun j => (codeDet (codes j)).val == 1) (checkRange_append detCheck_0 detCheck_1)
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 104) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 43 → List (Fin 6) := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [1]) (.branch 4 (.leaf [4]) (.leaf [0, 2])))) (.branch 7 (.branch 6 (.leaf [0, 5]) (.leaf [1, 5])) (.branch 8 (.leaf [2, 0]) (.branch 9 (.leaf [2, 1]) (.leaf [2, 4]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [4, 2]) (.leaf [4, 5])) (.branch 13 (.leaf [5, 0]) (.branch 14 (.leaf [5, 1]) (.leaf [0, 1, 2])))) (.branch 18 (.branch 16 (.leaf [0, 1, 5]) (.branch 17 (.leaf [0, 2, 0]) (.leaf [0, 2, 4]))) (.branch 19 (.leaf [0, 5, 0]) (.branch 20 (.leaf [0, 5, 1]) (.leaf [0, 5, 4])))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf [1, 2, 0]) (.leaf [1, 2, 1])) (.branch 24 (.leaf [1, 2, 4]) (.branch 25 (.leaf [1, 5, 0]) (.leaf [1, 5, 1])))) (.branch 29 (.branch 27 (.leaf [1, 5, 4]) (.branch 28 (.leaf [2, 0, 1]) (.leaf [2, 0, 2]))) (.branch 30 (.leaf [2, 1, 2]) (.branch 31 (.leaf [2, 1, 5]) (.leaf [2, 4, 5]))))) (.branch 37 (.branch 34 (.branch 33 (.leaf [4, 2, 4]) (.leaf [5, 0, 1])) (.branch 35 (.leaf [5, 0, 5]) (.branch 36 (.leaf [5, 1, 2]) (.leaf [5, 4, 2])))) (.branch 40 (.branch 38 (.leaf [0, 2, 0, 2]) (.branch 39 (.leaf [0, 2, 1, 5]) (.leaf [0, 2, 4, 5]))) (.branch 41 (.leaf [0, 5, 0, 5]) (.branch 42 (.leaf [0, 5, 1, 2]) (.leaf [0, 5, 4, 2]))))))) : Lean.RArray (List (Fin 6))).get j.val
@[expose] public def wordCodes : Fin 43 → MatrixCode := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 17579)) (.branch 3 (.leaf 6646) (.branch 4 (.leaf 6649) (.leaf 7223)))) (.branch 7 (.branch 6 (.leaf 2435) (.leaf 17755)) (.branch 8 (.leaf 2441) (.branch 9 (.leaf 2854) (.leaf 2857))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 2836) (.leaf 17764)) (.branch 13 (.leaf 7217) (.branch 14 (.leaf 17740) (.leaf 7235)))) (.branch 18 (.branch 16 (.leaf 2453) (.branch 17 (.leaf 17758) (.leaf 7226))) (.branch 19 (.leaf 2839) (.branch 20 (.leaf 2432) (.leaf 2438)))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf 2450) (.leaf 2851)) (.branch 24 (.leaf 2845) (.branch 25 (.leaf 7232) (.leaf 17749)))) (.branch 29 (.branch 27 (.leaf 17752) (.branch 28 (.leaf 2447) (.leaf 17594))) (.branch 30 (.leaf 17761) (.branch 31 (.leaf 6652) (.leaf 6661))))) (.branch 37 (.branch 34 (.branch 33 (.leaf 2842) (.leaf 7214)) (.branch 35 (.leaf 17600) (.branch 36 (.leaf 6667) (.leaf 6655)))) (.branch 40 (.branch 38 (.leaf 6664) (.branch 39 (.leaf 17597) (.leaf 17588))) (.branch 41 (.leaf 6658) (.branch 42 (.leaf 17591) (.leaf 17603))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 36) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 104 → Fin 4 → Fin 104 := fun j =>
  ((.branch 2 (.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) (.branch 3 (.leaf nextBlock2) (.leaf nextBlock3))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 104))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 104 → Fin 4 → Fin 43 := fun j =>
  ((.branch 2 (.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) (.branch 3 (.leaf factorBlock2) (.leaf factorBlock3))) : Lean.RArray (Lean.RArray (Fin 4 → Fin 43))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 6 104 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 104) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 104, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 64 = true := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem rowCheck_1 : checkRange rowCheck 64 40 = true := by decide +kernel

public theorem checked : ∀ j, transitionCheck j = true :=
  checkRange_fin (by decide) transitionCheck (checkRange_append rowCheck_0 rowCheck_1)
public theorem transitions : ∀ j k, (rep j).val * (ambientGenerator k).val =
    decodeMatrix (wordCodes (factorIndex j k)) * (rep (next j k)).val := by
  intro j k
  have h := checked j
  simp only [transitionCheck, Bool.and_eq_true] at h
  fin_cases k
  · exact matrixEq_sound h.1.1.1
  · exact matrixEq_sound h.1.1.2
  · exact matrixEq_sound h.1.2
  · exact matrixEq_sound h.2
public theorem valid : table.Valid ambientGenerator (nodeGenerator 36) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 36) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 36) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 36) (symmInv (n := (generatorCodes 36).length))
    (nodeGenerator_inv 36) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets36
