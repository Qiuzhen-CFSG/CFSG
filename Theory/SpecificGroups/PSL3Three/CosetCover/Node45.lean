module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 45

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets45
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 855) (.leaf 882))) (.branch 6 (.branch 5 (.leaf 975) (.leaf 1002)) (.branch 7 (.leaf 1029) (.leaf 1056)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1083) (.leaf 1110)) (.branch 11 (.leaf 1137) (.leaf 1164))) (.branch 14 (.branch 13 (.leaf 1191) (.leaf 2459)) (.branch 15 (.leaf 2486) (.leaf 2513))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2540) (.leaf 2567)) (.branch 19 (.leaf 2594) (.leaf 2621))) (.branch 22 (.branch 21 (.leaf 2648) (.leaf 3161)) (.branch 23 (.leaf 3188) (.leaf 3215)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3242) (.leaf 3269)) (.branch 27 (.leaf 3296) (.leaf 3323))) (.branch 30 (.branch 29 (.leaf 3350) (.leaf 3377)) (.branch 31 (.leaf 3890) (.leaf 3917))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 3 (.branch 1 (.leaf 3944) (.branch 2 (.leaf 3971) (.leaf 3998))) (.branch 5 (.branch 4 (.leaf 4025) (.leaf 4052)) (.branch 6 (.leaf 4079) (.leaf 4106))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 39) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 0, 4, 0]) (.leaf ![4, 3, 0, 2])) (.branch 3 (.leaf ![6, 1, 15, 3]) (.leaf ![5, 2, 18, 1]))) (.branch 6 (.branch 5 (.leaf ![0, 21, 1, 30]) (.leaf ![18, 25, 3, 37])) (.branch 7 (.leaf ![15, 29, 2, 35]) (.leaf ![21, 24, 13, 33])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![29, 28, 16, 31]) (.leaf ![25, 23, 19, 38])) (.branch 11 (.leaf ![30, 27, 14, 36]) (.leaf ![37, 22, 20, 34]))) (.branch 14 (.branch 13 (.leaf ![35, 26, 17, 32]) (.leaf ![7, 16, 21, 19])) (.branch 15 (.leaf ![10, 20, 30, 17]) (.leaf ![2, 15, 6, 15]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![8, 19, 29, 13]) (.leaf ![12, 14, 35, 20])) (.branch 19 (.leaf ![3, 18, 5, 18]) (.leaf ![9, 13, 25, 16]))) (.branch 22 (.branch 21 (.leaf ![11, 17, 37, 14]) (.leaf ![13, 30, 7, 4])) (.branch 23 (.leaf ![38, 34, 24, 11]) (.leaf ![26, 38, 33, 9])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![22, 33, 38, 7]) (.leaf ![19, 37, 9, 5])) (.branch 27 (.leaf ![33, 32, 23, 12]) (.leaf ![31, 36, 28, 10]))) (.branch 30 (.branch 29 (.leaf ![27, 31, 31, 8]) (.leaf ![16, 35, 8, 6])) (.branch 31 (.leaf ![14, 4, 10, 21]) (.leaf ![28, 8, 27, 28]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 39) := (.branch 3 (.branch 1 (.leaf ![34, 12, 36, 26]) (.branch 2 (.leaf ![23, 7, 26, 24]) (.leaf ![36, 11, 32, 22]))) (.branch 5 (.branch 4 (.leaf ![17, 6, 12, 29]) (.leaf ![32, 10, 34, 27])) (.branch 6 (.leaf ![20, 5, 11, 25]) (.leaf ![24, 9, 22, 23]))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 38) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![9, 10, 0, 14]) (.leaf ![9, 24, 9, 36])) (.branch 3 (.leaf ![33, 37, 0, 8]) (.leaf ![30, 5, 0, 23]))) (.branch 6 (.branch 5 (.leaf ![0, 32, 9, 25]) (.leaf ![33, 32, 33, 25])) (.branch 7 (.leaf ![30, 32, 30, 25]) (.leaf ![9, 32, 10, 25])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![33, 32, 12, 25]) (.leaf ![30, 32, 28, 25])) (.branch 11 (.leaf ![9, 32, 3, 25]) (.leaf ![33, 32, 27, 25]))) (.branch 14 (.branch 13 (.leaf ![30, 32, 22, 25]) (.leaf ![14, 31, 19, 32])) (.branch 15 (.leaf ![4, 31, 7, 32]) (.leaf ![0, 31, 33, 32]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![15, 31, 1, 32]) (.leaf ![17, 31, 35, 32])) (.branch 19 (.leaf ![0, 31, 30, 32]) (.leaf ![29, 31, 11, 32]))) (.branch 22 (.branch 21 (.leaf ![21, 31, 18, 32]) (.leaf ![20, 26, 9, 31])) (.branch 23 (.leaf ![13, 26, 19, 31]) (.leaf ![2, 26, 7, 31])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![20, 26, 35, 31]) (.leaf ![13, 26, 33, 31])) (.branch 27 (.leaf ![2, 26, 1, 31]) (.leaf ![20, 26, 11, 31]))) (.branch 30 (.branch 29 (.leaf ![13, 26, 18, 31]) (.leaf ![2, 26, 30, 31])) (.branch 31 (.leaf ![6, 26, 9, 25]) (.leaf ![16, 26, 19, 25]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 38) := (.branch 3 (.branch 1 (.leaf ![34, 26, 7, 25]) (.branch 2 (.leaf ![6, 26, 1, 25]) (.leaf ![16, 26, 35, 25]))) (.branch 5 (.branch 4 (.leaf ![34, 26, 33, 25]) (.leaf ![6, 26, 18, 25])) (.branch 6 (.leaf ![16, 26, 30, 25]) (.leaf ![34, 26, 11, 25]))))
@[expose] public def codes : Fin 39 → MatrixCode := fun j =>
  ((.branch 1 (.leaf codeBlock0) (.leaf codeBlock1)) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 39, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 39 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 39)
    (fun j => (codeDet (codes j)).val == 1) detCheck_0
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 39) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 38 → List (Fin 4) := fun j =>
  ((.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 3])) (.branch 3 (.leaf [1, 0]) (.leaf [0, 1, 1]))) (.branch 6 (.branch 5 (.leaf [1, 1, 0]) (.leaf [0, 3, 0, 1])) (.branch 7 (.leaf [0, 3, 0, 3]) (.branch 8 (.leaf [1, 0, 1, 0]) (.leaf [3, 0, 1, 0]))))) (.branch 14 (.branch 11 (.branch 10 (.leaf [0, 3, 0, 1, 0]) (.leaf [0, 1, 1, 0, 1, 1])) (.branch 12 (.leaf [0, 3, 0, 1, 0, 3]) (.branch 13 (.leaf [1, 0, 1, 1, 0, 1]) (.leaf [1, 0, 3, 0, 1, 0])))) (.branch 16 (.branch 15 (.leaf [1, 1, 0, 1, 1, 0]) (.leaf [3, 0, 1, 1, 0, 3])) (.branch 17 (.leaf [0, 1, 0, 1, 0, 3, 0]) (.branch 18 (.leaf [0, 1, 0, 1, 1, 0, 3]) (.leaf [0, 1, 0, 3, 0, 3, 0])))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf [0, 1, 1, 0, 3, 0, 1]) (.leaf [0, 3, 0, 3, 0, 1, 1])) (.branch 22 (.leaf [1, 0, 1, 0, 1, 0, 1]) (.leaf [1, 0, 1, 1, 0, 3, 0]))) (.branch 25 (.branch 24 (.leaf [1, 1, 0, 1, 0, 1, 1]) (.leaf [1, 1, 0, 3, 0, 1, 1])) (.branch 26 (.leaf [3, 0, 1, 0, 1, 0, 1]) (.branch 27 (.leaf [3, 0, 3, 0, 3, 0, 1]) (.leaf [3, 0, 3, 0, 3, 0, 3]))))) (.branch 33 (.branch 30 (.branch 29 (.leaf [0, 1, 0, 1, 0, 1, 0, 3]) (.leaf [0, 1, 0, 1, 1, 0, 1, 0])) (.branch 31 (.leaf [0, 1, 1, 0, 1, 0, 1, 1]) (.branch 32 (.leaf [0, 3, 0, 1, 0, 1, 0, 1]) (.leaf [0, 3, 0, 3, 0, 3, 0, 1])))) (.branch 35 (.branch 34 (.leaf [1, 0, 1, 1, 0, 1, 0, 3]) (.leaf [0, 1, 0, 1, 0, 1, 1, 0, 1])) (.branch 36 (.leaf [0, 1, 0, 1, 0, 1, 1, 0, 3]) (.branch 37 (.leaf [0, 1, 0, 1, 1, 0, 1, 0, 3]) (.leaf [0, 1, 1, 0, 1, 0, 1, 1, 0]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 38 → MatrixCode := fun j =>
  ((.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 9335)) (.branch 3 (.leaf 15974) (.leaf 6728))) (.branch 6 (.branch 5 (.leaf 6731) (.leaf 2674)) (.branch 7 (.leaf 4624) (.branch 8 (.leaf 2692) (.leaf 4618))))) (.branch 14 (.branch 11 (.branch 10 (.leaf 2432) (.leaf 6646)) (.branch 12 (.leaf 15977) (.branch 13 (.leaf 6664) (.leaf 9341)))) (.branch 16 (.branch 15 (.leaf 6649) (.leaf 6658)) (.branch 17 (.leaf 18088) (.branch 18 (.leaf 6749) (.leaf 9172)))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf 2450) (.leaf 2438)) (.branch 22 (.leaf 6740) (.leaf 6746))) (.branch 25 (.branch 24 (.leaf 11584) (.leaf 15634)) (.branch 26 (.leaf 13214) (.branch 27 (.leaf 13223) (.leaf 6737))))) (.branch 33 (.branch 30 (.branch 29 (.leaf 6655) (.leaf 6667)) (.branch 31 (.leaf 15959) (.branch 32 (.leaf 6661) (.leaf 6652)))) (.branch 35 (.branch 34 (.leaf 9317) (.leaf 11599)) (.branch 36 (.leaf 15652) (.branch 37 (.leaf 18064) (.leaf 9154))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 45) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 39 → Fin 4 → Fin 39 := fun j =>
  ((.branch 1 (.leaf nextBlock0) (.leaf nextBlock1)) : Lean.RArray (Lean.RArray (Fin 4 → Fin 39))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 39 → Fin 4 → Fin 38 := fun j =>
  ((.branch 1 (.leaf factorBlock0) (.leaf factorBlock1)) : Lean.RArray (Lean.RArray (Fin 4 → Fin 38))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 39 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 39) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 39, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 39 = true := by decide +kernel

public theorem checked : ∀ j, transitionCheck j = true :=
  checkRange_fin (by decide) transitionCheck rowCheck_0
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 45) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 45) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 45) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 45) (symmInv (n := (generatorCodes 45).length))
    (nodeGenerator_inv 45) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets45
