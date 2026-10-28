module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 44

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets44
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 828)) (.branch 3 (.leaf 829) (.leaf 830))) (.branch 6 (.branch 5 (.leaf 831) (.leaf 832)) (.branch 7 (.leaf 833) (.leaf 834)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 835) (.leaf 836)) (.branch 11 (.leaf 855) (.leaf 856))) (.branch 14 (.branch 13 (.leaf 857) (.leaf 858)) (.branch 15 (.leaf 859) (.leaf 860))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 861) (.leaf 862)) (.branch 19 (.leaf 863) (.leaf 882))) (.branch 22 (.branch 21 (.leaf 883) (.leaf 884)) (.branch 23 (.leaf 885) (.leaf 886)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 887) (.leaf 888)) (.branch 27 (.leaf 889) (.leaf 890))) (.branch 30 (.branch 29 (.leaf 975) (.leaf 976)) (.branch 31 (.leaf 977) (.leaf 1002))))))

@[expose] public def codeBlock1 : Lean.RArray (MatrixCode) := (.branch 3 (.branch 1 (.leaf 1003) (.branch 2 (.leaf 1004) (.leaf 1029))) (.branch 5 (.branch 4 (.leaf 1030) (.leaf 1031)) (.branch 6 (.leaf 2513) (.leaf 2594))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 39) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![1, 29, 28, 30]) (.leaf ![28, 19, 0, 10])) (.branch 3 (.leaf ![4, 23, 30, 17]) (.leaf ![7, 27, 29, 15]))) (.branch 6 (.branch 5 (.leaf ![30, 22, 2, 13]) (.leaf ![24, 26, 17, 11])) (.branch 7 (.leaf ![26, 21, 23, 18]) (.leaf ![29, 25, 3, 16])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![14, 20, 15, 14]) (.leaf ![18, 24, 27, 12])) (.branch 11 (.leaf ![34, 1, 37, 19]) (.leaf ![22, 5, 33, 26]))) (.branch 14 (.branch 13 (.leaf ![16, 9, 35, 24]) (.leaf ![36, 4, 20, 22])) (.branch 15 (.leaf ![15, 8, 8, 20]) (.leaf ![8, 3, 14, 27]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![35, 7, 12, 25]) (.leaf ![5, 2, 24, 23])) (.branch 19 (.leaf ![27, 6, 9, 21]) (.leaf ![31, 10, 38, 1]))) (.branch 22 (.branch 21 (.leaf ![13, 14, 36, 8]) (.leaf ![25, 18, 32, 6])) (.branch 23 (.leaf ![33, 13, 11, 4]) (.leaf ![6, 17, 26, 2])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![17, 12, 5, 9]) (.leaf ![32, 16, 21, 7])) (.branch 27 (.leaf ![23, 11, 6, 5]) (.leaf ![9, 15, 18, 3]))) (.branch 30 (.branch 29 (.leaf ![0, 28, 1, 28]) (.leaf ![3, 30, 7, 0])) (.branch 31 (.leaf ![2, 0, 4, 29]) (.leaf ![38, 31, 19, 31]))))))

@[expose] public def nextBlock1 : Lean.RArray (Fin 4 → Fin 39) := (.branch 3 (.branch 1 (.leaf ![21, 36, 25, 38]) (.branch 2 (.leaf ![11, 37, 22, 35]) (.leaf ![37, 34, 10, 34]))) (.branch 5 (.branch 4 (.leaf ![12, 33, 16, 37]) (.leaf ![20, 38, 13, 32])) (.branch 6 (.leaf ![10, 35, 34, 33]) (.leaf ![19, 32, 31, 36]))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 38) := (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf ![3, 20, 0, 34]) (.leaf ![3, 7, 3, 9])) (.branch 3 (.leaf ![10, 7, 14, 9]) (.leaf ![18, 7, 31, 9]))) (.branch 6 (.branch 5 (.leaf ![3, 7, 11, 9]) (.leaf ![10, 7, 24, 9])) (.branch 7 (.leaf ![18, 7, 21, 9]) (.leaf ![3, 7, 16, 9])))) (.branch 12 (.branch 10 (.branch 9 (.leaf ![10, 7, 6, 9]) (.leaf ![18, 7, 28, 9])) (.branch 11 (.leaf ![19, 12, 0, 5]) (.leaf ![27, 12, 26, 5]))) (.branch 14 (.branch 13 (.leaf ![8, 12, 1, 5]) (.leaf ![19, 12, 21, 5])) (.branch 15 (.leaf ![27, 12, 11, 5]) (.leaf ![8, 12, 24, 5]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf ![19, 12, 6, 5]) (.leaf ![27, 12, 28, 5])) (.branch 19 (.leaf ![8, 12, 16, 5]) (.leaf ![25, 4, 0, 13]))) (.branch 22 (.branch 21 (.leaf ![23, 4, 37, 13]) (.leaf ![33, 4, 32, 13])) (.branch 23 (.leaf ![25, 4, 24, 13]) (.leaf ![23, 4, 21, 13])))) (.branch 28 (.branch 26 (.branch 25 (.leaf ![33, 4, 11, 13]) (.leaf ![25, 4, 28, 13])) (.branch 27 (.leaf ![23, 4, 16, 13]) (.leaf ![33, 4, 6, 13]))) (.branch 30 (.branch 29 (.leaf ![0, 14, 3, 22]) (.leaf ![35, 31, 3, 15])) (.branch 31 (.leaf ![22, 29, 3, 35]) (.leaf ![19, 26, 19, 17]))))))

@[expose] public def factorBlock1 : Lean.RArray (Fin 4 → Fin 38) := (.branch 3 (.branch 1 (.leaf ![30, 1, 19, 30]) (.branch 2 (.leaf ![17, 17, 19, 30]) (.leaf ![25, 37, 25, 36]))) (.branch 5 (.branch 4 (.leaf ![2, 32, 25, 2]) (.leaf ![36, 36, 25, 2])) (.branch 6 (.leaf ![0, 1, 19, 26]) (.leaf ![0, 32, 25, 37]))))
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
  ((.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 0, 1])) (.branch 3 (.leaf [1, 0, 0]) (.leaf [2, 1, 0]))) (.branch 6 (.branch 5 (.leaf [0, 1, 0, 1]) (.leaf [1, 2, 1, 2])) (.branch 7 (.leaf [0, 1, 0, 1, 2]) (.branch 8 (.leaf [0, 1, 2, 1, 0]) (.leaf [0, 1, 2, 1, 2]))))) (.branch 14 (.branch 11 (.branch 10 (.leaf [1, 0, 0, 1, 0]) (.leaf [1, 0, 1, 0, 1])) (.branch 12 (.leaf [1, 2, 1, 2, 1]) (.branch 13 (.leaf [2, 1, 0, 0, 1]) (.leaf [2, 1, 0, 1, 2])))) (.branch 16 (.branch 15 (.leaf [0, 0, 1, 0, 0, 1]) (.leaf [0, 0, 1, 0, 1, 2])) (.branch 17 (.leaf [0, 0, 1, 2, 1, 2]) (.branch 18 (.leaf [0, 1, 0, 0, 1, 0]) (.leaf [0, 1, 0, 1, 0, 0])))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf [0, 1, 0, 1, 0, 1]) (.leaf [0, 1, 2, 1, 0, 0])) (.branch 22 (.leaf [0, 1, 2, 1, 2, 1]) (.leaf [1, 0, 0, 1, 0, 0]))) (.branch 25 (.branch 24 (.leaf [1, 0, 1, 0, 1, 2]) (.leaf [1, 2, 1, 0, 1, 0])) (.branch 26 (.leaf [1, 2, 1, 2, 1, 2]) (.branch 27 (.leaf [2, 1, 0, 0, 1, 2]) (.leaf [2, 1, 2, 1, 0, 1]))))) (.branch 33 (.branch 30 (.branch 29 (.leaf [0, 0, 1, 0, 0, 1, 0]) (.leaf [0, 0, 1, 2, 1, 0, 1])) (.branch 31 (.leaf [0, 1, 0, 0, 1, 2, 1]) (.branch 32 (.leaf [0, 1, 0, 1, 0, 1, 0]) (.leaf [0, 1, 2, 1, 2, 1, 0])))) (.branch 35 (.branch 34 (.leaf [1, 0, 1, 2, 1, 0, 1]) (.leaf [1, 2, 1, 0, 1, 0, 0])) (.branch 36 (.leaf [2, 1, 2, 1, 2, 1, 2]) (.branch 37 (.leaf [0, 1, 2, 1, 0, 1, 0, 1]) (.leaf [0, 1, 2, 1, 2, 1, 2, 1]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 38 → MatrixCode := fun j =>
  ((.branch 19 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 13961)) (.branch 3 (.leaf 14690) (.leaf 2432))) (.branch 6 (.branch 5 (.leaf 2674) (.leaf 4618)) (.branch 7 (.leaf 15688) (.branch 8 (.leaf 15634) (.leaf 13096))))) (.branch 14 (.branch 11 (.branch 10 (.leaf 18064) (.leaf 3890)) (.branch 12 (.leaf 2486) (.branch 13 (.leaf 9154) (.leaf 11584)))) (.branch 16 (.branch 15 (.leaf 7372) (.leaf 5347)) (.branch 17 (.leaf 2728) (.branch 18 (.leaf 8155) (.leaf 6076)))))) (.branch 28 (.branch 23 (.branch 21 (.branch 20 (.leaf 9317) (.leaf 2701)) (.branch 22 (.leaf 9371) (.leaf 8101))) (.branch 25 (.branch 24 (.leaf 17444) (.leaf 16013)) (.branch 26 (.leaf 15959) (.branch 27 (.leaf 7399) (.leaf 10829))))) (.branch 33 (.branch 30 (.branch 29 (.leaf 9208) (.leaf 3161)) (.branch 31 (.leaf 14717) (.branch 32 (.leaf 13934) (.leaf 13988)))) (.branch 35 (.branch 34 (.leaf 19549) (.leaf 2459)) (.branch 36 (.leaf 14663) (.branch 37 (.leaf 8128) (.leaf 7426))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 44) (words j)).val =
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 44) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 44) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 44) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 44) (symmInv (n := (generatorCodes 44).length))
    (nodeGenerator_inv 44) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets44
