module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 46

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets46
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 828) (.leaf 829))) (.branch 4 (.leaf 830) (.branch 5 (.leaf 831) (.leaf 832)))) (.branch 9 (.branch 7 (.leaf 833) (.branch 8 (.leaf 834) (.leaf 835))) (.branch 11 (.branch 10 (.leaf 836) (.leaf 900)) (.branch 12 (.leaf 901) (.leaf 902))))) (.branch 19 (.branch 16 (.branch 14 (.leaf 903) (.branch 15 (.leaf 904) (.leaf 905))) (.branch 17 (.leaf 906) (.branch 18 (.leaf 907) (.leaf 908)))) (.branch 22 (.branch 20 (.leaf 975) (.branch 21 (.leaf 976) (.leaf 977))) (.branch 24 (.branch 23 (.leaf 1221) (.leaf 1222)) (.branch 25 (.leaf 1223) (.leaf 2432))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 26) := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf ![10, 20, 19, 23]) (.branch 2 (.leaf ![22, 1, 25, 1]) (.leaf ![16, 5, 21, 8]))) (.branch 4 (.leaf ![7, 9, 24, 6]) (.branch 5 (.leaf ![23, 4, 12, 4]) (.leaf ![17, 8, 15, 2])))) (.branch 9 (.branch 7 (.leaf ![8, 3, 18, 9]) (.branch 8 (.leaf ![24, 7, 3, 7]) (.leaf ![18, 2, 6, 5]))) (.branch 11 (.branch 10 (.leaf ![9, 6, 9, 3]) (.leaf ![19, 10, 0, 10])) (.branch 12 (.leaf ![13, 14, 20, 17]) (.leaf ![4, 18, 23, 15]))))) (.branch 19 (.branch 16 (.branch 14 (.leaf ![20, 13, 11, 13]) (.branch 15 (.leaf ![14, 17, 14, 11]) (.leaf ![5, 12, 17, 18]))) (.branch 17 (.leaf ![21, 16, 2, 16]) (.branch 18 (.leaf ![15, 11, 5, 14]) (.leaf ![6, 15, 8, 12])))) (.branch 22 (.branch 20 (.leaf ![0, 19, 10, 19]) (.branch 21 (.leaf ![11, 23, 13, 0]) (.leaf ![2, 25, 16, 24]))) (.branch 24 (.branch 23 (.leaf ![25, 22, 1, 22]) (.leaf ![12, 0, 4, 20])) (.branch 25 (.leaf ![3, 21, 7, 25]) (.leaf ![1, 24, 22, 21]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 33) := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf ![8, 4, 0, 29]) (.branch 2 (.leaf ![8, 11, 0, 12]) (.leaf ![6, 11, 19, 12]))) (.branch 4 (.leaf ![13, 11, 18, 12]) (.branch 5 (.leaf ![8, 11, 14, 12]) (.leaf ![1, 11, 26, 12])))) (.branch 9 (.branch 7 (.leaf ![10, 11, 21, 12]) (.branch 8 (.leaf ![8, 11, 15, 12]) (.leaf ![5, 11, 16, 12]))) (.branch 11 (.branch 10 (.leaf ![20, 11, 22, 12]) (.leaf ![9, 12, 9, 11])) (.branch 12 (.leaf ![24, 12, 2, 11]) (.leaf ![17, 12, 25, 11]))))) (.branch 19 (.branch 16 (.branch 14 (.leaf ![9, 12, 29, 11]) (.branch 15 (.leaf ![32, 12, 31, 11]) (.leaf ![28, 12, 23, 11]))) (.branch 17 (.leaf ![9, 12, 4, 11]) (.branch 18 (.leaf ![30, 12, 3, 11]) (.leaf ![27, 12, 7, 11])))) (.branch 22 (.branch 20 (.leaf ![0, 19, 8, 25]) (.branch 21 (.leaf ![2, 18, 8, 6]) (.leaf ![25, 25, 8, 2]))) (.branch 24 (.branch 23 (.leaf ![9, 25, 9, 19]) (.leaf ![19, 24, 9, 18])) (.branch 25 (.leaf ![18, 2, 9, 18]) (.leaf ![0, 18, 8, 19]))))))
@[expose] public def codes : Fin 26 → MatrixCode := fun j =>
  ((.leaf codeBlock0) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 26, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 26 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 26)
    (fun j => (codeDet (codes j)).val == 1) detCheck_0
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 26) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 33 → List (Fin 4) := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0, 3])) (.branch 3 (.leaf [1, 1]) (.leaf [1, 2]))) (.branch 6 (.branch 5 (.leaf [0, 1, 2]) (.leaf [0, 3, 0])) (.branch 7 (.leaf [0, 3, 2]) (.leaf [2, 1, 2])))) (.branch 12 (.branch 10 (.branch 9 (.leaf [2, 3, 0, 1]) (.leaf [3, 2, 1, 0])) (.branch 11 (.leaf [0, 1, 0, 1, 1]) (.leaf [0, 1, 1, 0, 3]))) (.branch 14 (.branch 13 (.leaf [0, 3, 0, 1, 2]) (.leaf [1, 0, 1, 2, 3])) (.branch 15 (.leaf [1, 0, 3, 2, 1]) (.leaf [1, 0, 3, 2, 3]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf [1, 1, 2, 3, 2]) (.leaf [3, 0, 1, 2, 3])) (.branch 19 (.leaf [0, 1, 0, 1, 0, 1]) (.leaf [0, 1, 0, 1, 0, 3]))) (.branch 22 (.branch 21 (.leaf [0, 1, 0, 1, 1, 2]) (.leaf [0, 1, 0, 3, 2, 1])) (.branch 23 (.leaf [0, 1, 1, 2, 3, 2]) (.leaf [1, 1, 0, 1, 0, 1])))) (.branch 28 (.branch 26 (.branch 25 (.leaf [1, 1, 2, 3, 0, 1]) (.leaf [1, 2, 3, 2, 3, 2])) (.branch 27 (.leaf [2, 1, 0, 3, 2, 1]) (.leaf [2, 3, 2, 1, 0, 3]))) (.branch 30 (.branch 29 (.leaf [3, 0, 1, 2, 3, 0]) (.leaf [3, 2, 1, 0, 1, 1])) (.branch 31 (.leaf [3, 2, 3, 2, 1, 1]) (.branch 32 (.leaf [0, 3, 2, 1, 0, 1, 1]) (.leaf [1, 1, 2, 3, 0, 1, 2]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 33 → MatrixCode := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 18469)) (.branch 3 (.leaf 14014) (.leaf 2863))) (.branch 6 (.branch 5 (.leaf 2701) (.leaf 11908)) (.branch 7 (.leaf 5347) (.leaf 2782)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 4618) (.leaf 2674)) (.branch 11 (.leaf 12637) (.leaf 8830))) (.branch 14 (.branch 13 (.leaf 11017) (.leaf 6076)) (.branch 15 (.leaf 4645) (.leaf 2728))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 2809) (.leaf 4132)) (.branch 19 (.leaf 14743) (.leaf 7372))) (.branch 22 (.branch 21 (.leaf 19198) (.leaf 4807)) (.branch 23 (.leaf 2890) (.leaf 4753)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 3403) (.leaf 8101)) (.branch 27 (.leaf 4726) (.leaf 17254))) (.branch 30 (.branch 29 (.leaf 10693) (.leaf 4672)) (.branch 31 (.leaf 9964) (.branch 32 (.leaf 4834) (.leaf 16525))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 46) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 26 → Fin 4 → Fin 26 := fun j =>
  ((.leaf nextBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 26))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 26 → Fin 4 → Fin 33 := fun j =>
  ((.leaf factorBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 33))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 26 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 26) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 26, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 26 = true := by decide +kernel

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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 46) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 46) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 46) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 46) (symmInv (n := (generatorCodes 46).length))
    (nodeGenerator_inv 46) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets46
