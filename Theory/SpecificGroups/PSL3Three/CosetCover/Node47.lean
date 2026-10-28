module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 47

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets47
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 828) (.leaf 900))) (.branch 4 (.leaf 975) (.branch 5 (.leaf 1056) (.leaf 1137)))) (.branch 9 (.branch 7 (.leaf 1221) (.branch 8 (.leaf 1302) (.leaf 1383))) (.branch 11 (.branch 10 (.leaf 2432) (.leaf 2459)) (.branch 12 (.leaf 2486) (.leaf 2701))))) (.branch 19 (.branch 16 (.branch 14 (.leaf 2728) (.branch 15 (.leaf 3161) (.leaf 3188))) (.branch 17 (.leaf 3215) (.branch 18 (.leaf 3403) (.leaf 3430)))) (.branch 22 (.branch 20 (.leaf 3457) (.branch 21 (.leaf 3890) (.leaf 3917))) (.branch 24 (.branch 23 (.leaf 3944) (.leaf 4132)) (.branch 25 (.leaf 4159) (.leaf 4186))))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 26) := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf ![2, 0, 3, 0]) (.branch 2 (.leaf ![6, 1, 9, 1]) (.leaf ![3, 2, 0, 2]))) (.branch 4 (.leaf ![0, 14, 2, 23]) (.branch 5 (.leaf ![17, 16, 10, 25]) (.leaf ![23, 15, 12, 24])))) (.branch 9 (.branch 7 (.leaf ![9, 17, 1, 20]) (.branch 8 (.leaf ![20, 19, 11, 22]) (.leaf ![14, 18, 13, 21]))) (.branch 11 (.branch 10 (.leaf ![1, 9, 6, 9]) (.leaf ![4, 10, 17, 10])) (.branch 12 (.leaf ![7, 11, 20, 11]) (.leaf ![5, 12, 23, 12]))))) (.branch 19 (.branch 16 (.branch 14 (.leaf ![8, 13, 14, 13]) (.branch 15 (.leaf ![13, 23, 8, 3]) (.leaf ![25, 24, 18, 5]))) (.branch 17 (.leaf ![19, 25, 21, 4]) (.branch 18 (.leaf ![10, 20, 4, 6]) (.leaf ![15, 21, 25, 8])))) (.branch 22 (.branch 20 (.leaf ![21, 22, 16, 7]) (.branch 21 (.leaf ![11, 6, 7, 17]) (.leaf ![16, 8, 19, 18]))) (.branch 24 (.branch 23 (.leaf ![22, 7, 22, 19]) (.leaf ![12, 3, 5, 14])) (.branch 25 (.leaf ![24, 5, 24, 15]) (.leaf ![18, 4, 15, 16]))))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 43) := (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf ![7, 36, 0, 35]) (.branch 2 (.leaf ![7, 15, 0, 14]) (.leaf ![8, 14, 8, 15]))) (.branch 4 (.leaf ![0, 22, 7, 27]) (.branch 5 (.leaf ![7, 21, 36, 20]) (.leaf ![7, 9, 35, 12])))) (.branch 9 (.branch 7 (.leaf ![8, 24, 8, 42]) (.branch 8 (.leaf ![8, 10, 35, 40]) (.leaf ![8, 25, 36, 41]))) (.branch 11 (.branch 10 (.leaf ![0, 24, 7, 22]) (.leaf ![35, 10, 26, 9])) (.branch 12 (.leaf ![36, 25, 19, 21]) (.leaf ![36, 21, 13, 25]))))) (.branch 19 (.branch 16 (.branch 14 (.leaf ![35, 9, 5, 10]) (.branch 15 (.leaf ![6, 42, 7, 24]) (.leaf ![2, 40, 30, 10]))) (.branch 17 (.leaf ![3, 41, 16, 25]) (.branch 18 (.leaf ![31, 27, 8, 22]) (.leaf ![23, 20, 28, 21])))) (.branch 22 (.branch 20 (.leaf ![39, 12, 4, 9]) (.branch 21 (.leaf ![17, 42, 7, 27]) (.leaf ![11, 40, 38, 12]))) (.branch 24 (.branch 23 (.leaf ![32, 41, 33, 20]) (.leaf ![18, 27, 8, 42])) (.branch 25 (.leaf ![34, 20, 29, 41]) (.leaf ![37, 12, 1, 40]))))))
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
@[expose] public def words : Fin 43 → List (Fin 4) := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf []) (.leaf [1, 0])) (.branch 3 (.leaf [2, 3]) (.branch 4 (.leaf [0, 1, 0]) (.leaf [1, 0, 1])))) (.branch 7 (.branch 6 (.leaf [1, 0, 3]) (.leaf [1, 2, 3])) (.branch 8 (.leaf [0, 3, 2, 1]) (.branch 9 (.leaf [3, 0, 1, 2]) (.leaf [0, 0, 1, 0, 0]))))) (.branch 15 (.branch 12 (.branch 11 (.leaf [0, 0, 3, 0, 0]) (.leaf [0, 0, 3, 0, 3])) (.branch 13 (.leaf [0, 1, 2, 1, 0]) (.branch 14 (.leaf [0, 1, 2, 3, 0]) (.leaf [1, 0, 0, 1, 0])))) (.branch 18 (.branch 16 (.leaf [1, 0, 1, 2, 3]) (.branch 17 (.leaf [1, 2, 1, 0, 0]) (.leaf [2, 1, 0, 3, 0]))) (.branch 19 (.leaf [2, 1, 0, 3, 2]) (.branch 20 (.leaf [2, 1, 2, 3, 0]) (.leaf [2, 3, 0, 3, 2])))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf [0, 0, 1, 0, 0, 1]) (.leaf [0, 0, 1, 0, 0, 3])) (.branch 24 (.leaf [0, 0, 1, 2, 1, 2]) (.branch 25 (.leaf [0, 0, 3, 0, 0, 1]) (.leaf [0, 0, 3, 0, 0, 3])))) (.branch 29 (.branch 27 (.leaf [0, 0, 3, 0, 1, 2]) (.branch 28 (.leaf [0, 1, 0, 0, 3, 2]) (.leaf [0, 1, 2, 3, 0, 1]))) (.branch 30 (.leaf [0, 1, 2, 3, 0, 3]) (.branch 31 (.leaf [0, 3, 0, 3, 0, 0]) (.leaf [0, 3, 2, 1, 0, 0]))))) (.branch 37 (.branch 34 (.branch 33 (.leaf [1, 0, 0, 3, 0, 3]) (.leaf [1, 2, 1, 0, 0, 3])) (.branch 35 (.leaf [1, 2, 1, 0, 3, 2]) (.branch 36 (.leaf [1, 2, 1, 2, 1, 0]) (.leaf [2, 3, 0, 3, 0, 3])))) (.branch 40 (.branch 38 (.leaf [3, 2, 1, 0, 3, 2]) (.branch 39 (.leaf [0, 0, 3, 0, 1, 2, 3]) (.leaf [1, 0, 3, 2, 1, 0, 0]))) (.branch 41 (.leaf [2, 1, 0, 3, 2, 1, 0]) (.branch 42 (.leaf [2, 3, 0, 1, 2, 3, 0]) (.leaf [0, 0, 3, 0, 3, 0, 3, 2]))))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 43 → MatrixCode := fun j =>
  ((.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 15805)) (.branch 3 (.leaf 4783) (.branch 4 (.leaf 4702) (.leaf 9244)))) (.branch 7 (.branch 6 (.leaf 2683) (.leaf 4621)) (.branch 8 (.leaf 4618) (.branch 9 (.leaf 2674) (.leaf 7138))))) (.branch 15 (.branch 12 (.branch 11 (.leaf 6904) (.leaf 4705)) (.branch 13 (.leaf 13780) (.branch 14 (.leaf 4627) (.leaf 11017)))) (.branch 18 (.branch 16 (.leaf 8830) (.branch 17 (.leaf 9253) (.leaf 4624))) (.branch 19 (.leaf 2680) (.branch 20 (.leaf 2692) (.leaf 13537)))))) (.branch 32 (.branch 26 (.branch 23 (.branch 22 (.leaf 6895) (.leaf 6652)) (.branch 24 (.leaf 2758) (.branch 25 (.leaf 6661) (.leaf 7147)))) (.branch 29 (.branch 27 (.leaf 4636) (.branch 28 (.leaf 13294) (.leaf 11188))) (.branch 30 (.leaf 17749) (.branch 31 (.leaf 11197) (.leaf 2677))))) (.branch 37 (.branch 34 (.branch 33 (.leaf 4786) (.leaf 15814)) (.branch 35 (.leaf 2842) (.branch 36 (.leaf 6649) (.leaf 6646)))) (.branch 40 (.branch 38 (.leaf 2761) (.branch 39 (.leaf 17758) (.leaf 2839))) (.branch 41 (.leaf 13546) (.branch 42 (.leaf 13789) (.leaf 13303))))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 47) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 26 → Fin 4 → Fin 26 := fun j =>
  ((.leaf nextBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 26))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 26 → Fin 4 → Fin 43 := fun j =>
  ((.leaf factorBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 43))).get (j.val / 32) |>.get (j.val % 32)
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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 47) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 47) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 47) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 47) (symmInv (n := (generatorCodes 47).length))
    (nodeGenerator_inv 47) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets47
