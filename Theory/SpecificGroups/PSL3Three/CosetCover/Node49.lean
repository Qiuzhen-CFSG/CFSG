module
public import Theory.SpecificGroups.PSL3Three.CosetCover.Check
/-!
# Checked right cosets for node 49

These are untrusted matrix codes and subgroup words generated from the fixed
lists in `RepresentativeBounds`. The kernel checks determinants, word values,
and every transition by the four ambient generators. `cover` then follows from
`RightCosetTable.sound`, using the proved generation of the actual SL₃(3).

Source: the elementary coset-table argument in `SubgroupEnumeration` and
GLS III, Theorem 6.5.3. Row zero represents the identity matrix.
-/

namespace Matrix.PSL3Three.CertifiedEnumeration.Cosets49
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration CosetCheck
set_option maxRecDepth 100000

@[expose] public def codeBlock0 : Lean.RArray (MatrixCode) := (.branch 6 (.branch 3 (.branch 1 (.leaf 6643) (.branch 2 (.leaf 828) (.leaf 975))) (.branch 4 (.leaf 1056) (.branch 5 (.leaf 1137) (.leaf 2459)))) (.branch 9 (.branch 7 (.leaf 2486) (.branch 8 (.leaf 3161) (.leaf 3188))) (.branch 11 (.branch 10 (.leaf 3215) (.leaf 3890)) (.branch 12 (.leaf 3917) (.leaf 3944)))))

@[expose] public def nextBlock0 : Lean.RArray (Fin 4 → Fin 13) := (.branch 6 (.branch 3 (.branch 1 (.leaf ![1, 0, 2, 0]) (.branch 2 (.leaf ![2, 1, 0, 1]) (.leaf ![0, 7, 1, 10]))) (.branch 4 (.leaf ![7, 9, 5, 11]) (.branch 5 (.leaf ![10, 8, 6, 12]) (.leaf ![3, 5, 7, 5])))) (.branch 9 (.branch 7 (.leaf ![4, 6, 10, 6]) (.branch 8 (.leaf ![5, 10, 3, 2]) (.leaf ![11, 12, 9, 4]))) (.branch 11 (.branch 10 (.leaf ![8, 11, 11, 3]) (.leaf ![6, 2, 4, 7])) (.branch 12 (.leaf ![9, 3, 8, 9]) (.leaf ![12, 4, 12, 8])))))

@[expose] public def factorBlock0 : Lean.RArray (Fin 4 → Fin 32) := (.branch 6 (.branch 3 (.branch 1 (.leaf ![31, 5, 0, 10]) (.branch 2 (.leaf ![31, 18, 31, 16]) (.leaf ![0, 22, 31, 19]))) (.branch 4 (.leaf ![31, 2, 5, 6]) (.branch 5 (.leaf ![31, 29, 17, 15]) (.leaf ![10, 30, 13, 29])))) (.branch 9 (.branch 7 (.leaf ![20, 1, 3, 2]) (.branch 8 (.leaf ![12, 14, 31, 27]) (.leaf ![26, 8, 23, 30]))) (.branch 11 (.branch 10 (.leaf ![25, 11, 21, 1]) (.leaf ![4, 14, 31, 19])) (.branch 12 (.leaf ![24, 8, 28, 15]) (.leaf ![7, 11, 9, 6])))))
@[expose] public def codes : Fin 13 → MatrixCode := fun j =>
  ((.leaf codeBlock0) : Lean.RArray (Lean.RArray (MatrixCode))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def detCheck (k : Nat) : Bool := (codeDet (codes ⟨k % 13, Nat.mod_lt _ (by decide)⟩)).val == 1
set_option maxHeartbeats 4000000 in
private theorem detCheck_0 : checkRange detCheck 0 13 = true := by decide +kernel

public theorem det : ∀ j, codeDet (codes j) = 1 := by
  have h := checkRange_fin (by decide : 0 < 13)
    (fun j => (codeDet (codes j)).val == 1) detCheck_0
  intro j
  apply Fin.ext
  exact beq_iff_eq.mp (h j)
@[expose] public def rep (j : Fin 13) : SL := finiteModelEquiv ⟨codes j, det j⟩
@[expose] public def words : Fin 32 → List (Fin 4) := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf []) (.leaf [0])) (.branch 3 (.leaf [2]) (.leaf [1, 1]))) (.branch 6 (.branch 5 (.leaf [3, 3]) (.leaf [0, 1, 0, 1])) (.branch 7 (.leaf [1, 1, 0, 3]) (.leaf [1, 2, 1, 0])))) (.branch 12 (.branch 10 (.branch 9 (.leaf [1, 2, 3, 3]) (.leaf [2, 3, 0, 3])) (.branch 11 (.leaf [3, 2, 3, 2]) (.leaf [0, 1, 1, 0, 3]))) (.branch 14 (.branch 13 (.leaf [0, 1, 1, 1, 0]) (.leaf [0, 1, 1, 2, 3])) (.branch 15 (.leaf [1, 1, 0, 3, 0]) (.leaf [1, 2, 3, 3, 2]))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf [2, 1, 0, 3, 0]) (.leaf [2, 1, 2, 1, 1])) (.branch 19 (.leaf [2, 1, 2, 3, 0]) (.leaf [2, 1, 2, 3, 3]))) (.branch 22 (.branch 21 (.leaf [3, 3, 0, 3, 0]) (.leaf [0, 1, 1, 0, 3, 3])) (.branch 23 (.leaf [1, 1, 0, 1, 0, 3]) (.leaf [1, 1, 1, 1, 0, 3])))) (.branch 28 (.branch 26 (.branch 25 (.leaf [1, 1, 2, 3, 3, 2]) (.leaf [1, 2, 1, 1, 1, 1])) (.branch 27 (.leaf [1, 2, 3, 2, 1, 0]) (.leaf [1, 2, 3, 2, 3, 3]))) (.branch 30 (.branch 29 (.leaf [2, 3, 0, 1, 0, 3]) (.leaf [0, 1, 2, 3, 2, 3, 3])) (.branch 31 (.leaf [0, 3, 3, 2, 3, 0, 3]) (.leaf [1, 1, 1, 1, 0, 3, 0])))))) : Lean.RArray (List (Fin 4))).get j.val
@[expose] public def wordCodes : Fin 32 → MatrixCode := fun j =>
  ((.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 6643) (.leaf 7147)) (.branch 3 (.leaf 6895) (.leaf 2692))) (.branch 6 (.branch 5 (.leaf 4624) (.leaf 6646)) (.branch 7 (.leaf 13457) (.leaf 4786)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 13466) (.leaf 15814)) (.branch 11 (.leaf 6649) (.leaf 13709))) (.branch 14 (.branch 13 (.leaf 2438) (.leaf 2450)) (.branch 15 (.leaf 13223) (.leaf 13700))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 11017) (.leaf 6728)) (.branch 19 (.leaf 8830) (.leaf 13214))) (.branch 22 (.branch 21 (.leaf 6731) (.leaf 9253)) (.branch 23 (.leaf 6652) (.leaf 9011)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 4705) (.leaf 2600)) (.branch 27 (.leaf 2519) (.leaf 6661))) (.branch 30 (.branch 29 (.leaf 15572) (.leaf 7138)) (.branch 31 (.leaf 6904) (.leaf 2432)))))) : Lean.RArray MatrixCode).get j.val
set_option maxHeartbeats 4000000 in
public theorem wordEval : ∀ j, (evalWord (nodeGenerator 49) (words j)).val =
    decodeMatrix (wordCodes j) := by decide +kernel
@[expose] public def next : Fin 13 → Fin 4 → Fin 13 := fun j =>
  ((.leaf nextBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 13))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def factorIndex : Fin 13 → Fin 4 → Fin 32 := fun j =>
  ((.leaf factorBlock0) : Lean.RArray (Lean.RArray (Fin 4 → Fin 32))).get (j.val / 32) |>.get (j.val % 32)
@[expose] public def table : RightCosetTable 4 4 13 where
  base := 0
  next := next
  factor := fun j k => words (factorIndex j k)
@[expose] public def transitionCheck (j : Fin 13) : Bool :=
  matrixEq ((rep j).val * (ambientGenerator 0).val)
    (decodeMatrix (wordCodes (factorIndex j 0)) * (rep (next j 0)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 1).val)
    (decodeMatrix (wordCodes (factorIndex j 1)) * (rep (next j 1)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 2).val)
    (decodeMatrix (wordCodes (factorIndex j 2)) * (rep (next j 2)).val) &&
  matrixEq ((rep j).val * (ambientGenerator 3).val)
    (decodeMatrix (wordCodes (factorIndex j 3)) * (rep (next j 3)).val)
@[expose] public def rowCheck (k : Nat) : Bool := transitionCheck ⟨k % 13, Nat.mod_lt _ (by decide)⟩
set_option maxHeartbeats 4000000 in
private theorem rowCheck_0 : checkRange rowCheck 0 13 = true := by decide +kernel

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
public theorem valid : table.Valid ambientGenerator (nodeGenerator 49) rep := by
  constructor
  · decide +kernel
  · intro j k
    apply Subtype.ext
    change (rep j).val * (ambientGenerator k).val =
      (evalWord (nodeGenerator 49) (words (factorIndex j k))).val * (rep (next j k)).val
    rw [wordEval]
    exact transitions j k
public theorem cover : RightCosetCover (properNode 49) rep := by
  rw [properNode_eq_wordSubgroup]
  exact table.sound ambientGenerator ambientInverse ambientGenerator_inv
    ambient_wordSubgroup_eq_top (nodeGenerator 49) (symmInv (n := (generatorCodes 49).length))
    (nodeGenerator_inv 49) rep valid
end Matrix.PSL3Three.CertifiedEnumeration.Cosets49
