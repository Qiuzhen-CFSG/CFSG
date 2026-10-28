module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Labels
/-!
# Point-fixing words for three enlarged cubic representatives

The permutations use the binary labels of the actual six-coordinate space.
For each displayed cubic, a ten-letter word in it and the column cubic fixes
the marked point. A square or cube of this word has order seven. All finite
identities are checked by the kernel on 64 labels.

These are representative witnesses, not a classification of rotating cubics.
The final theorem excludes these representatives in any subgroup whose point
stabilizer has only element orders dividing 4608.

Source: Aschbacher–Smith, the point-stabilizer contradiction in 14.4.4,
printed p.1007, enlarged to retain the possible central plane.
-/

@[expose] public section
namespace EnlargedSwappingTable
def p : Equiv.Perm (Fin 64) := {
  toFun := ![0,2,3,1,8,10,11,9,12,14,15,13,4,6,7,5,16,18,19,17,24,26,27,25,28,30,31,29,20,22,23,21,32,34,35,33,40,42,43,41,44,46,47,45,36,38,39,37,48,50,51,49,56,58,59,57,60,62,63,61,52,54,55,53]
  invFun := ![0,3,1,2,12,15,13,14,4,7,5,6,8,11,9,10,16,19,17,18,28,31,29,30,20,23,21,22,24,27,25,26,32,35,33,34,44,47,45,46,36,39,37,38,40,43,41,42,48,51,49,50,60,63,61,62,52,55,53,54,56,59,57,58]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }
def q1 : Equiv.Perm (Fin 64) := {
  toFun := ![0,8,2,10,20,28,22,30,11,3,9,1,31,23,29,21,34,42,32,40,54,62,52,60,41,33,43,35,61,53,63,55,48,56,50,58,36,44,38,46,59,51,57,49,47,39,45,37,18,26,16,24,6,14,4,12,25,17,27,19,13,5,15,7]
  invFun := ![0,11,2,9,54,61,52,63,1,10,3,8,55,60,53,62,50,57,48,59,4,15,6,13,51,56,49,58,5,14,7,12,18,25,16,27,36,47,38,45,19,24,17,26,37,46,39,44,32,43,34,41,22,29,20,31,33,42,35,40,23,28,21,30]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }
def q2 : Equiv.Perm (Fin 64) := {
  toFun := ![0,8,2,10,22,30,20,28,11,3,9,1,29,21,31,23,32,40,34,42,54,62,52,60,43,35,41,33,61,53,63,55,50,58,48,56,36,44,38,46,57,49,59,51,47,39,45,37,18,26,16,24,4,12,6,14,25,17,27,19,15,7,13,5]
  invFun := ![0,11,2,9,52,63,54,61,1,10,3,8,53,62,55,60,50,57,48,59,6,13,4,15,51,56,49,58,7,12,5,14,16,27,18,25,36,47,38,45,17,26,19,24,37,46,39,44,34,41,32,43,22,29,20,31,35,40,33,42,23,28,21,30]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }
def q3 : Equiv.Perm (Fin 64) := {
  toFun := ![0,8,2,10,22,30,20,28,11,3,9,1,29,21,31,23,34,42,32,40,52,60,54,62,41,33,43,35,63,55,61,53,50,58,48,56,36,44,38,46,57,49,59,51,47,39,45,37,16,24,18,26,6,14,4,12,27,19,25,17,13,5,15,7]
  invFun := ![0,11,2,9,54,61,52,63,1,10,3,8,55,60,53,62,48,59,50,57,6,13,4,15,49,58,51,56,7,12,5,14,18,25,16,27,36,47,38,45,19,24,17,26,37,46,39,44,34,41,32,43,20,31,22,29,35,40,33,42,21,30,23,28]
  left_inv := by decide +kernel
  right_inv := by decide +kernel }
def w1 : Equiv.Perm (Fin 64) := p*q1*p⁻¹*q1⁻¹*p*q1*p⁻¹*q1⁻¹*p*q1⁻¹
def w2 : Equiv.Perm (Fin 64) := p*q2*p*q2⁻¹*p*q2*p⁻¹*q2⁻¹*p*q2⁻¹
def w3 : Equiv.Perm (Fin 64) := p*q3*p*q3*p*q3⁻¹*p*q3⁻¹*p⁻¹*q3
theorem w1_fix : w1 2=2 := by decide +kernel
theorem w2_fix : w2 2=2 := by decide +kernel
theorem w3_fix : w3 2=2 := by decide +kernel
theorem w1_seven : orderOf (w1^2)=7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Equiv.ext
    decide +kernel
  · intro h
    exact (by decide +kernel : (w1^2) 1 ≠ 1) (Equiv.congr_fun h 1)
theorem w2_seven : orderOf (w2^2)=7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Equiv.ext
    decide +kernel
  · intro h
    exact (by decide +kernel : (w2^2) 1 ≠ 1) (Equiv.congr_fun h 1)
theorem w3_seven : orderOf (w3^3)=7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Equiv.ext
    decide +kernel
  · intro h
    exact (by decide +kernel : (w3^3) 1 ≠ 1) (Equiv.congr_fun h 1)
private theorem fixed_pow {X : Type*} (f : Equiv.Perm X) (x : X) (h : f x = x) :
    ∀ n : ℕ, (f^n) x = x
  | 0 => rfl
  | n+1 => by rw [pow_succ,Equiv.Perm.mul_apply,h,fixed_pow f x h n]
theorem witness_1 : ∃ w ∈ Subgroup.closure ({p,q1} : Set (Equiv.Perm (Fin 64))),
    w 2 = 2 ∧ orderOf w = 7 := by
  let K := Subgroup.closure ({p,q1} : Set (Equiv.Perm (Fin 64)))
  have hp : p ∈ K := Subgroup.subset_closure (by simp)
  have hq : q1 ∈ K := Subgroup.subset_closure (by simp)
  have hw : w1 ∈ K := by
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hp hq) (K.inv_mem hp)) (K.inv_mem hq)) hp) hq) (K.inv_mem hp)) (K.inv_mem hq)) hp) (K.inv_mem hq))
  refine ⟨w1^2,K.pow_mem hw _,?_,w1_seven⟩
  · exact fixed_pow w1 2 w1_fix 2
theorem witness_2 : ∃ w ∈ Subgroup.closure ({p,q2} : Set (Equiv.Perm (Fin 64))),
    w 2 = 2 ∧ orderOf w = 7 := by
  let K := Subgroup.closure ({p,q2} : Set (Equiv.Perm (Fin 64)))
  have hp : p ∈ K := Subgroup.subset_closure (by simp)
  have hq : q2 ∈ K := Subgroup.subset_closure (by simp)
  have hw : w2 ∈ K := by
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hp hq) hp) (K.inv_mem hq)) hp) hq) (K.inv_mem hp)) (K.inv_mem hq)) hp) (K.inv_mem hq))
  refine ⟨w2^2,K.pow_mem hw _,?_,w2_seven⟩
  · exact fixed_pow w2 2 w2_fix 2
theorem witness_3 : ∃ w ∈ Subgroup.closure ({p,q3} : Set (Equiv.Perm (Fin 64))),
    w 2 = 2 ∧ orderOf w = 7 := by
  let K := Subgroup.closure ({p,q3} : Set (Equiv.Perm (Fin 64)))
  have hp : p ∈ K := Subgroup.subset_closure (by simp)
  have hq : q3 ∈ K := Subgroup.subset_closure (by simp)
  have hw : w3 ∈ K := by
    exact (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hp hq) hp) hq) hp) (K.inv_mem hq)) hp) (K.inv_mem hq)) (K.inv_mem hp)) hq)
  refine ⟨w3^3,K.pow_mem hw _,?_,w3_seven⟩
  · exact fixed_pow w3 2 w3_fix 3
theorem parabolic_cubic_label :
    BinarySixSplitPair.permAction (BinarySixSplitPair.extend BinaryFourSplitPair.columnCubic) = p := by
  apply Equiv.ext
  decide +kernel

/-- Each representative contradicts the required stabilizer order bound. -/
theorem no_representative (J : Subgroup (Equiv.Perm (Fin 64))) (hp : p ∈ J)
    (hbound : ∀ w ∈ J, w 2=2 → orderOf w ∣ 4608) :
    q1 ∉ J ∧ q2 ∉ J ∧ q3 ∉ J := by
  have impossible (q : Equiv.Perm (Fin 64)) (hq : q ∈ J)
      (hw : ∃ w ∈ Subgroup.closure ({p,q} : Set (Equiv.Perm (Fin 64))),
        w 2=2 ∧ orderOf w=7) : False := by
    obtain ⟨w,hw,hfix,hseven⟩ := hw
    have hle : Subgroup.closure ({p,q} : Set (Equiv.Perm (Fin 64))) ≤ J := by
      apply (Subgroup.closure_le J).mpr
      intro x hx
      rcases (show x=p ∨ x=q from by simpa using hx) with rfl | rfl
      · exact hp
      · exact hq
    have hd := hbound w (hle hw) hfix
    rw [hseven] at hd
    exact (by decide : ¬ 7 ∣ 4608) hd
  exact ⟨fun h => impossible q1 h witness_1,
    fun h => impossible q2 h witness_2,fun h => impossible q3 h witness_3⟩
end EnlargedSwappingTable
