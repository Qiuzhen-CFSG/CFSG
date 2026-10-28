module
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Coordinates
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
/-!
# Literal split coordinates for the outer Ree center calculation

The 24 split-root factors are ordered as in the existing positive block layout.
Injectivity is inherited from the proved split-coordinate theorem. Expanding
`positiveWord` retains both factors of every central B₂ word: its mixed-root
coordinate is `a * halfFrobenius m a + halfFrobenius m c`, and its high-root
coordinate is `c`. The small group identities below support checked collection.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
Application: the root-center assertion used on printed p.927 of
`refs/quasithin.pdf`, with the family conventions of A.2.3–4.
-/
@[expose] public section
noncomputable section
namespace ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
open Parabolics Parabolics.RadicalCoordinates Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations MatrixRelations.LongCommutators
open Theory.AlgebraicGroup.StandardRootSystem

def splitWord (m : ℕ) (v : Fin 24 → CoefficientField m) : SplitGroup m :=
  X m 22 (v 22) * (X m 23 (v 23) * (X m 4 (v 4) * (X m 5 (v 5) * (X m 16 (v 16) * (X m 17 (v 17) * (X m 10 (v 10) * (X m 11 (v 11) * (X m 0 (v 0) * (X m 1 (v 1) * (X m 2 (v 2) * (X m 3 (v 3) * (X m 12 (v 12) * (X m 13 (v 13) * (X m 14 (v 14) * (X m 15 (v 15) * (X m 18 (v 18) * (X m 19 (v 19) * (X m 20 (v 20) * (X m 21 (v 21) * (X m 6 (v 6) * (X m 7 (v 7) * (X m 8 (v 8) * (X m 9 (v 9) * (1))))))))))))))))))))))))

private def blocks (m : ℕ) (v : Fin 24 → CoefficientField m) : BlockParameters m .positive :=
  (![![v 22, v 23], ![v 4, v 5], ![v 16, v 17], ![v 10, v 11]],
   ![![v 0, v 1, v 2, v 3], ![v 12, v 13, v 14, v 15], ![v 18, v 19, v 20, v 21], ![v 6, v 7, v 8, v 9]])

private theorem splitWord_blocks (m : ℕ) (v : Fin 24 → CoefficientField m) :
    splitWord m v = positiveRootWordLayout.blocks.blockWord m (blocks m v) := by
  unfold RootBlocks.blockWord
  change splitWord m v =
    (rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((0 : Fin 4), 0))).val (v 22) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((0 : Fin 4), 1))).val (v 23)) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((1 : Fin 4), 0))).val (v 4) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((1 : Fin 4), 1))).val (v 5)) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((2 : Fin 4), 0))).val (v 16) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((2 : Fin 4), 1))).val (v 17)) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((3 : Fin 4), 0))).val (v 10) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inl ((3 : Fin 4), 1))).val (v 11)) * (1)))) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((0 : Fin 4), 0))).val (v 0) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((0 : Fin 4), 1))).val (v 1) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((0 : Fin 4), 2))).val (v 2) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((0 : Fin 4), 3))).val (v 3)) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((1 : Fin 4), 0))).val (v 12) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((1 : Fin 4), 1))).val (v 13) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((1 : Fin 4), 2))).val (v 14) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((1 : Fin 4), 3))).val (v 15)) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((2 : Fin 4), 0))).val (v 18) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((2 : Fin 4), 1))).val (v 19) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((2 : Fin 4), 2))).val (v 20) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((2 : Fin 4), 3))).val (v 21)) * ((rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((3 : Fin 4), 0))).val (v 6) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((3 : Fin 4), 1))).val (v 7) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((3 : Fin 4), 2))).val (v 8) * rootGeneratorInGroup m (positiveRootWordLayout.blocks.roots (.inr ((3 : Fin 4), 3))).val (v 9)) * (1)))))
  simp only [splitWord, mul_assoc, one_mul]
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_long (0 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_short (0 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_long (1 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_short (1 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_long (2 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_short (2 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_long (3 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.pair_short (3 : Fin 4), positive_pair_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_long (0 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_short (0 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_mixed (0 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_high (0 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_long (1 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_short (1 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_mixed (1 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_high (1 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_long (2 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_short (2 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_mixed (2 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_high (2 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_long (3 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_short (3 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_mixed (3 : Fin 4), positive_quartet_indices]
    rfl
  apply congrArg₂ (· * ·)
  · rw [positiveRootWordLayout.quartet_high (3 : Fin 4), positive_quartet_indices]
    rfl
  rfl

theorem splitWord_injective (m : ℕ) : Function.Injective (splitWord m) := by
  intro v w h
  have hb : blocks m v = blocks m w := by
    apply positiveRootWordLayout.blocks.blockWord_injective m (wordInSubgroup_bijective m _)
    simpa only [← splitWord_blocks] using h
  funext i
  fin_cases i
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (0 : Fin 4) (0 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (0 : Fin 4) (1 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (0 : Fin 4) (2 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (0 : Fin 4) (3 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (1 : Fin 4) (0 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (1 : Fin 4) (1 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (3 : Fin 4) (0 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (3 : Fin 4) (1 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (3 : Fin 4) (2 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (3 : Fin 4) (3 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (3 : Fin 4) (0 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (3 : Fin 4) (1 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (1 : Fin 4) (0 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (1 : Fin 4) (1 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (1 : Fin 4) (2 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (1 : Fin 4) (3 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (2 : Fin 4) (0 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (2 : Fin 4) (1 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (2 : Fin 4) (0 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (2 : Fin 4) (1 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (2 : Fin 4) (2 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.2 (2 : Fin 4) (3 : Fin 4)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (0 : Fin 4) (0 : Fin 2)) hb
  · exact congrArg (fun b : BlockParameters m .positive => b.1 (0 : Fin 4) (1 : Fin 2)) hb

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]

private theorem word_0 (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = X m 0 t * X m 1 (halfFrobenius m t) * X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem central_0 (m : ℕ) (t : CoefficientField m) :
    centralWord m 0 t = X m 3 t * X m 2 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

theorem word_1 (m : ℕ) (t : CoefficientField m) :
    rootWord m 1 t = X m 4 t * X m 5 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 4 t * X m 5 (halfFrobenius m t)) * 1 = _
  exact mul_one _

private theorem word_2 (m : ℕ) (t : CoefficientField m) :
    rootWord m 2 t = X m 6 t * X m 7 (halfFrobenius m t) * X m 8 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem central_2 (m : ℕ) (t : CoefficientField m) :
    centralWord m 2 t = X m 9 t * X m 8 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

theorem word_3 (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t = X m 10 t * X m 11 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 10 t * X m 11 (halfFrobenius m t)) * 1 = _
  exact mul_one _

private theorem word_4 (m : ℕ) (t : CoefficientField m) :
    rootWord m 4 t = X m 12 t * X m 13 (halfFrobenius m t) * X m 14 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem central_4 (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

private theorem word_5 (m : ℕ) (t : CoefficientField m) :
    rootWord m 5 t = X m 16 t * X m 17 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 16 t * X m 17 (halfFrobenius m t)) * 1 = _
  exact mul_one _

theorem word_6 (m : ℕ) (t : CoefficientField m) :
    rootWord m 6 t = X m 18 t * X m 19 (halfFrobenius m t) * X m 20 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem central_6 (m : ℕ) (t : CoefficientField m) :
    centralWord m 6 t = X m 21 t * X m 20 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

private theorem word_7 (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = X m 22 t * X m 23 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change (X m 22 t * X m 23 (halfFrobenius m t)) * 1 = _
  exact mul_one _

def parameters (m : ℕ) (p : PositiveParameters m) : Fin 24 → CoefficientField m :=
  ![p.main 0, halfFrobenius m (p.main 0), p.main 0 * halfFrobenius m (p.main 0) + halfFrobenius m (p.central 0), p.central 0, p.pair 1, halfFrobenius m (p.pair 1), p.main 3, halfFrobenius m (p.main 3), p.main 3 * halfFrobenius m (p.main 3) + halfFrobenius m (p.central 3), p.central 3, p.pair 3, halfFrobenius m (p.pair 3), p.main 1, halfFrobenius m (p.main 1), p.main 1 * halfFrobenius m (p.main 1) + halfFrobenius m (p.central 1), p.central 1, p.pair 2, halfFrobenius m (p.pair 2), p.main 2, halfFrobenius m (p.main 2), p.main 2 * halfFrobenius m (p.main 2) + halfFrobenius m (p.central 2), p.central 2, p.pair 0, halfFrobenius m (p.pair 0)]

theorem add_suffix (m : ℕ) (i : Fin 24) (a b : CoefficientField m) (z : SplitGroup m) :
    X m i a * (X m i b * z) = X m i (a+b) * z := by rw [← mul_assoc, xa]

theorem positiveWord_split (m : ℕ) (p : PositiveParameters m) :
    positiveWord m p = splitWord m (parameters m p) := by
  rw [positiveWord, positive_pair_indices, positive_quartet_indices]
  change (rootWord m 7 (p.pair 0) * (rootWord m 1 (p.pair 1) * (rootWord m 5 (p.pair 2) * (rootWord m 3 (p.pair 3) * (1))))) * ((rootWord m 0 (p.main 0) * centralWord m 0 (p.central 0)) * ((rootWord m 4 (p.main 1) * centralWord m 4 (p.central 1)) * ((rootWord m 6 (p.main 2) * centralWord m 6 (p.central 2)) * ((rootWord m 2 (p.main 3) * centralWord m 2 (p.central 3)) * (1))))) = _
  simp only [word_0, word_1, word_2, word_3, word_4, word_5, word_6, word_7,
    central_0, central_2, central_4, central_6, mul_assoc, one_mul]
  change _ = X m 22 (parameters m p 22) * (X m 23 (parameters m p 23) * (X m 4 (parameters m p 4) * (X m 5 (parameters m p 5) * (X m 16 (parameters m p 16) * (X m 17 (parameters m p 17) * (X m 10 (parameters m p 10) * (X m 11 (parameters m p 11) * (X m 0 (parameters m p 0) * (X m 1 (parameters m p 1) * (X m 2 (parameters m p 2) * (X m 3 (parameters m p 3) * (X m 12 (parameters m p 12) * (X m 13 (parameters m p 13) * (X m 14 (parameters m p 14) * (X m 15 (parameters m p 15) * (X m 18 (parameters m p 18) * (X m 19 (parameters m p 19) * (X m 20 (parameters m p 20) * (X m 21 (parameters m p 21) * (X m 6 (parameters m p 6) * (X m 7 (parameters m p 7) * (X m 8 (parameters m p 8) * (X m 9 (parameters m p 9) * (1))))))))))))))))))))))))
  rw [(xc m 3 2 (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) (p.central 0)
    (halfFrobenius m (p.central 0))).left_comm, add_suffix]
  rw [(xc m 15 14 (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) (p.central 1)
    (halfFrobenius m (p.central 1))).left_comm, add_suffix]
  rw [(xc m 21 20 (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) (p.central 2)
    (halfFrobenius m (p.central 2))).left_comm, add_suffix]
  rw [(xc m 9 8 (by norm_num [V, dot, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]) (p.central 3)
    (halfFrobenius m (p.central 3))).left_comm, add_suffix]

  rfl

theorem swap_suffix {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) (d : G) : a * (b * d) = b * (a * (c * d)) := by
  simpa only [mul_assoc] using congrArg (fun z => z * d) h

theorem swap_suffix_two {G : Type*} [Group G] {a b c d : G}
    (h : a * b = b * a * c * d) (e : G) :
    a * (b * e) = b * (a * (c * (d * e))) := by
  simpa only [mul_assoc] using congrArg (fun z => z * e) h

theorem reverse_two {G : Type*} [Group G] {a b c d : G}
    (h : b * a = a * b * c * d) (hc : c * c = 1) (hd : d * d = 1)
    (hcd : Commute c d) : a * b = b * a * c * d := by
  have hcc : (c * d) * (c * d) = 1 := by
    rw [hcd.symm.mul_mul_mul_comm, hc, hd, one_mul]
  calc
    a * b = (a * b * (c * d)) * (c * d) := by rw [mul_assoc, hcc, mul_one]
    _ = b * a * c * d := by
      simpa only [mul_assoc] using congrArg (fun z => z * (c * d)) h.symm

end ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
