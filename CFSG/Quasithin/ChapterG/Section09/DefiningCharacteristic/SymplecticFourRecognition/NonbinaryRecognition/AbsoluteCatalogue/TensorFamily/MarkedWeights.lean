module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.MarkedWeights.HighestVector

/-!
# Distinguishing the marked symplectic tensor weights

Assume exactly that the standard unipotent fixed space of each concrete tensor
model is the line through its marked highest vector. A genuine intertwining
equivalence sends that vector to a nonzero scalar multiple of the corresponding
vector. The two coroot characters and negative-simple-root fixation tests then
recover both binary labels. Positive labels lie in [1,q-1], so subtracting one
puts their exponents below the order of a generator of the finite-field units.
The separately proved binary-label injectivity recovers the tensor subset.

The fixed-line premise is the sole representation-theoretic input. The parent
`TensorFamily` assembly must discharge it using the full-tensor orbit argument;
this module does not assume or assert a general Steinberg classification.

Sources: GLS3, 2.8.1(a), 2.8.4, 2.8.6(a), 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, G.9.3,
printed pp.356--357 of `refs/quasithin.pdf`. The finite-unit exponent argument
follows `Theory/Representation/SL2/HighestWeightUnique.lean`.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
open Representation

variable {F E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Field E]
variable {n : ℕ} (e : F →+* E)

/-- The precise fixed-line input supplied by the full-tensor orbit argument. -/
def HasHighestFixedLines : Prop :=
  ∀ (S : Finset (Fin (2*n))) (v : (S → Coordinate) → E),
    (∀ g ∈ U, tensorModel e S g v = v) ↔ ∃ z : E, v = z • highestVector S

private theorem equiv_highest (hfixed : HasHighestFixedLines (n := n) e)
    (S T : Finset (Fin (2*n))) (φ : (tensorModel e S).Equiv (tensorModel e T)) :
    ∃ z : E, z ≠ 0 ∧ φ (highestVector S) = z • highestVector T := by
  obtain ⟨z, hz⟩ := (hfixed T (φ (highestVector S))).mp (by
    intro g hg
    have hi : φ (tensorModel e S g (highestVector S)) =
        tensorModel e T g (φ (highestVector S)) :=
      IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (highestVector S)
    rw [highestVector_fixed e S g hg] at hi
    exact hi.symm)
  refine ⟨z, ?_, hz⟩
  intro hz0
  have hφ : φ (highestVector S) = 0 := by simpa [hz0] using hz
  apply highestVector_ne_zero (E := E) S
  apply φ.toLinearEquiv.injective
  simpa using hφ

private theorem equiv_eigenvalue (S T : Finset (Fin (2*n)))
    (φ : (tensorModel e S).Equiv (tensorModel e T)) {z : E} (hz : z ≠ 0)
    (hφ : φ (highestVector S) = z • highestVector T)
    (g : Derived F) (x y : E)
    (hS : tensorModel e S g (highestVector S) = x • highestVector S)
    (hT : tensorModel e T g (highestVector T) = y • highestVector T) : x = y := by
  have h := IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (highestVector S)
  change φ (tensorModel e S g (highestVector S)) = tensorModel e T g (φ (highestVector S)) at h
  rw [hS, map_smul, hφ, map_smul, hT, smul_smul, smul_smul] at h
  have hh := congrFun h (fun _ => .inl 0)
  simp only [Pi.smul_apply, smul_eq_mul, highestVector_top, mul_one] at hh
  exact (mul_right_cancel₀ hz) (by simpa only [mul_comm] using hh)

private theorem equiv_fix_iff (S T : Finset (Fin (2*n)))
    (φ : (tensorModel e S).Equiv (tensorModel e T)) {z : E} (hz : z ≠ 0)
    (hφ : φ (highestVector S) = z • highestVector T) (g : Derived F) :
    tensorModel e S g (highestVector S) = highestVector S ↔
      tensorModel e T g (highestVector T) = highestVector T := by
  rw [← φ.toLinearEquiv.injective.eq_iff]
  change φ (tensorModel e S g (highestVector S)) = φ (highestVector S) ↔ _
  have hi : φ (tensorModel e S g (highestVector S)) =
      tensorModel e T g (φ (highestVector S)) :=
    IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (highestVector S)
  rw [hi, hφ, map_smul]
  exact smul_right_injective _ hz |>.eq_iff

omit [Algebra (ZMod 2) F] in
/-- Finite-torus characters together with a zero marker determine restricted labels. -/
private theorem exponent_eq_of_character_and_zero {a b : ℕ}
    (ha : a < Nat.card F) (hb : b < Nat.card F)
    (hzero : a = 0 ↔ b = 0)
    (hchar : ∀ s : Fˣ, e (s:F)^a = e (s:F)^b) : a = b := by
  by_cases ha0 : a = 0
  · exact ha0.trans (hzero.mp ha0).symm
  have hb0 : b ≠ 0 := mt hzero.mpr ha0
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ho : orderOf s = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_units]
  have he : s ^ a = s ^ b := Units.ext (e.injective (by
    simpa only [Units.val_pow_eq_pow_val, map_pow] using hchar s))
  have he' : s ^ (a-1) = s ^ (b-1) := by
    apply mul_right_cancel (b := s)
    simpa only [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a),
      Nat.sub_add_cancel (by omega : 1 ≤ b)] using he
  have hab := pow_injOn_Iio_orderOf (x := s)
    (show a-1 < orderOf s by rw [ho]; omega)
    (show b-1 < orderOf s by rw [ho]; omega) he'
  omega

/-- Genuine equivalences distinguish all subsets once the marked U-fixed lines are known. -/
theorem tensorModel_equiv_imp_eq_of_fixed_lines
    (hq : 2 < Nat.card F) (hF : Nat.card F = 2^n)
    (hfixed : HasHighestFixedLines (n := n) e)
    (S T : Finset (Fin (2*n)))
    (h : Nonempty ((tensorModel e S).Equiv (tensorModel e T))) : S = T := by
  obtain ⟨φ⟩ := h
  obtain ⟨z, hz, hφ⟩ := equiv_highest e hfixed S T φ
  have hzero (p : Fin 2) : label S p.val = 0 ↔ label T p.val = 0 := by
    rw [← negativeRoot_highest_iff e S hq p, ← negativeRoot_highest_iff e T hq p]
    exact equiv_fix_iff e S T φ hz hφ (negativeRoot hq p)
  have hA : A S = A T := by
    apply exponent_eq_of_character_and_zero e
      (by rw [hF]; exact label_lt S 0) (by rw [hF]; exact label_lt T 0) (hzero 0)
    intro s
    exact equiv_eigenvalue e S T φ hz hφ (corootA hq s) _ _
      (corootA_highest e S hq s) (corootA_highest e T hq s)
  have hB : B S = B T := by
    apply exponent_eq_of_character_and_zero e
      (by rw [hF]; exact label_lt S 1) (by rw [hF]; exact label_lt T 1) (hzero 1)
    intro s
    exact equiv_eigenvalue e S T φ hz hφ (corootB hq s) _ _
      (corootB_highest e S hq s) (corootB_highest e T hq s)
  exact labels_injective (Prod.ext hA hB)

/-- The source parameter range gives the required actual derived/full comparison. -/
theorem tensorModel_distinguish_of_fixed_lines (hn : 2 ≤ n) (hF : Nat.card F = 2^n)
    (hfixed : HasHighestFixedLines (n := n) e) :
    ∀ S T : Finset (Fin (2*n)),
      Nonempty ((tensorModel e S).Equiv (tensorModel e T)) → S = T := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) hn
    omega
  exact tensorModel_equiv_imp_eq_of_fixed_lines e hq hF hfixed

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
