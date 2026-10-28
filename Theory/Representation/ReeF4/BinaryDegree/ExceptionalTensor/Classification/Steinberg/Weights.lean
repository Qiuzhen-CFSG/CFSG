module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicWeights

/-!
# Exceptional F₄ weight digits

An exceptional twist reverses the four simple-coroot coefficients and doubles
those at the short roots. Prepending a basic weight therefore sends
`(a₀,a₁,a₂,a₃)` to `(a₃,a₂,b₀+2*a₁,b₁+2*a₀)`.
Taking parity and dividing by two recovers the first basic weight and the tail.
Induction gives a bijection between `n` independent two-bit weights and the
restricted range: long coefficients are below `2^(n/2)` and short coefficients
below `2^((n+1)/2)`. In particular `n = 2*k+1` gives the bounds `2^k` and
`2^(k+1)` used for the concrete Ree group.

This is the arithmetic step in the proof of GLS3, Corollary 2.8.6(b), using
Definition 2.8.1(b) and Remark 2.8.4. The action-theoretic identification of these
coefficients, algebraic irreducibility, and restriction theorems are separate
obligations. There are `2*k+1` independent factors; the repeated subscripts in
the transcription of the corollary are not used.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg

/-- Dominant coefficients at the four numbered simple coroots. -/
abbrev Weight := Fin 4 → ℕ
/-- The independently chosen coefficients at the two short simple roots. -/
abbrev BasicWeight := Fin 2 × Fin 2

/-- Prepending a basic factor to an exceptional twist of the remaining factors. -/
@[expose] def prependWeight (b : BasicWeight) (a : Weight) : Weight :=
  ![a 3, a 2, b.1.val + 2 * a 1, b.2.val + 2 * a 0]

/-- Highest-weight arithmetic for an ordered family of exceptional factors. -/
@[expose] def parameterWeight : (n : ℕ) → (Fin n → BasicWeight) → Weight
  | 0, _ => 0
  | n + 1, b => prependWeight (b 0) (parameterWeight n (fun i => b i.succ))

/-- The source restricted range for the `n`th exceptional endomorphism. -/
@[expose] def InRestrictedRange (n : ℕ) (a : Weight) : Prop :=
  a 0 < 2 ^ (n / 2) ∧ a 1 < 2 ^ (n / 2) ∧
  a 2 < 2 ^ ((n + 1) / 2) ∧ a 3 < 2 ^ ((n + 1) / 2)

theorem prependWeight_injective {b c : BasicWeight} {a d : Weight}
    (h : prependWeight b a = prependWeight c d) : b = c ∧ a = d := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [prependWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3
  have hb1 := b.1.isLt
  have hb2 := b.2.isLt
  have hc1 := c.1.isLt
  have hc2 := c.2.isLt
  constructor
  · apply Prod.ext <;> apply Fin.ext <;> omega
  · funext i
    fin_cases i <;> simp_all <;> omega

theorem parameterWeight_injective (n : ℕ) : Function.Injective (parameterWeight n) := by
  induction n with
  | zero => intro b c _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro b c h
    obtain ⟨hhead, htail⟩ := prependWeight_injective h
    have ht := ih htail
    funext i
    refine Fin.cases hhead (fun j => congrFun ht j) i

theorem parameterWeight_mem_range (n : ℕ) (b : Fin n → BasicWeight) :
    InRestrictedRange n (parameterWeight n b) := by
  induction n with
  | zero => simp [InRestrictedRange, parameterWeight]
  | succ n ih =>
    have h := ih (fun i => b i.succ)
    have hn : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
    have ha := (b 0).1.isLt
    have hb := (b 0).2.isLt
    simp only [InRestrictedRange, parameterWeight, prependWeight,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h ⊢
    rw [hn, pow_succ]
    omega

theorem exists_parameterWeight (n : ℕ) (a : Weight) (ha : InRestrictedRange n a) :
    ∃ b, parameterWeight n b = a := by
  induction n generalizing a with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simp only [InRestrictedRange, Nat.zero_add, Nat.div_eq_of_lt (by decide : 1 < 2),
      pow_zero] at ha
    funext i
    fin_cases i <;> simp [parameterWeight] <;> omega
  | succ n ih =>
    let c : BasicWeight := (⟨a 2 % 2, Nat.mod_lt _ (by decide)⟩,
      ⟨a 3 % 2, Nat.mod_lt _ (by decide)⟩)
    let d : Weight := ![a 3 / 2, a 2 / 2, a 1, a 0]
    have hd : InRestrictedRange n d := by
      have hn : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      simp only [InRestrictedRange] at ha
      rw [hn, pow_succ] at ha
      simp only [InRestrictedRange, d, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      omega
    obtain ⟨b, hb⟩ := ih d hd
    refine ⟨Fin.cases c b, ?_⟩
    change prependWeight c (parameterWeight n b) = a
    rw [hb]
    funext i
    fin_cases i <;> simp [prependWeight, c, d] <;> omega


/-- Pullback of coroot coefficients under the exceptional root formula. -/
@[expose] def exceptionalWeight (a : Weight) : Weight := ![a 3, a 2, 2 * a 1, 2 * a 0]

theorem prependWeight_eq (b : BasicWeight) (a : Weight) :
    prependWeight b a = basicCoefficient b + exceptionalWeight a := by
  funext i
  fin_cases i <;> simp [prependWeight, basicCoefficient, exceptionalWeight]

theorem restrictedRange_odd (k : ℕ) (a : Weight) :
    InRestrictedRange (2 * k + 1) a ↔
      a 0 < 2 ^ k ∧ a 1 < 2 ^ k ∧ a 2 < 2 ^ (k + 1) ∧ a 3 < 2 ^ (k + 1) := by
  have h₀ : (2 * k + 1) / 2 = k := by omega
  have h₁ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [InRestrictedRange, h₀, h₁]

/-- The coefficient vector of the cyclically indexed exceptional tensor. -/
@[expose] def tensorWeight {k : ℕ} (b : ZMod (2 * k + 1) → BasicWeight) : Weight :=
  parameterWeight (2 * k + 1) (fun i => b (i.val : ZMod (2 * k + 1)))

theorem tensorWeight_injective (k : ℕ) : Function.Injective (tensorWeight (k := k)) := by
  intro b c h
  have hh := parameterWeight_injective (2 * k + 1) h
  funext i
  have hi := congrFun hh ⟨i.val, i.val_lt⟩
  simpa using hi

theorem tensorWeight_mem_range {k : ℕ} (b : ZMod (2 * k + 1) → BasicWeight) :
    InRestrictedRange (2 * k + 1) (tensorWeight b) :=
  parameterWeight_mem_range _ _

theorem exists_tensorWeight {k : ℕ} (a : Weight) (ha : InRestrictedRange (2 * k + 1) a) :
    ∃ b : ZMod (2 * k + 1) → BasicWeight, tensorWeight b = a := by
  obtain ⟨c, hc⟩ := exists_parameterWeight (2 * k + 1) a ha
  refine ⟨fun i => c ⟨i.val, i.val_lt⟩, ?_⟩
  unfold tensorWeight
  convert hc using 1
  congr 1
  funext i
  congr 1
  exact Fin.ext (ZMod.val_natCast_of_lt i.isLt)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
