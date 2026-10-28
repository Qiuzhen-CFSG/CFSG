module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.CubicCoefficient
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The cubic basis of the actual triality source field

The source extension and its Frobenius-fixed subfield are the fields carried by
the same `ScalarMarking` equivalence. Their cardinalities give extension degree
three over the actual fixed field. Thus every element outside that fixed field
is a primitive generator, and its first three powers form the source basis.
This derives the expansion used in Fong--Seitz (9.27) from the actual field
marking, including `q = 2`.

Source: Fong--Seitz II (9.22)--(9.26), with the compatible field marking used
throughout II 9B.
-/

@[expose] public noncomputable section
open Module
open Triality.Standard Triality.Standard.RootPresentationRecognition

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource

variable {F : Type*} [Field F] [Finite F]
  {n : ℕ} {hn : 0 < n} {σ : F ≃+* F}

local notation "K" => ScalarMarking.SourceFixed (σ := σ)

omit [Finite F] in
@[simp] theorem scalarMarking_sourceExtension_card
    (e : ScalarMarking (binaryParameters n hn) σ) :
    Nat.card F = (2 ^ n) ^ 3 := by
  rw [Nat.card_congr e.extension.toEquiv, card_extensionField]
  simp only [binaryParameters_q]

omit [Finite F] in
@[simp] theorem scalarMarking_sourceFixed_card
    (e : ScalarMarking (binaryParameters n hn) σ) :
    Nat.card K = 2 ^ n := by
  rw [Nat.card_congr e.fixed.toEquiv, card_fixedField]
  simp only [binaryParameters_q]

/-- The original source field has degree three over its actual fixed field. -/
theorem scalarMarking_sourceFixed_finrank
    (e : ScalarMarking (binaryParameters n hn) σ) : Module.finrank K F = 3 := by
  apply Nat.pow_right_injective (show 1 < 2 ^ n from (binaryParameters n hn).q_ge_two)
  change (2 ^ n) ^ Module.finrank K F = (2 ^ n) ^ 3
  have hc : Nat.card F = Nat.card K ^ Module.finrank K F := Module.natCard_eq_pow_finrank
  simpa only [scalarMarking_sourceExtension_card e, scalarMarking_sourceFixed_card e] using hc.symm

/-- A scalar outside the actual fixed field generates the full cubic source field. -/
private theorem scalarMarking_adjoin_top
    (e : ScalarMarking (binaryParameters n hn) σ) (θ : F) (hθ : σ θ ≠ θ) :
    IntermediateField.adjoin K {θ} = ⊤ := by
  have hprime : Nat.Prime (Module.finrank K F) := by
    rw [scalarMarking_sourceFixed_finrank e]
    norm_num
  let _ := IntermediateField.isSimpleOrder_of_finrank_prime K F hprime
  rcases eq_bot_or_eq_top (IntermediateField.adjoin K {θ}) with h | h
  · have hm : θ ∈ (⊥ : IntermediateField K F) :=
      h ▸ IntermediateField.subset_adjoin K {θ} (by simp)
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp hm
    exact (hθ (by rw [← hx]; exact x.property)).elim
  · exact h

/-- Every element is a linear combination of `1`, `θ`, and `θ²` when
`θ` is not fixed by the source Frobenius. This is the basis used in the
three-coordinate module calculation (9.27). -/
theorem scalarMarking_spans_of_nonfixed
    (e : ScalarMarking (binaryParameters n hn) σ) (θ : F) (hθ : σ θ ≠ θ) (x : F) :
    ∃ b₀ b₁ b₂ : K, x = b₀.val + b₁.val * θ + b₂.val * θ^2 := by
  let pb : PowerBasis K F :=
    (IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral θ)).map
      ((IntermediateField.equivOfEq (scalarMarking_adjoin_top e θ hθ)).trans
        IntermediateField.topEquiv)
  have hdim : pb.dim = 3 := by
    rw [← PowerBasis.finrank pb, scalarMarking_sourceFixed_finrank e]
  let b : Basis (Fin 3) K F := pb.basis.reindex (finCongr hdim)
  have hgen : pb.gen = θ := rfl
  have hb (i : Fin 3) : b i = θ ^ i.val := by
    simp [b, hgen]
  refine ⟨b.repr x 0, b.repr x 1, b.repr x 2, ?_⟩
  have hx := b.sum_repr x
  rw [Fin.sum_univ_three] at hx
  have hcoe (k : K) : algebraMap K F k = k.val := rfl
  simpa [hb, Algebra.smul_def, hcoe] using hx.symm

/-- The compatible source Frobenius is nontrivial: the fixed field has `q`
elements while the source field has `q³` elements. -/
theorem scalarMarking_exists_nonfixed
    (e : ScalarMarking (binaryParameters n hn) σ) : ∃ θ : F, σ θ ≠ θ := by
  by_contra h
  push Not at h
  have hall : ∀ x : F, σ x = x := h
  let f : F → K := fun x => ⟨x, hall x⟩
  have hinj : Function.Injective f := fun x y hxy => congrArg Subtype.val hxy
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [scalarMarking_sourceExtension_card e, scalarMarking_sourceFixed_card e] at hcard
  exact (not_lt_of_ge hcard)
    (lt_self_pow₀ (by exact (binaryParameters n hn).q_ge_two) (by decide : 1 < 3))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
