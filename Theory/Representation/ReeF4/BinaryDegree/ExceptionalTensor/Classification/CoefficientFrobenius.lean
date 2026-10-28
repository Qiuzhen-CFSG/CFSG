module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.FrobeniusReduction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius.Factors

/-!
# Coefficient Frobenius shifts the exceptional Ree tensor factors

Genuine coefficient transport of each rational basic algebraic factor gives
its trace after split Frobenius. The identity `ψ² = F` advances its exceptional
exponent by two, and the Ree fixed-point equation reduces this exponent modulo
`2*k+1`. Trace multiplicativity and translation of the cyclic index set give
the exact shift `B(i-2*r)`.

`character_shift` assumes only highest-weight uniqueness for the basic
algebraic factors. Rationality, irreducibility, highest-weight preservation,
and compatibility with the concrete coefficient embedding are proved in the
supporting modules. No character identity or prime-field realization is an
additional premise.

Source: GLS3, Definition 2.8.3, Remark 2.8.4, Corollary 2.8.6(b), and
Remark 2.8.8; Steinberg, *Endomorphisms of Linear Algebraic Groups*, §13.
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F]
noncomputable section

omit [IsAlgClosed F] in
/-- The trace of the recursively ordered tensor product is the product of traces. -/
theorem character_tensorPrefix {G : Type v} [Group G]
    (V : ℕ → FDRep F G) (n : ℕ) (g : G) :
    Representation.character (tensorPrefix V n).ρ g =
      ∏ i ∈ Finset.range n, Representation.character (V i).ρ g := by
  induction n with
  | zero =>
      change LinearMap.trace F F (LinearMap.id) = _
      simp
  | succ n ih =>
      change Representation.character (Representation.tprod (tensorPrefix V n).ρ (V n).ρ) g = _
      rw [Representation.char_tensor, Pi.mul_apply, ih, Finset.prod_range_succ]

/-- Trace of the exceptional tensor, indexed by the odd cyclic group. -/
theorem character_exceptionalTensor {k : ℕ}
    (ι : SplitGroup k →* Variety.Point (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) (g : Model k) :
    Representation.character (exceptionalTensor ι B).ρ g =
      ∏ i : ZMod (2 * k + 1), LinearMap.trace F (B i).Space
        ((B i).action.action (ι ((exceptionalEndomorphism k ^ i.val)
          (toSplitGroup k g))) : Module.End F (B i).Space) := by
  rw [exceptionalTensor, character_tensorPrefix,
    prod_range_cast k (fun i => Representation.character (exceptionalFactor ι B i).ρ g)]
  rfl

/-- Exceptional powers on the Ree fixed points depend only on their odd cyclic index. -/
theorem exceptional_pow_val {k : ℕ} (g : Model k) (a : ℕ) :
    (exceptionalEndomorphism k ^ (a : ZMod (2 * k + 1)).val) (toSplitGroup k g) =
      (exceptionalEndomorphism k ^ a) (toSplitGroup k g) := by
  have hp : Function.Periodic
      (fun j : ℕ => (exceptionalEndomorphism k ^ j) (toSplitGroup k g)) (2 * k + 1) := by
    intro j
    dsimp only
    rw [pow_add, ← reeTwist_eq_pow]
    change (exceptionalEndomorphism k ^ j) (reeTwist k (toSplitGroup k g)) = _
    rw [reeTwist_toSplitGroup]
  rw [ZMod.val_natCast]
  exact hp.map_mod_nat a

/-- Ordinary Frobenius advances exceptional exponents by two, with reduction
modulo the actual Ree fixed-point period. -/
theorem frobenius_exceptional_shift {k : ℕ} (g : Model k)
    (i : ZMod (2 * k + 1)) (r : ℕ) :
    (splitFrobeniusEnd k ^ r)
        ((exceptionalEndomorphism k ^ i.val) (toSplitGroup k g)) =
      (exceptionalEndomorphism k ^ (i + 2 * (r : ZMod (2 * k + 1))).val)
        (toSplitGroup k g) := by
  rw [← exceptionalEndomorphism_sq, ← pow_mul]
  change ((exceptionalEndomorphism k ^ (2 * r)) *
    (exceptionalEndomorphism k ^ i.val)) (toSplitGroup k g) = _
  rw [← pow_add]
  have hi : (i + 2 * (r : ZMod (2 * k + 1))) =
      ((2 * r + i.val : ℕ) : ZMod (2 * k + 1)) := by
    simp [add_comm]
  rw [hi, exceptional_pow_val]

variable [CharP F 2]

/-- The exact coefficient-Frobenius premise for the exceptional tensor
classification. Highest-weight uniqueness is its only representation-theoretic
hypothesis. -/
theorem character_shift {k : ℕ}
    (hunique : ∀ B C : AlgebraicFactor F, ∀ weight : Fin 2 × Fin 2,
      HasBasicHighestWeight B weight → HasBasicHighestWeight C weight →
        AreEquivalentRepresentations B.action C.action)
    (f : CoefficientField k →+* F)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F)
    (hB : ∀ i, (B i).IsExceptionalBasic) (r : ℕ) (g : Model k) :
    Representation.character (exceptionalTensor (splitEmbedding f) B).ρ g ^ (2 ^ r) =
      Representation.character (exceptionalTensor (splitEmbedding f) (shiftFactors B r)).ρ g := by
  rw [character_exceptionalTensor, character_exceptionalTensor, ← Finset.prod_pow]
  have hfactor (i : ZMod (2 * k + 1)) :
      LinearMap.trace F (B i).Space
        ((B i).action.action ((splitEmbedding f)
          ((exceptionalEndomorphism k ^ i.val) (toSplitGroup k g))) :
            Module.End F (B i).Space) ^ (2 ^ r) =
      LinearMap.trace F (B i).Space
        ((B i).action.action ((splitEmbedding f)
          ((exceptionalEndomorphism k ^ (i + 2 * (r : ZMod (2 * k + 1))).val)
            (toSplitGroup k g))) : Module.End F (B i).Space) := by
    rw [trace_splitFrobenius_pow hunique f (B i) (hB i), frobenius_exceptional_shift]
  simp_rw [hfactor]
  let e : Equiv.Perm (ZMod (2 * k + 1)) := Equiv.addRight (2 * (r : ZMod (2 * k + 1)))
  apply Fintype.prod_equiv e
  intro i
  have hBi : shiftFactors B r (e i) = B i := by
    change B (i + 2 * (r : ZMod (2 * k + 1)) - 2 * r) = B i
    rw [add_sub_cancel_right]
  rw [hBi]
  rfl

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
