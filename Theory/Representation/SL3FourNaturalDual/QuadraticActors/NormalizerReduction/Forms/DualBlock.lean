module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Forms.Summands

/-!
# The dual block of a summand-preserving binary SL₃(4) normalizer

Once the natural block is given by an invertible matrix and a field
automorphism, the dual block has the contragredient matrix and the same field
automorphism, up to an independent nonzero field scalar.

The natural–dual pairing is invariant under the component. Removing the
specified matrix and field automorphism from the dual block therefore gives
an additive map commuting with the dual action. The computed additive
centralizer makes this map a field scalar; invertibility of the dual block
excludes zero. No classification of normalizers or automorphisms is assumed.

This is the conditional dual-block calculation for Aschbacher--Smith, combined
manuscript of 1 March 2004, proof of 13.8.20, printed p.955 (PDF p.972).
Construction of the natural block's matrix and field automorphism remains a
separate prerequisite for the full normalizer classification.
-/

public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
open Matrix

private lemma natural_dual_pairing (g : SL) (x y : W) :
    dotProduct (natural g x) (dualCoordinates g y) = dotProduct x y := by
  change dotProduct (g.val.mulVec x) ((g⁻¹).val.transpose.mulVec y) = _
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]
  have hg : (g⁻¹).val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [hg, Matrix.one_mulVec, dotProduct_comm]

/-- The natural semilinear formula determines the dual block up to an independent
nonzero scalar, with the same field automorphism and the contragredient matrix. -/
theorem dualBlock_standard (f : BinaryGL) (hf : f ∈ normalizer)
    (hp : PreservesSummands f) (M : Matrix.GeneralLinearGroup (Fin 3) F)
    (σ : F ≃+* F)
    (hM : ∀ w : W, firstBlock f w = M.val.mulVec (σ ∘ w)) :
    ∃ c : Fˣ, ∀ w : W, secondBlock f w =
      (c : F) • (M⁻¹).val.transpose.mulVec (σ ∘ w) := by
  -- This is the dual block with the prescribed semilinear operator removed.
  let q : W →+ W :=
    { toFun := fun w => σ.symm ∘ M.val.transpose.mulVec (secondBlock f w)
      map_zero' := by
        funext i
        simp
      map_add' := by
        intro u v
        funext i
        simp [Matrix.mulVec_add] }
  have hpair (x y : W) : σ (dotProduct x (q y)) =
      dotProduct (firstBlock f x) (secondBlock f y) := by
    have hq : σ ∘ q y = M.val.transpose.mulVec (secondBlock f y) := by
      funext i
      exact σ.apply_symm_apply _
    calc
      σ (dotProduct x (q y)) = dotProduct (σ ∘ x) (σ ∘ q y) :=
        σ.toRingHom.map_dotProduct x (q y)
      _ = dotProduct (firstBlock f x) (secondBlock f y) := by
        rw [hq, Matrix.dotProduct_transpose_mulVec, dotProduct_comm, hM]
  have hcomm (g : SL) (y : W) :
      q (dualCoordinates g y) = dualCoordinates g (q y) := by
    obtain ⟨h, hn, hd⟩ := normalizer_blocks_intertwine f hf g
    apply dotProduct_eq
    intro x
    obtain ⟨z, rfl⟩ := (natural.apply_bijective g).2 x
    rw [dotProduct_comm (q _), dotProduct_comm (dualCoordinates g (q y))]
    apply σ.injective
    rw [hpair, hn, hd, natural_dual_pairing, natural_dual_pairing, hpair]
  obtain ⟨a, ha⟩ := dual_centralizer_scalar q hcomm
  have hformula (w : W) : secondBlock f w =
      σ a • (M⁻¹).val.transpose.mulVec (σ ∘ w) := by
    have he : M.val.transpose.mulVec (secondBlock f w) = σ a • (σ ∘ w) := by
      funext i
      have hi := congrArg (fun v : W => σ (v i)) (ha w)
      simpa [q, map_mul] using hi
    have hinv : (M⁻¹).val.transpose * M.val.transpose = 1 := by
      rw [← Matrix.transpose_mul, M.mul_inv, Matrix.transpose_one]
    have he' := congrArg (fun v : W => (M⁻¹).val.transpose.mulVec v) he
    simpa only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec,
      Matrix.mulVec_smul] using he'
  have hne : σ a ≠ 0 := by
    intro hz
    have he : secondBlock f (Pi.single 0 1) = secondBlock f 0 := by
      rw [hformula, hz, zero_smul, map_zero]
    have he' := congrFun ((secondBlock_bijective f hp).1 he) 0
    simp at he'
  exact ⟨Units.mk0 (σ a) hne, hformula⟩

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
