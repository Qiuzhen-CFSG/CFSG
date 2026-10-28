module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus.DiagonalData

/-!
# Coroot words on the actual Geck lattice

The six-transvection word n(t)n(-1) in SL₂ is diag(t,t⁻¹). Its proved
rank-one representation fixes the Cartan vectors, has weights ±2 on the
exceptional roots, weights ±1 on the eight natural root strings, and weight
zero on the six orthogonal roots. Integral coordinate calculations identify
these with the original D₄ Cartan pairings, proving the coroot diagonal on
the entire Geck lattice in characteristic two, including the smallest field.

Source: GLS3 1.12.1 and §§2.3–2.4 (`refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`). The code's word n(t)n(-1) is preserved;
GLS3 uses the opposite order n(1)⁻¹n(t), so the diagonal is computed directly.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ConcreteBruhat.TorusCoordinates
open Parabolics Parabolics.RankOneMatrices
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

private def flatWeight : FlatIndex → ℤ
  | .inl _ => 0
  | .inr r => if r = 0 then 2 else if r = 1 then -2 else
      if r < 18 then (if r.val % 2 = 0 then 1 else -1) else 0

private lemma ordered_weight (i : Fin 4) (r : Fin 24) :
    (∑ j : Fin 4, orderedCoords i r j * orderedCoords i 0 j) = flatWeight (.inr r) := by
  revert i r
  decide +kernel

private lemma corootWeight_flat (i : Fin 4) (r : FlatIndex) :
    corootWeight i (flatEquiv i r) = flatWeight r := by
  rcases r with r | r
  · rfl
  · change (typeDRootPairing 2).pairingIn ℤ (orderedRoot i r)
      (typeDSimpleRootIndex 2 i) = _
    apply FaithfulSMul.algebraMap_injective ℤ ℝ
    rw [RootPairing.algebraMap_pairingIn, ← orderedRoot_zero i, typeDRootPairing_pairing]
    change (∑ j : Fin 4, _ * _) = _
    simp only [← typeDRootPairing_root_val, orderedCoords_spec]
    change (∑ j : Fin 4, (orderedCoords i 0 j : ℝ) * (orderedCoords i r j : ℝ)) =
      (flatWeight (.inr r) : ℝ)
    simpa only [Int.cast_sum, Int.cast_mul, mul_comm] using
      congrArg (fun z : ℤ => (z : ℝ)) (ordered_weight i r)

private def blockWeight : BlockIndex → ℤ
  | .inl (.inl _) => 0
  | .inl (.inr r) => if r = 0 then 2 else -2
  | .inr (.inl (r, _)) => if r = 0 then 1 else -1
  | .inr (.inr _) => 0

private lemma flatWeight_block (r : BlockIndex) :
    flatWeight (blockToFlat r) = blockWeight r := by
  revert r
  decide +kernel

private lemma corootWeight_block (i : Fin 4) (r : BlockIndex) :
    corootWeight i (latticeEquiv i r) = blockWeight r := by
  rw [← flatEquiv_blockToFlat, corootWeight_flat, flatWeight_block]

private abbrev upper {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev lower {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t
private def rankOneWeyl {F : Type*} [Field F] (t : F) : SL(2, F) :=
  upper t * lower (-t⁻¹) * upper t
private def rankOneTorus {F : Type*} [Field F] (t : Fˣ) : SL(2, F) :=
  rankOneWeyl t.val * rankOneWeyl (-1)

private lemma rankOneTorus_val {F : Type*} [Field F] (t : Fˣ) :
    (rankOneTorus t).val = Matrix.diagonal ![t.val, t.val⁻¹] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [rankOneTorus, rankOneWeyl, upper, lower, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, t.ne_zero]

private lemma blockMatrix_torus {F : Type*} [Field F] (i : Fin 4) (t : Fˣ) :
    blockMatrix i (rankOneTorus t) = Matrix.diagonal (fun r => t.val ^ blockWeight r) := by
  ext r s
  rcases r with (r | r) | (⟨r, k⟩ | r) <;>
    rcases s with (s | s) | (⟨s, l⟩ | s)
  all_goals
    simp [blockMatrix, specialBlock, rankOneTorus_val, blockWeight,
      Matrix.diagonal_apply, Matrix.one_apply, Matrix.blockDiagonal]
  all_goals try (guard_hyp r : Fin 2; fin_cases r)
  all_goals try (guard_hyp s : Fin 2; fin_cases s)
  all_goals simp

private lemma ambientHom_torus (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) :
    let := rankOneExtensionCharTwo P hp
    ambientHom i (rankOneTorus t) = (torusWord P i t).val := by
  let := rankOneExtensionCharTwo P hp
  simp only [rankOneTorus, rankOneWeyl, map_mul, upper, lower,
    ambientHom_positive, ambientHom_negative]
  rfl

/-- The original coroot word has the prescribed integral-weight diagonal. -/
theorem torusWord_val (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (t : (ExtensionField P)ˣ) :
    (torusWord P i t).val.val = corootDiagonal P i t := by
  let := rankOneExtensionCharTwo P hp
  rw [← ambientHom_torus P hp]
  ext r s
  obtain ⟨r, rfl⟩ := (latticeEquiv i).surjective r
  obtain ⟨s, rfl⟩ := (latticeEquiv i).surjective s
  rw [ambientHom_entry, blockMatrix_torus]
  simp only [corootDiagonal, Matrix.diagonal_apply, (latticeEquiv i).injective.eq_iff,
    corootWeight_block]

end
end Triality.Standard.ConcreteBruhat.TorusCoordinates
