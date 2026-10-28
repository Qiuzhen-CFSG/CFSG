module

public import Theory.SpecificGroups.Alternating.PositiveLocalCubicRank
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Positive local cubic rank in binary linear groups

The full coordinate permutation action is faithful over the binary field.
Its determinant is automatically one, so an embedded A₄ on four coordinates
supplies a normal Klein-four witness in every binary special linear group
of dimension at least four. The existing literal comparison of binary PSL
with SL transports this same local bound to the projective carrier.

Source: Aschbacher–Smith, A.1.34 and A.3.8, printed pp.29–30 and45–46.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.PositiveLocalCubicRank

private def permutationAction (n : ℕ) :
    Equiv.Perm (Fin n) →* OuterCyclic.LinearGroup n where
  toFun σ := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) σ.symm
  map_one' := by ext v i; rfl
  map_mul' σ τ := by ext v i; rfl

private theorem permutationAction_injective (n : ℕ) :
    Function.Injective (permutationAction n) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  let v : Fin n → ZMod 2 := Pi.single i 1
  have he := congrArg (fun k : OuterCyclic.LinearGroup n => k v (σ i)) h
  change v (σ.symm (σ i)) = v (τ.symm (σ i)) at he
  have hh : τ.symm (σ i) = i := by
    simpa [v, Pi.single_apply] using he.symm
  exact (τ.apply_symm_apply (σ i)).symm.trans (congrArg τ hh)

/-- The original binary special linear carrier has positive local cubic rank. -/
theorem specialLinear {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ twoLocalPrimeRank 3 (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  let f := (OuterCyclic.slEquivLinear n).symm.toMonoidHom.comp
    ((permutationAction n).comp (alternatingGroup (Fin n)).subtype)
  have hf : Function.Injective f := (OuterCyclic.slEquivLinear n).symm.injective.comp
    ((permutationAction_injective n).comp Subtype.val_injective)
  exact (Theory.Quasithin.alternating_one_le_twoLocalPrimeRank hn).trans
    (twoLocalPrimeRank_le_of_injective 3 f hf)

/-- The binary projective comparison preserves the actual local witness. -/
theorem projectiveSpecialLinear {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ twoLocalPrimeRank 3 (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  let e := OuterCyclic.projectiveEquivSL (by omega : 0 < n)
  exact (specialLinear hn).trans
    (twoLocalPrimeRank_le_of_injective 3 e.symm.toMonoidHom e.symm.injective)

end BinaryLinear.PositiveLocalCubicRank
