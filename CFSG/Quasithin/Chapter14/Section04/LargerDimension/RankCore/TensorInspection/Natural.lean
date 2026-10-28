module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import Theory.Representation.BinaryPermutation.ThreeTensorSemilinear

/-!
# The natural tensor rank bound in the literal star action

The faithful action of H/O₂(H) on U/Z(U) induces faithfulness on the first
tensor factor. Once its degree-two semilinearity is established, every
nonidentity star actor has binary moved rank at least four. In particular,
no natural-module involution contributes to the low-rank exception.

The semilinearity premise remains explicit: the full S₅ natural-module
extension must be identified inside the semilinear normalizer before this
is a completed source branch. It is not a rank-exclusion premise.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.2(5)
and 14.4.6(a), printed pp.1006,1008.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open TensorProduct Module Subgroup BinaryPermutation
variable {H V F W D : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module F W] [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F W]
  [Module.Finite (ZMod 2) W] [Group D]

/-- An explicitly equivariant semilinear natural tensor model excludes low rank. -/
theorem SourceAction.tensor_natural_semilinear_rank
    (d : SourceAction H U V)
    (hdegree : finrank (ZMod 2) F = 2) (hdim : 4 ≤ finrank (ZMod 2) W)
    (ρ : Representation (ZMod 2) D W)
    (hsemi : ∀ g, ∃ σ : F →+* F, ∀ c w, ρ g (c • w) = σ c • ρ g w)
    (e : (H ⧸ pCore 2 H) ≃* D × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] (W ⊗[ZMod 2] core (Fin 3)))
    (hf : ∀ a v, f (d.representation a v) = ThreeTensor.action ρ (e a) (f v))
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) : 4 ≤ d.movedRank a := by
  have hfaith : Function.Injective ρ := by
    intro g h hgh
    have heq : d.representation (e.symm (g, 1)) = d.representation (e.symm (h, 1)) := by
      apply LinearMap.ext
      intro v
      apply f.injective
      rw [hf, hf, e.apply_symm_apply, e.apply_symm_apply]
      change TensorProduct.map (ρ g) (coreRepresentation (Fin 3) 1) (f v) =
        TensorProduct.map (ρ h) (coreRepresentation (Fin 3) 1) (f v)
      rw [hgh]
    have heq' := congrArg (fun a => (e a).1) (d.faithful heq)
    simpa only [e.apply_symm_apply] using heq'
  rw [d.movedRank_eq_of_equivariant a f _ (hf a)]
  exact ThreeTensor.four_le_displacement_of_semilinear hdegree hdim ρ hfaith hsemi (e a)
    (fun h => ha (e.injective (h.trans (map_one e).symm)))
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
