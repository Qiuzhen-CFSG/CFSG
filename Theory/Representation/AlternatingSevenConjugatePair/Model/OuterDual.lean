module
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Natural
public import Theory.Representation.SymmetricEightConstituents.OuterDual
/-!
# The actual dual of the marked binary A₇ four-space

Restrict the established A₈ outer-duality pairing along the literal
seven-letter embedding. The exceptional comparisons agree by their public
orthogonal-action equations and injectivity, so the resulting equivalence
uses the same A₇ actor on both sides.

Source: the four-plus-dual alternative used in Aschbacher–Smith 13.8.24,
printed pp.958–959. The pairing comes from the attributed ATLAS coordinate
comparison in SymmetricEightConstituents.OuterDual; its license and
attribution remain in that module.
-/

public section
open Representation
namespace Representation.AlternatingSevenConjugatePair.Model
noncomputable section
private theorem lift_transposition :
    Equiv.Perm.viaEmbeddingHom letterEmbedding transposition =
      SymmetricEightConstituents.transposition := by
  apply _root_.Equiv.ext
  intro x
  refine Fin.lastCases ?_ (fun i => ?_) x
  · change transposition.viaEmbedding letterEmbedding 7 = _
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · rw [SymmetricEightConstituents.transposition_eq_swap]
      decide
    · rintro ⟨i, hi⟩
      have hh := congrArg Fin.val hi
      change i.val = 7 at hh
      omega
  · change transposition.viaEmbedding letterEmbedding (letterEmbedding i) = _
    rw [Equiv.Perm.viaEmbedding_apply, SymmetricEightConstituents.transposition_eq_swap]
    have h : ∀ i : Fin 7, letterEmbedding (transposition i) =
        Equiv.swap (0 : Fin 8) 1 (letterEmbedding i) := by decide
    exact h i

private theorem embedding_outer (a : alternatingGroup (Fin 7)) :
    alternatingEmbedding (outer a) =
      SymmetricEightConstituents.outer (alternatingEmbedding a) := by
  apply Subtype.ext
  change Equiv.Perm.viaEmbeddingHom letterEmbedding (transposition * a.val * transposition) = _
  rw [map_mul, map_mul, lift_transposition, SymmetricEightConstituents.outer_val]
  rfl

private theorem natural_restrict (a : alternatingGroup (Fin 7)) (v : Four) :
    natural a v = SymmetricEightConstituents.natural (alternatingEmbedding a) v := by
  rw [natural_apply, SymmetricEightConstituents.natural_apply]
  congr 2
  apply Atlas.Order20160A8.Exterior.binary_injective
  rw [← SymmetricEightConstituents.comparison_orthogonal]
  exact (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two_orthogonal
    (alternatingEmbedding a)).symm

/-- The same-marked outer-conjugate four-space is the actual dual. -/
noncomputable def outerDualEquiv : outerNatural.Equiv natural.dual :=
  .mk SymmetricEightConstituents.outerDualEquiv (by
    intro a
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change SymmetricEightConstituents.outerDualEquiv (natural (outer a) v) w =
      SymmetricEightConstituents.outerDualEquiv v (natural a⁻¹ w)
    rw [natural_restrict, embedding_outer, natural_restrict, map_inv]
    simpa only [SymmetricEightConstituents.outerNatural_apply, Representation.dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply] using LinearMap.congr_fun
      (SymmetricEightConstituents.outerDualEquiv_equivariant (alternatingEmbedding a) v) w)
end
end Representation.AlternatingSevenConjugatePair.Model
