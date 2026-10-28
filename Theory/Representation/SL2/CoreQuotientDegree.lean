module

public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.GroupAction.NormalPChiefSeries.Linear
/-!
# Binary chief degrees above an SL₂ two-core quotient

A normal two-subgroup acts trivially on every irreducible binary module.
Descend the original representation through its two-core, then transport
along the specified actual SL₂ quotient equivalence. The unconditional
prime-field degree theorem supplies dimension at least twice the defining
field exponent. The final theorem applies this to every noncentral factor
of an actual group chief series on an elementary normal subgroup.

Source: Aschbacher–Smith E.2.13(4), printed p.225. The whole module need
not factor through the two-core; only its actual chief factors are descended.
-/

public section
open Subgroup Representation
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {H K W : Type*} [Group H] [Finite H] [Field K] [Finite K] [CharP K 2]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem core_quotient_irreducible_finrank_bound
    (e : (H ⧸ pCore 2 H) ≃* SL(2,K))
    (ρ : Representation (ZMod 2) H W) [ρ.IsIrreducible]
    (hn : ∃ h, ρ h ≠ 1) (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card K = 2 ^ m) :
    2 * m ≤ Module.finrank (ZMod 2) W := by
  have hk : pCore 2 H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let τ := quotientOfLEKer ρ (pCore 2 H) hk
  let σ := τ.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr inferInstance
  have hnσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨h, hh⟩ := hn
    refine ⟨e (QuotientGroup.mk' (pCore 2 H) h), ?_⟩
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, τ, quotientOfLEKer_apply] using hh
  exact Unsigned.irreducible_finrank_bound 2 σ hnσ m hm hcard

end Representation.SL2

namespace NoncentralChiefRefinement.SeriesOn
variable {H K : Type*} [Group H] [Finite H] [Field K] [Finite K] [CharP K 2]
  {U : Subgroup H} [U.Normal] [IsElementaryAbelian 2 U]
theorem noncentral_factor_finrank_ge_sl2
    (e : (H ⧸ pCore 2 H) ≃* SL(2,K))
    (s : SeriesOn U) (i : Fin s.series.length) (hi : ¬ s.Central i)
    (m : ℕ) (hm : m ≠ 0) (hcard : Nat.card K = 2 ^ m) :
    2 * m ≤ Module.finrank (ZMod 2) (Additive (s.Factor i)) := by
  let := s.factorRepresentation_irreducible i
  apply Representation.SL2.core_quotient_irreducible_finrank_bound e
    (s.factorRepresentation i) ?_ m hm hcard
  by_contra! hn
  apply hi
  rw [s.central_iff_action]
  intro h x
  exact congrArg Additive.toMul (congrArg (fun f => f (Additive.ofMul x)) (hn h))
end NoncentralChiefRefinement.SeriesOn
