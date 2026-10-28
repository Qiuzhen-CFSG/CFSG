module

public import Theory.Representation.PSL3Two.ResidualFFForms.Reduction
public import Theory.Representation.DualCommutator
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Full displacement survives restriction to the two-residual

Full commutator generation is equivalent to absence of fixed vectors on the
dual module. A normal subgroup with two-group quotient has the same vanishing
property, by the modular fixed-vector theorem. Duality gives generation by
the actual embedded residual, with no assumption of ambient normality for K.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
G.6.2(2), printed p.345. O²(K) is the two-residual, not the two-core.
-/

public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
/-- The explicit commutator span agrees with Mathlib's coinvariant kernel. -/
theorem subspaceCommutator_top_eq_coinvariants (K : Subgroup G) :
    subspaceCommutator ρ ⊤ K = Coinvariants.ker (ρ.comp K.subtype) := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, _, rfl⟩
    exact ⟨(⟨g, hg⟩, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, g.property, w, Submodule.mem_top, rfl⟩

variable [Finite G] [FiniteDimensional (ZMod 2) V]
/-- Full commutator generation persists on the embedded two-residual. -/
theorem commutator_pResidual_eq_top (K : Subgroup G)
    (hK : subspaceCommutator ρ ⊤ K = ⊤) :
    subspaceCommutator ρ ⊤ ((pResidual 2 K).map K.subtype) = ⊤ := by
  let σ : Representation (ZMod 2) K V := ρ.comp K.subtype
  have hcoin : Coinvariants.ker σ = ⊤ := by
    rwa [subspaceCommutator_top_eq_coinvariants] at hK
  have hdual : σ.dual.invariants = ⊥ := by
    rw [invariants_dual_eq_commutator_annihilator, hcoin,
      Submodule.dualAnnihilator_top]
  have hres := BinaryLinearThree.ResidualFFForms.invariants_restrict_eq_bot
    σ.dual (pResidual 2 K) (isPGroup_quotient_pResidual 2) hdual
  have hres' : Representation.invariants (Representation.dual (σ.comp (pResidual 2 K).subtype)) = ⊥ := hres
  rw [invariants_dual_eq_commutator_annihilator,
    Submodule.dualAnnihilator_eq_bot_iff] at hres'
  apply top_unique
  apply hres'.ge.trans
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, v⟩, rfl⟩
  exact Submodule.subset_span ⟨g.val.val,
    ⟨g.val, g.property, rfl⟩, v, Submodule.mem_top, rfl⟩
end Representation.BinaryOffender
