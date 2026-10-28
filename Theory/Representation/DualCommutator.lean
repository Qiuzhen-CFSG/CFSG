module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Fixed spaces and commutator spaces under duality

For a group representation, the commutator space `[V,G]` is Mathlib's
`Representation.Coinvariants.ker`. The fixed space on the dual is its
annihilator, and the fixed space on the original representation is the
coannihilator of the dual commutator space. This pairing also shows that
quadratic action passes in both directions under duality. In finite dimension,
the dimension of `[V*,G]` equals the codimension of `C_V(G)`.

These are the linear-algebra reductions used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.4.7(4) and B.5.13 (combined
1 March 2004 manuscript, pp. 90 and 110–112). The proofs use annihilator
duality and do not require finite groups or characteristic two.
-/

namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)

/-- Fixed functionals are exactly those vanishing on the commutator space. -/
public theorem invariants_dual_eq_commutator_annihilator :
    invariants ρ.dual = (Coinvariants.ker ρ).dualAnnihilator := by
  ext f
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hf
    have hle : Coinvariants.ker ρ ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, v⟩, rfl⟩
      change f (ρ g v - v) = 0
      rw [map_sub, sub_eq_zero]
      have h := LinearMap.congr_fun (hf g⁻¹) v
      change f (ρ ((g⁻¹)⁻¹) v) = f v at h
      simpa only [inv_inv] using h
    exact fun w hw => hle hw
  · intro hf g
    apply LinearMap.ext
    intro v
    have h := hf _ (Coinvariants.sub_mem_ker (ρ := ρ) g⁻¹ v)
    change f (ρ g⁻¹ v) = f v
    simpa only [map_sub, sub_eq_zero] using h

/-- Fixed vectors are exactly those annihilated by the dual commutator space. -/
public theorem invariants_eq_dual_commutator_coannihilator :
    invariants ρ = (Coinvariants.ker ρ.dual).dualCoannihilator := by
  ext v
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hv
    have hle : Coinvariants.ker ρ.dual ≤ LinearMap.ker (Module.Dual.eval k V v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, f⟩, rfl⟩
      change f (ρ g⁻¹ v) - f v = 0
      rw [hv g⁻¹, sub_self]
    exact fun f hf => hle hf
  · intro hv g
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro f
    have h := hv _ (Coinvariants.sub_mem_ker (ρ := ρ.dual) g⁻¹ f)
    change f (ρ ((g⁻¹)⁻¹) v) - f v = 0 at h
    simpa only [inv_inv, map_sub] using h

/-- The fixed-space codimension is the dimension of the dual commutator space. -/
public theorem finrank_quotient_invariants_eq_dual_commutator [FiniteDimensional k V] :
    Module.finrank k (V ⧸ invariants ρ) = Module.finrank k (Coinvariants.ker ρ.dual) := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (Coinvariants.ker ρ.dual)
  rw [← ρ.invariants_eq_dual_commutator_coannihilator] at h
  exact Nat.add_right_cancel ((invariants ρ).finrank_quotient_add_finrank.trans h.symm)

/-- Quadratic action is preserved and reflected by duality. -/
public theorem quadratic_dual_iff :
    Coinvariants.ker ρ.dual ≤ invariants ρ.dual ↔ Coinvariants.ker ρ ≤ invariants ρ := by
  rw [ρ.invariants_dual_eq_commutator_annihilator,
    Submodule.le_dualAnnihilator_iff_le_dualCoannihilator,
    ← ρ.invariants_eq_dual_commutator_coannihilator]

/-- The dual fixed-space codimension is the dimension of the original commutator space. -/
public theorem finrank_quotient_dual_invariants_eq_commutator [FiniteDimensional k V] :
    Module.finrank k (Module.Dual k V ⧸ invariants ρ.dual) =
      Module.finrank k (Coinvariants.ker ρ) := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (Coinvariants.ker ρ)
  rw [← ρ.invariants_dual_eq_commutator_annihilator] at h
  have hq := (invariants ρ.dual).finrank_quotient_add_finrank
  rw [Subspace.dual_finrank_eq] at hq
  exact Nat.add_right_cancel (hq.trans h.symm)
end Representation
