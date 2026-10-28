module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Fixed spaces and commutator spaces under duality

The annihilator exchanges the commutator space `[V, G]` with the fixed space
of the contragredient representation, and exchanges fixed spaces with dual
commutator spaces in finite dimension. Thus `[V, G] ≤ C_V(G)` is invariant
under duality. The proof uses evaluation of functionals on the generators
`ρ g v - v`, followed by double annihilation.

This gives the linear algebra of Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma B.4.7(1)–(3),
and the dimension identity used in B.4.7(4). The identities hold over any field;
no characteristic-two or elementary-abelian hypothesis is needed here.
-/

public section

open Module
namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- The subspace formulation of quadratic action agrees with the pointwise one. -/
theorem commutator_le_invariants_iff : Coinvariants.ker ρ ≤ ρ.invariants ↔
    ∀ g h : G, ∀ v : V, ρ g (ρ h v - v) = ρ h v - v := by
  rw [Coinvariants.ker, Submodule.span_le]
  constructor
  · intro h g t v
    exact (h (Set.mem_range_self (t, v))) g
  · intro h x hx
    obtain ⟨⟨g, v⟩, rfl⟩ := hx
    exact fun t => h t g v

/-- The annihilator of `[V, G]` is the fixed space in the dual. -/
theorem dualAnnihilator_coinvariantsKer : (Coinvariants.ker ρ).dualAnnihilator = ρ.dual.invariants := by
  ext f
  rw [Submodule.mem_dualAnnihilator, mem_invariants]
  constructor
  · intro hf g
    ext v
    exact sub_eq_zero.mp (by simpa [Module.Dual.transpose_apply] using hf _ (Coinvariants.sub_mem_ker (ρ := ρ) g⁻¹ v))
  · intro hf
    have hle : Coinvariants.ker ρ ≤ LinearMap.ker f := by
      rw [Coinvariants.ker, Submodule.span_le]
      rintro _ ⟨⟨g,v⟩, rfl⟩
      have he := congrArg (fun (l : Module.Dual k V) => l v) (hf g⁻¹)
      simpa [Module.Dual.transpose_apply] using sub_eq_zero.mpr he
    exact fun v hv => hle hv

/-- Evaluation identifies the coannihilator of `[V*, G]` with `C_V(G)`. -/
theorem dualCoannihilator_dual_coinvariantsKer : (Coinvariants.ker ρ.dual).dualCoannihilator = ρ.invariants := by
  ext v
  rw [Submodule.mem_dualCoannihilator, mem_invariants]
  constructor
  · intro hv g
    apply Module.eval_apply_injective k
    ext f
    have he := hv _ (Coinvariants.sub_mem_ker (ρ := ρ.dual) g⁻¹ f)
    simpa [Module.Dual.transpose_apply] using sub_eq_zero.mp he
  · intro hv f hf
    have hle : Coinvariants.ker ρ.dual ≤ LinearMap.ker (Module.Dual.eval k V v) := by
      rw [Coinvariants.ker, Submodule.span_le]
      rintro _ ⟨⟨g,f⟩, rfl⟩
      change f (ρ g⁻¹ v) - f v = 0
      rw [hv g⁻¹, sub_self]
    exact hle hf

variable [FiniteDimensional k V]
/-- The annihilator of the fixed space is the dual commutator space. -/
theorem dualAnnihilator_invariants : ρ.invariants.dualAnnihilator = Coinvariants.ker ρ.dual := by
  rw [← dualCoannihilator_dual_coinvariantsKer ρ, Subspace.dualCoannihilator_dualAnnihilator_eq]

/-- An action is quadratic exactly when its contragredient action is quadratic. -/
theorem commutator_le_invariants_iff_dual : Coinvariants.ker ρ ≤ ρ.invariants ↔
    Coinvariants.ker ρ.dual ≤ ρ.dual.invariants := by
  rw [← dualAnnihilator_coinvariantsKer ρ, ← dualAnnihilator_invariants ρ, Subspace.dualAnnihilator_le_dualAnnihilator_iff]

omit [FiniteDimensional k V] in
/-- The numerator of the dual offender ratio is the dimension of `[V, G]`. -/
theorem finrank_dual_quotient_invariants : Module.finrank k (Module.Dual k V ⧸ ρ.dual.invariants) =
    Module.finrank k (Coinvariants.ker ρ) := by
  rw [← dualAnnihilator_coinvariantsKer ρ]
  exact (Subspace.quotAnnihilatorEquiv (Coinvariants.ker ρ)).finrank_eq.trans
    Subspace.dual_finrank_eq
end Representation

namespace Subspace
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
/-- Equivariance of annihilation for the contragredient action of `GL(V)`. -/
theorem dualAnnihilator_map_linearEquiv (e : V ≃ₗ[k] V) (U : Submodule k V) :
    (U.map e.toLinearMap).dualAnnihilator =
      U.dualAnnihilator.map e.symm.dualMap.toLinearMap := by
  ext f
  constructor
  · intro hf
    refine ⟨e.dualMap f, ?_, by ext v; simp⟩
    change e.dualMap f ∈ U.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro v hv
    exact hf _ (Submodule.mem_map_of_mem hv)
  · rintro ⟨f, hf, rfl⟩
    change f ∈ U.dualAnnihilator at hf
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    rintro _ ⟨v, hv, rfl⟩
    simpa using hf v hv

/-- Annihilator dimension in the ambient finite-dimensional space. -/
theorem finrank_dualAnnihilator [FiniteDimensional k V] (U : Submodule k V) :
    Module.finrank k U.dualAnnihilator = Module.finrank k V - Module.finrank k U := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega
end Subspace
