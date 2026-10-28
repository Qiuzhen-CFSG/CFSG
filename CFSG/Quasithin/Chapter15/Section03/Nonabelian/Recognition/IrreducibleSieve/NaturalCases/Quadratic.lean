module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import Theory.Representation.BinaryQuadraticTransitivity

/-!
# Transporting the quadratic obstruction to the source action

The source nonsingular quadratic form is invariant under every subgroup of
the actor. An actual group-and-module equivalence transports nonzero-vector
transitivity back to this action, contradicting the binary dimension bound.
This route does not require the marked involution to belong to the component.

Source: Aschbacher--Smith, 15.3.53(2) and 15.3.58, printed pp.1146,1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open Representation
open CFSG.Quasithin.ChapterG.Section09

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X : Subgroup H} {T : Sylow 2 H} {v : H} {s : ℕ}

/-- The source orthogonal action cannot restrict to a model transitive on its
nonzero vectors. Only the model's actual orbit theorem remains to be supplied. -/
theorem SourceData.not_nonzero_transitive_model (h : SourceData ρ X T v s)
    (K : Subgroup H) {D M : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) D M)
    (ht : ∀ x y : M, x ≠ 0 → y ≠ 0 → ∃ g, σ g x = y) :
    ¬ Quasiequivalent (ρ.comp K.subtype) σ := by
  rintro ⟨e, f, hf⟩
  have ht' : ∀ x y : W, x ≠ 0 → y ≠ 0 → ∃ g : K, (ρ.comp K.subtype) g x = y := by
    intro x y hx hy
    obtain ⟨g, hg⟩ := ht (f x) (f y) (fun he => hx (f.map_eq_zero_iff.mp he))
      (fun he => hy (f.map_eq_zero_iff.mp he))
    refine ⟨e.symm g, f.injective ?_⟩
    rw [hf, e.apply_symm_apply, hg]
  obtain ⟨q, hn, hi⟩ := h.quadratic
  exact not_nondegenerate_quadratic_of_nonzero_transitive (ρ.comp K.subtype)
    (by have := h.six_le_degree; omega) ht' q (fun g w => hi g.val w) hn

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
