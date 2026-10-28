module

public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# A finite unipotent fixed-line criterion

Every nonzero representation of a finite two-group in characteristic two has
a nonzero fixed vector. Consequently, if the fixed vectors lie in one line,
every nonzero subrepresentation contains that line. If its ambient orbit spans,
the representation is irreducible.

This isolates the finite-group step in the highest-weight approach to GLS3,
Theorem 2.8.2. Identifying the fixed line and proving its finite orbit spans
remain the substantive restricted-highest-weight obligations.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

universe u v w
variable {k : Type u} [Field k] [CharP k 2]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

/-- Fixed-line detection and cyclicity under the finite group imply
irreducibility. No rational or algebraic-group action is assumed here. -/
theorem irreducible_of_fixedLine_of_orbitSpan
    (ρ : Representation k G V) (U : Subgroup G) [Finite U]
    (hU : IsPGroup 2 U) (v : V)
    (hline : ∀ w : V, (∀ g : U, ρ g.val w = w) →
      w ∈ Submodule.span k ({v} : Set V))
    (hspan : Submodule.span k (Set.range (fun g : G => ρ g v)) = ⊤) :
    Representation.IsIrreducible ρ := by
  refine ⟨fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    have hWbot : W.toSubmodule ≠ ⊥ := by
      intro h
      exact hW (Subrepresentation.toSubmodule_injective h)
    let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hWbot
    have hc : ringChar k = 2 := ringChar.eq k 2
    obtain ⟨w, hw, hfix⟩ := Representation.pGroup_fix_nonzero_vector
      (hc ▸ (by decide : (2 : ℕ) ≠ 0)) (hc.symm ▸ hU)
      (W.toRepresentation.comp U.subtype)
    have hw0 : (w : V) ≠ 0 := by
      intro h
      exact hw (Subtype.ext h)
    have hwline := hline w (fun g => congrArg Subtype.val (hfix g))
    obtain ⟨c, hcw⟩ := Submodule.mem_span_singleton.mp hwline
    have hc0 : c ≠ 0 := by
      intro h
      apply hw0
      rw [← hcw, h, zero_smul]
    have hvW : v ∈ W.toSubmodule := by
      have h := W.toSubmodule.smul_mem c⁻¹ w.property
      rw [← hcw, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
      exact h
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact W.apply_mem_toSubmodule g hvW

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
