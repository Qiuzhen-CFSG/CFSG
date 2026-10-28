module

public import Theory.Representation.SL2.HighestWeightUnique
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Mathlib.RepresentationTheory.Invariants

/-!
# Upper-Unipotent Invariants of Highest-Weight Modules

For a finite field K embedded in a coefficient field F and a degree n < |K|,
the actual highest-weight orbit span has a one-dimensional fixed subspace
under the shared upper-unipotent subgroup of SL2(K). No algebraic closure or
characteristic restriction is required for this computation.

The range-membership theorem for the subgroup identifies invariance with
being fixed by every upper transvection. The proved fixed-line characterization
then identifies the invariant submodule with the span of the actual nonzero
pure-power generator, whose span has dimension one.

This is the concrete fixed-space calculation in Alperin--Brauer--Gorenstein
II.4, Lemma 18(ii), article pp. 45--46. Sylow conjugacy and descent through the
Schur field transfer it to the original prime-field representation.
-/

open MvPolynomial Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace Representation.SL2

public theorem highestWeightSpan_upper_invariants_finrank {K F : Type*} [Field K] [Finite K]
    [Field F] (e : K →+* F) (n : ℕ) (hn : n < Nat.card K) :
    Module.finrank F (Representation.invariants
      ((highestWeightSpan e n).toRepresentation.comp (upperUnipotent K).subtype)) = 1 := by
  let v₀ : (highestWeightSpan e n).toSubmodule :=
    ⟨X 0 ^ n, X_pow_mem_highestWeightSpan e n⟩
  have heq : Representation.invariants
      ((highestWeightSpan e n).toRepresentation.comp (upperUnipotent K).subtype) =
      Submodule.span F {v₀} := by
    ext v
    rw [Representation.mem_invariants, Submodule.mem_span_singleton]
    constructor
    · intro hv
      have hfix : ∀ t : K, (highestWeightSpan e n).toRepresentation
          (transvection zero_ne_one t) v = v := fun t =>
        hv ⟨_, (mem_upperUnipotent K _).mpr ⟨t, rfl⟩⟩
      obtain ⟨c, hc⟩ := (highestWeightSpan_upper_fixed_iff e n hn v).mp hfix
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩ g
      obtain ⟨t, ht⟩ := (mem_upperUnipotent K g.val).mp g.property
      have hfix := (highestWeightSpan_upper_fixed_iff e n hn v).mpr ⟨c, hc.symm⟩
      change (highestWeightSpan e n).toRepresentation g.val v = v
      rw [← ht]
      exact hfix t
  rw [heq]
  apply finrank_span_singleton
  intro h
  exact (pow_ne_zero n (X_ne_zero (0 : Fin 2))) (congrArg Subtype.val h)

end Representation.SL2
