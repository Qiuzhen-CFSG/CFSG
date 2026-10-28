module

public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Tori.Basic

/-!
The common-torus input to GLS3, Theorem 1.11.4, isolated at an API boundary.

The source theorem obtains a maximal torus in the intersection of two Borels
by a geometric argument that is not yet represented by the affine variety
interfaces in this repository.  This module records the exact conversion
needed by downstream intersection arguments: an explicitly supplied maximal
torus of the Borel intersection gives a maximal torus contained in both
Borels.  The converse and the forward conversion are packaged as an
equivalence, so the missing geometric input is visible as a single explicit
hypothesis rather than hidden behind a placeholder-backed theorem.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

section

variable {K : Variety k} [AlgebraicGroup K]

/-- A maximal torus explicitly contained in the Borel intersection is a
common maximal torus for the two Borels.

The reductivity and Borel hypotheses are retained in the interface to match
the geometric source context; the proof itself is the carrier-level
intersection calculation. -/
public theorem exists_common_maximalTorus_of_borel_pair
    (_hK : IsReductiveAlgebraicGroup K)
    (B₀ B₁ : ClosedSubgroup K)
    (_hB₀ : IsBorelSubgroup B₀) (_hB₁ : IsBorelSubgroup B₁)
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T)
    (hTinter : T ≤ B₀.inter B₁) :
    ∃ T : ClosedSubgroup K,
      IsMaximalTorus T ∧ T ≤ B₀ ∧ T ≤ B₁ := by
  refine ⟨T, hT, ?_, ?_⟩
  · intro x hx
    exact (ClosedSubgroup.mem_inter_iff B₀ B₁ x).mp (hTinter hx) |>.1
  · intro x hx
    exact (ClosedSubgroup.mem_inter_iff B₀ B₁ x).mp (hTinter hx) |>.2

/-- The common-maximal-torus conclusion is equivalent to supplying a maximal
torus of the Borel intersection.  This is the explicit geometric/API form
used by the intersection decomposition consumers. -/
public theorem common_maximalTorus_exists_iff
    (_hK : IsReductiveAlgebraicGroup K)
    (B₀ B₁ : ClosedSubgroup K)
    (_hB₀ : IsBorelSubgroup B₀) (_hB₁ : IsBorelSubgroup B₁) :
    (∃ T : ClosedSubgroup K,
      IsMaximalTorus T ∧ T ≤ B₀ ∧ T ≤ B₁) ↔
      (∃ T : ClosedSubgroup K,
        IsMaximalTorus T ∧ T ≤ B₀.inter B₁) := by
  constructor
  · rintro ⟨T, hT, hTB₀, hTB₁⟩
    refine ⟨T, hT, ?_⟩
    intro x hx
    exact ⟨hTB₀ hx, hTB₁ hx⟩
  · rintro ⟨T, hT, hTinter⟩
    exact exists_common_maximalTorus_of_borel_pair
      (K := K) _hK B₀ B₁ _hB₀ _hB₁ T hT hTinter

end

end Theory.AlgebraicGroup
