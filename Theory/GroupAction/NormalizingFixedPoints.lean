module

public import Theory.GroupAction.Invariant
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Fixed subgroups preserved by a normalizing actor

For an action of `G` on a group `V`, a subgroup `B` normalizing `A`
preserves the subgroup of `A`-fixed points. No finiteness, commutativity,
or coprimality hypotheses are needed.

If `v` is `A`-fixed, then `a • (b • v)` can be rewritten as
`b • ((b⁻¹ab) • v) = b • v`, since `b⁻¹ab` belongs to `A`.
This gives forward stability; applying it with `b⁻¹` gives the reverse
membership implication. All subgroup actions are the canonical restrictions
of the given ambient action.

This standard action lemma complements `NormalizingActor` and supplies
invariance of coprime fixed-point summands in the exceptional-module argument
of Stellmacher (1.6), journal p.18; see `refs/latex/stellmacher-n-group.tex`.
-/

/-- A normalizing actor preserves the fixed subgroup. -/
public theorem fixedPoints_isInvariant_of_normalizing_actor
    {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
    (B A : Subgroup G) (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    IsInvariant B V (FixedPoints.subgroup A V) := by
  have hforward : ∀ b : B, ∀ v : V,
      v ∈ FixedPoints.subgroup A V → b • v ∈ FixedPoints.subgroup A V := by
    intro b v hv a
    have hconj : (b : G)⁻¹ * (a : G) * (b : G) ∈ A := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (hBA (B.inv_mem b.property)) (a : G)).mp a.property
    have ha := hv (⟨(b : G)⁻¹ * (a : G) * (b : G), hconj⟩ : A)
    change ((b : G)⁻¹ * (a : G) * (b : G)) • v = v at ha
    change (a : G) • ((b : G) • v) = (b : G) • v
    calc
      (a : G) • ((b : G) • v) =
          (b : G) • (((b : G)⁻¹ * (a : G) * (b : G)) • v) := by
        simp only [← mul_smul, mul_assoc, mul_inv_cancel_left]
      _ = (b : G) • v := congrArg (fun w : V => (b : G) • w) ha
  constructor
  intro b v
  constructor
  · exact hforward b v
  · intro hv
    simpa only [inv_smul_smul] using hforward b⁻¹ (b • v) hv
