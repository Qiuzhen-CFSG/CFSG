module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLeviDefinitions
public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLevi.CentralTorus

/-!
# Full-Levi fixed points and radical separation in triality

In characteristic two the full split Levi is the product of the root subsystem
and its centralizing torus, with unique factors. Graph-field invariance then
forces both factors of a fixed element to be fixed. The torus factor lies in
the elementary group by the concrete folded rank-one construction, so division
lifts the subsystem factor as well. Mapping through the original central
quotient yields exactly the join of the descended subsystem Levi and torus.

The imported normalization and separation results supply the other two
full-Levi inputs required by the parabolic assembly. Only radical separation
uses relative normality of the radical in its split parabolic. All results
include q = 2 and make no perfectness assertion for PSL₂(2).

Source: GLS3 Definition 2.6.4 and Theorem 2.6.5(f,g)
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.11–12,
printed pp.262–264 (`refs/quasithin.pdf`).
-/

@[expose] public section

namespace Triality.Standard.RadicalCoordinates
open Parabolics ConcreteBruhat TorusCoordinates
open scoped Pointwise
noncomputable section

/-- Unique subsystem/central-torus factors of a fixed element are fixed. -/
theorem splitFullLevi_central_factors_fixed (P : Parameters) (hp : P.prime = 2)
    (a : Node) (l t : SplitGroup P) (hl : l ∈ splitLevi P a)
    (ht : t ∈ splitCentralTorus P a)
    (hfix : graphFieldAutomorphism P (l * t) = l * t) :
    l ∈ fixedSubgroup P ∧ t ∈ fixedSubgroup P := by
  have hlF : graphFieldAutomorphism P l ∈ splitLevi P a :=
    (splitLevi_invariant P a).le ⟨l, hl, rfl⟩
  have htF := graphField_mem_splitCentralTorus P a ht
  have he : (⟨graphFieldAutomorphism P l, hlF⟩, ⟨graphFieldAutomorphism P t, htF⟩) =
      ((⟨l, hl⟩, ⟨t, ht⟩) : splitLevi P a × splitCentralTorus P a) :=
    Subgroup.mul_injective_of_disjoint (disjoint_splitLevi_splitCentralTorus P hp a)
      ((map_mul _ l t).symm.trans hfix)
  exact ⟨congrArg (fun x : splitLevi P a × splitCentralTorus P a => x.1.val) he,
    congrArg (fun x : splitLevi P a × splitCentralTorus P a => x.2.val) he⟩

/-- Descent of the full Levi retains exactly the subsystem Levi and torus.
The fixed torus factor is elementary by its proved folded rank-one words;
the other factor is then elementary by division in the elementary group. -/
theorem descendSubgroup_splitFullLevi (P : Parameters) (hp : P.prime = 2) (a : Node) :
    descendSubgroup P (splitFullLevi P a) = levi P a ⊔ torus P := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    have hx' : elementaryInclusion P x ∈
        (splitLevi P a : Set (SplitGroup P)) * splitCentralTorus P a :=
      (Set.ext_iff.mp (splitFullLevi_eq_mul_centralTorus P hp a)
        (elementaryInclusion P x)).mp hx
    obtain ⟨l, hl, t, ht, he⟩ := hx'
    have hfix : graphFieldAutomorphism P (l * t) = l * t :=
      (congrArg (graphFieldAutomorphism P) he).trans (x.val.property.trans he.symm)
    have htf := (splitFullLevi_central_factors_fixed P hp a l t hl ht hfix).2
    let tf : fixedSubgroup P := ⟨t, htf⟩
    let te : ElementaryGroup P := ⟨tf, fixedTorus_le_elementary P hp ht.1⟩
    let le : ElementaryGroup P := x * te⁻¹
    have hle : elementaryInclusion P le = l := by
      change elementaryInclusion P x * t⁻¹ = l
      rw [← he, mul_inv_cancel_right]
    have hprod : toCarrier P le * toCarrier P te = toCarrier P x :=
      (map_mul (toCarrier P) le te).symm.trans
        (congrArg (toCarrier P) (inv_mul_cancel_right x te))
    rw [← hprod]
    apply Subgroup.mul_mem
    · apply Subgroup.mem_sup_left
      refine ⟨le, ?_, rfl⟩
      change elementaryInclusion P le ∈ splitLevi P a
      exact hle.symm ▸ hl
    · exact Subgroup.mem_sup_right ⟨te, ht.1, rfl⟩
  · exact sup_le (descendSubgroup_mono P (show splitLevi P a ≤ splitFullLevi P a from le_sup_left))
      (descendSubgroup_mono P (show splitTorus P ≤ splitFullLevi P a from le_sup_right))

end
end Triality.Standard.RadicalCoordinates
