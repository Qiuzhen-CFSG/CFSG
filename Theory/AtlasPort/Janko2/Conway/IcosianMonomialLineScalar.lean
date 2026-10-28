/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialLineScalar.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialRootShapes

/-!
# IcosianMonomialLineScalar

Fixing a quaternionic root line is equivalent to a common right-scalar equation.
Nonzero coordinates determine monomial coefficients and constrain coordinate norms.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialLineScalar.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- An actual integral monomial map fixes a root line exactly when its three
coordinate equations have one common integral norm-one right scalar. -/
theorem icosianMonomial_line_iff (g : icosianLiftedMonomial) (r : IcosianRoot) :
    icosianMonomialToHermitian g • icosianRootPoint r=icosianRootPoint r ↔
      ∃ u : icosianNormOneGroup,∀ i,
        (g.val.left i).val.val*(r.val (g.val.right.symm i)).val=
          (r.val i).val*u.val.val := by
  rw [← icosianRootPoint_smul,icosianRootPoint_eq_iff]
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,fun i => ?_⟩
    have h := congrArg (fun s : IcosianRoot => (s.val i).val) hu
    change ((icosianMonomialToHermitian g • r).val i).val=(r.val i).val*u.val.val at h
    rwa [icosianMonomialRoot_coordinates] at h
  · rintro ⟨u,hu⟩
    refine ⟨u,?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [icosianMonomialRoot_coordinates]
    exact hu i

theorem icosianMonomial_line_permutation_norm (g : icosianLiftedMonomial)
    (r : IcosianRoot) (h : icosianMonomialToHermitian g • icosianRootPoint r=icosianRootPoint r)
    (i : Fin 3) : icosianRootNormWord r (g.val.right.symm i)=icosianRootNormWord r i := by
  obtain ⟨u,hu⟩ := (icosianMonomial_line_iff g r).mp h
  apply goldenIntegerToRational_injective
  simp only [icosianRootNormWord,icosianIntegralNorm_spec]
  have hn := congrArg icosianNorm (hu i)
  simpa only [icosianNorm_mul,icosianNormOneGroup_norm,one_mul,mul_one] using hn

/-- Once the block permutation and common right scalar are fixed, a monomial
line stabilizer of a root with no zero coordinate is uniquely determined. -/
theorem icosianMonomial_line_determined (r : IcosianRoot) (hr : ∀ i,r.val i≠0)
    (g h : icosianLiftedMonomial) (hp : g.val.right=h.val.right) (u : icosianNormOneGroup)
    (hg : ∀ i,(g.val.left i).val.val*(r.val (g.val.right.symm i)).val=(r.val i).val*u.val.val)
    (hh : ∀ i,(h.val.left i).val.val*(r.val (h.val.right.symm i)).val=(r.val i).val*u.val.val) :
    g=h := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    apply Subtype.ext
    have hn : (r.val (h.val.right.symm i)).val≠0 := by
      intro hz
      exact hr _ (Subtype.ext hz)
    apply mul_right_cancel₀ hn
    have he : (g.val.left i).val.val*(r.val (h.val.right.symm i)).val=
        (r.val i).val*u.val.val := by simpa only [hp] using hg i
    exact he.trans (hh i).symm
  · exact hp

end Atlas.Conway
