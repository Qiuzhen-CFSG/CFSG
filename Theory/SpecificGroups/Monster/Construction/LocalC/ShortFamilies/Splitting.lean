module

public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortFamilies.Partition
public import Mathlib.Algebra.DirectSum.Module

/-!
# The four orthogonal short-space summands

The source subspaces `B_Z`, `B_0^1`, `B_E^2` and `B_E^3` are the spans of
the octad vectors, odd vectors, `wPlus = v + u`, and `wMinus = v - u`.
The partition distinguishes the first two spans from the pair vectors.
The already computed pair inner products show that the two `w` spans are
orthogonal. The identities `wPlus ± wMinus = 2v, 2u` recover every short
vector, and `shortBasis` supplies their spanning property. Positivity of
`shortForm` proves independence, giving the internal direct sum and its
canonical addition equivalence.

Source: Michael Aschbacher, *Sporadic Groups*, Lemma 27.8(5), printed p. 150
(PDF page 81, left page). The displayed definition of `B_Z` prints `R^1`,
although (1) defines only `R^2`, `R^3`, and `R^4`. Here `B_Z` uses `R^2`,
the octad family: this is forced by the preceding partition, the remaining
three displayed spans, and the stated proof from (2)–(4).
-/

@[expose] public section
noncomputable section
open Atlas.Codes Atlas.Fischer Atlas.Lattices
open scoped BigOperators DirectSum
namespace Sporadic.Monster.Construction.LocalC.ShortFamilies
open TrialitySpin
attribute [local instance] Classical.propDecidable

/-- The four spaces denoted `B_Z`, `B_0^1`, `B_E^2`, and `B_E^3` in the source. -/
inductive Summand
  | octad | odd | plus | minus
  deriving DecidableEq

abbrev PointPair := {p : Omega × Omega // p.1 ≠ p.2}

def summandGenerators : Summand → Set Space
  | .octad => Set.range (fun p : OctadParameters => shortVector sourceLatticeComparison (rOctad p))
  | .odd => Set.range (fun p : Omega × ParkerLoop => shortVector sourceLatticeComparison (rOdd p.1 p.2))
  | .plus => Set.range (fun p : PointPair => wPlus p.val.1 p.val.2 p.prop)
  | .minus => Set.range (fun p : PointPair => wMinus p.val.1 p.val.2 p.prop)

def summandSpace (i : Summand) : Submodule ℝ Space := Submodule.span ℝ (summandGenerators i)

abbrev octadSpace := summandSpace .octad
abbrev oddSpace := summandSpace .odd
abbrev plusSpace := summandSpace .plus
abbrev minusSpace := summandSpace .minus

private theorem form_octad_odd (p : OctadParameters) (x : Omega) (d : ParkerLoop) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison (rOctad p))
      (shortVector sourceLatticeComparison (rOdd x d)) = 0 :=
  form_different_shapes (i := .octad) (j := .odd) (by decide)
    (rOctad_hasShape p) (rOdd_hasShape x d)

private theorem form_octad_u (p : OctadParameters) (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison (rOctad p))
      (u x y hxy) = 0 :=
  form_different_shapes (i := .octad) (j := .pureFour) (by decide)
    (rOctad_hasShape p) (ru_hasShape x y hxy)

private theorem form_octad_v (p : OctadParameters) (x y : Omega) (hxy : x ≠ y) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison (rOctad p))
      (v x y hxy) = 0 :=
  form_different_shapes (i := .octad) (j := .pureFour) (by decide)
    (rOctad_hasShape p) (rv_hasShape x y hxy)

private theorem form_odd_u (x : Omega) (d : ParkerLoop) (y z : Omega) (hyz : y ≠ z) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison (rOdd x d))
      (u y z hyz) = 0 :=
  form_different_shapes (i := .odd) (j := .pureFour) (by decide)
    (rOdd_hasShape x d) (ru_hasShape y z hyz)

private theorem form_odd_v (x : Omega) (d : ParkerLoop) (y z : Omega) (hyz : y ≠ z) :
    shortForm sourceLatticeComparison (shortVector sourceLatticeComparison (rOdd x d))
      (v y z hyz) = 0 :=
  form_different_shapes (i := .odd) (j := .pureFour) (by decide)
    (rOdd_hasShape x d) (rv_hasShape y z hyz)

theorem summandGenerators_orthogonal {i j : Summand} (hij : i ≠ j)
    {a b : Space} (ha : a ∈ summandGenerators i) (hb : b ∈ summandGenerators j) :
    shortForm sourceLatticeComparison a b = 0 := by
  cases i <;> cases j
  all_goals try exact (hij rfl).elim
  all_goals obtain ⟨p, rfl⟩ := ha; obtain ⟨q, rfl⟩ := hb
  · exact form_octad_odd p q.1 q.2
  · simp [wPlus, form_octad_u, form_octad_v]
  · simp [wMinus, form_octad_u, form_octad_v]
  · rw [shortForm_symmetric]; exact form_octad_odd q p.1 p.2
  · simp [wPlus, form_odd_u, form_odd_v]
  · simp [wMinus, form_odd_u, form_odd_v]
  · rw [shortForm_symmetric]; simp [wPlus, form_octad_u, form_octad_v]
  · rw [shortForm_symmetric]; simp [wPlus, form_odd_u, form_odd_v]
  · exact form_wPlus_wMinus_all _ _ _ _ _ _
  · rw [shortForm_symmetric]; simp [wMinus, form_octad_u, form_octad_v]
  · rw [shortForm_symmetric]; simp [wMinus, form_odd_u, form_odd_v]
  · rw [shortForm_symmetric]; exact form_wPlus_wMinus_all _ _ _ _ _ _

/-- Distinct source summands are orthogonal for the actual signed-space form. -/
theorem summandSpace_orthogonal {i j : Summand} (hij : i ≠ j)
    {a b : Space} (ha : a ∈ summandSpace i) (hb : b ∈ summandSpace j) :
    shortForm sourceLatticeComparison a b = 0 := by
  have hright (x : Space) (hx : x ∈ summandGenerators i) :
      summandSpace j ≤ (shortForm sourceLatticeComparison x).ker := by
    apply Submodule.span_le.mpr
    intro y hy
    exact summandGenerators_orthogonal hij hx hy
  have hleft : summandSpace i ≤ ((shortForm sourceLatticeComparison).flip b).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    exact hright x hx hb
  exact hleft ha

theorem u_mem_plus_sup_minus (x y : Omega) (hxy : x ≠ y) :
    u x y hxy ∈ plusSpace ⊔ minusSpace := by
  have hp : wPlus x y hxy ∈ plusSpace ⊔ minusSpace :=
    Submodule.mem_sup_left (Submodule.subset_span ⟨⟨(x,y), hxy⟩, rfl⟩)
  have hm : wMinus x y hxy ∈ plusSpace ⊔ minusSpace :=
    Submodule.mem_sup_right (Submodule.subset_span ⟨⟨(x,y), hxy⟩, rfl⟩)
  have h := (plusSpace ⊔ minusSpace).smul_mem (1 / 2 : ℝ)
    ((plusSpace ⊔ minusSpace).sub_mem hp hm)
  rw [wPlus_sub_wMinus, smul_smul] at h
  norm_num at h ⊢
  exact h

theorem v_mem_plus_sup_minus (x y : Omega) (hxy : x ≠ y) :
    v x y hxy ∈ plusSpace ⊔ minusSpace := by
  have hp : wPlus x y hxy ∈ plusSpace ⊔ minusSpace :=
    Submodule.mem_sup_left (Submodule.subset_span ⟨⟨(x,y), hxy⟩, rfl⟩)
  have hm : wMinus x y hxy ∈ plusSpace ⊔ minusSpace :=
    Submodule.mem_sup_right (Submodule.subset_span ⟨⟨(x,y), hxy⟩, rfl⟩)
  have h := (plusSpace ⊔ minusSpace).smul_mem (1 / 2 : ℝ)
    ((plusSpace ⊔ minusSpace).add_mem hp hm)
  rw [wPlus_add_wMinus, smul_smul] at h
  norm_num at h ⊢
  exact h

theorem summandSpace_iSup : (⨆ i : Summand, summandSpace i) = ⊤ := by
  apply top_unique
  rw [← span_shortVectors]
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  have hpm : plusSpace ⊔ minusSpace ≤ ⨆ i : Summand, summandSpace i :=
    sup_le (le_iSup summandSpace Summand.plus) (le_iSup summandSpace Summand.minus)
  rcases families_exhaustion q with ⟨p, rfl⟩ | ⟨x, d, rfl⟩ | ⟨x, y, hxy, h | h | h | h⟩
  · exact Submodule.mem_iSup_of_mem .octad (Submodule.subset_span ⟨p, rfl⟩)
  · exact Submodule.mem_iSup_of_mem .odd (Submodule.subset_span ⟨(x,d), rfl⟩)
  · subst q; exact hpm (u_mem_plus_sup_minus x y hxy)
  · subst q
    rw [shortVector_sign]
    exact (⨆ i : Summand, summandSpace i).neg_mem (hpm (u_mem_plus_sup_minus x y hxy))
  · subst q; exact hpm (v_mem_plus_sup_minus x y hxy)
  · subst q
    rw [shortVector_sign]
    exact (⨆ i : Summand, summandSpace i).neg_mem (hpm (v_mem_plus_sup_minus x y hxy))

/-- Orthogonality and positivity make this an internal direct sum. -/
theorem summandSpace_independent : iSupIndep summandSpace := by
  rw [iSupIndep_def]
  intro i
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  have hker : (⨆ (j) (_ : j ≠ i), summandSpace j) ≤
      (shortForm sourceLatticeComparison x).ker := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    intro y hy
    exact summandSpace_orthogonal hji.symm hx hy
  have hzero : shortForm sourceLatticeComparison x x = 0 := hker hy
  by_contra hne
  have hpos := shortForm_pos sourceLatticeComparison x hne
  linarith

/-- The orthogonal splitting in 27.8(5), with its octad, odd and two `w` spans. -/
theorem shortSpace_splitting : DirectSum.IsInternal summandSpace :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    summandSpace_independent summandSpace_iSup

/-- Addition identifies the four source summands with the whole short space. -/
def shortSpace_sumEquiv : (⨁ i : Summand, summandSpace i) ≃ₗ[ℝ] Space :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap summandSpace) shortSpace_splitting

@[simp] theorem shortSpace_sumEquiv_lof (i : Summand) (a : summandSpace i) :
    shortSpace_sumEquiv (DirectSum.lof ℝ Summand (fun j => summandSpace j) i a) = a :=
  DirectSum.coeLinearMap_lof summandSpace i a

end Sporadic.Monster.Construction.LocalC.ShortFamilies
