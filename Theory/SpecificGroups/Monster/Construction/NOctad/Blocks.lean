module

public import Theory.SpecificGroups.Monster.Construction.NOctad.Carrier

/-!
# The orthogonal octad blocks

Each block is the span of the actual vectors whose Parker-loop code is a
fixed weight-eight Golay word. The short-lift class criterion makes different
blocks orthogonal. The vectors span `B_Z`, so positivity gives independence
and the full supremum. This proves the direct-sum decomposition in
29.13(1) without assuming a triality extension or a block-permutation action.

Source: Aschbacher, *Sporadic Groups*, Lemma 29.13(1), printed p. 160.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer
open scoped DirectSum

/-- The source octads, as actual weight-eight Golay words. -/
abbrev Octad := {c : golay // hammingNorm c.val = 8}

/-- The octad underlying a signed source parameter. -/
def parameterOctad (p : OctadParameters) : Octad := ⟨p.c.1, p.octad⟩

/-- The generating source vectors of the block indexed by `c`. -/
def blockGenerators (c : Octad) : Set Space :=
  {v | ∃ p : OctadParameters, p.c.1 = c.val ∧ vector p = v}

/-- The literal subspace `B_{Z,c}` inside `B_Z`. -/
def block (c : Octad) : Submodule ℝ Space := Submodule.span ℝ (blockGenerators c)

theorem vector_mem_block (p : OctadParameters) : vector p ∈ block (parameterOctad p) :=
  Submodule.subset_span ⟨p, rfl, rfl⟩

theorem gamma_vectors_of_code_ne (p q : OctadParameters) (h : p.c.1 ≠ q.c.1) :
    gamma (vector p) (vector q) = 0 :=
  form_vector_eq_zero _ _ (fun he => h ((rOctad_class_eq_iff p q).mp he).1)

theorem blockGenerators_orthogonal {c d : Octad} (h : c ≠ d)
    {v w : Space} (hv : v ∈ blockGenerators c) (hw : w ∈ blockGenerators d) :
    gamma v w = 0 := by
  obtain ⟨p, hp, rfl⟩ := hv
  obtain ⟨q, hq, rfl⟩ := hw
  apply gamma_vectors_of_code_ne
  intro he
  exact h (Subtype.ext (hp.symm.trans (he.trans hq)))

/-- Different octads give orthogonal source blocks. -/
theorem block_orthogonal {c d : Octad} (h : c ≠ d)
    {v w : Space} (hv : v ∈ block c) (hw : w ∈ block d) : gamma v w = 0 := by
  have hright (x : Space) (hx : x ∈ blockGenerators c) : block d ≤ (gamma x).ker := by
    apply Submodule.span_le.mpr
    intro y hy
    exact blockGenerators_orthogonal h hx hy
  have hleft : block c ≤ (gamma.flip w).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    exact hright x hx hw
  exact hleft hv

theorem block_iSup : (⨆ c : Octad, block c) = ⊤ := by
  apply top_unique
  rw [← span_vectors]
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact Submodule.mem_iSup_of_mem (parameterOctad p) (vector_mem_block p)

theorem block_independent : iSupIndep block := by
  rw [iSupIndep_def]
  intro c
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  have hker : (⨆ (d) (_ : d ≠ c), block d) ≤ (gamma x).ker := by
    refine iSup_le fun d => iSup_le fun hdc => ?_
    intro y hy
    exact block_orthogonal hdc.symm hx hy
  have hzero : gamma x x = 0 := hker hy
  by_contra hne
  exact (ne_of_gt (gamma_pos x hne)) hzero

/-- The source direct-sum assertion of 29.13(1). -/
theorem blocks_decomposition : iSupIndep block ∧ (⨆ c : Octad, block c) = ⊤ :=
  ⟨block_independent, block_iSup⟩

/-- The canonical addition map from the source blocks is bijective. -/
theorem blocks_internal : DirectSum.IsInternal block :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (M := Space) (A := block) block_independent block_iSup

/-- Addition identifies the direct sum of the octad blocks with the existing `B_Z`. -/
def blocks_sumEquiv : (⨁ c : Octad, block c) ≃ₗ[ℝ] Space :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap block) blocks_internal

@[simp] theorem blocks_sumEquiv_lof (c : Octad) (v : block c) :
    blocks_sumEquiv (DirectSum.lof ℝ Octad (fun d => block d) c v) = v :=
  DirectSum.coeLinearMap_lof block c v

/-- The actual block inclusion used by the full Griess action assembly. -/
def blockInclusion (c : Octad) : block c →ₗ[ℝ] GriessSpace :=
  inclusion.comp (block c).subtype

theorem blockInclusion_injective (c : Octad) : Function.Injective (blockInclusion c) :=
  inclusion_injective.comp Subtype.val_injective

theorem griessGamma_blocks {c d : Octad} (h : c ≠ d) (v : block c) (w : block d) :
    griessGamma (blockInclusion c v) (blockInclusion d w) = 0 := by
  change griessGamma (inclusion v.val) (inclusion w.val) = 0
  rw [gamma_inclusion]
  exact block_orthogonal h v.prop w.prop

end Sporadic.Monster.Construction.NOctad
