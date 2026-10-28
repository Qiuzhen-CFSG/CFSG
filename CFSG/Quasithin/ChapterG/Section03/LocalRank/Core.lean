module

public import CFSG.Quasithin.ChapterG.Section03.LocalRank.Geometry

/-!
# Block kernels and the intrinsic two-core

A block kernel fixes its own summand and, by the decomposition, every other
summand. It therefore fixes the total span. Its displacement is also in that
span, so it lies in the ambient span radical intersected with `G`. This
intersection is a normal elementary abelian subgroup of `G`, because `G`
stabilizes the total span. Thus it is contained in the intrinsic `O₂(G)`.

Source: Aschbacher--Smith, G.3.1(3), printed pp. 337--338.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03.LocalRank
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem span_stable {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) {g : GL V} (hg : g ∈ G) {v : V}
    (hv : v ∈ Submodule.span (ZMod 2) Δ) :
    g v ∈ Submodule.span (ZMod 2) Δ := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h.stable g hg x hx)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

/-- The binary radical of the total span, intersected with `G`, lies in `O₂(G)`. -/
theorem total_radical_le_pCore {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) :
    (radical (Submodule.span (ZMod 2) Δ)).subgroupOf G ≤ pCore 2 G := by
  let W := Submodule.span (ZMod 2) Δ
  have hpar : G ≤ parabolic W := by
    intro g hg v
    constructor
    · intro hv
      simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
        span_stable h (G.inv_mem hg) hv
    · exact span_stable h hg
  have hn : ((radical W).subgroupOf G).Normal := by
    constructor
    intro n hn g
    exact (Subgroup.le_set_normalizer_iff.mp (parabolic_le_normalizer W))
      g.val (hpar g.property) n.val hn
  let : IsElementaryAbelian 2 ((radical W).subgroupOf G) :=
    elementaryAbelian_of_le_radical
      (G.subtype.comp ((radical W).subgroupOf G).subtype)
      (Subtype.val_injective.comp Subtype.val_injective) W (fun g => g.property)
  exact le_sSup ⟨hn, IsElementaryAbelian.isPGroup 2 _⟩

/-- The pointwise kernel of one factor fixes the full span of the orbit. -/
theorem block_kernel_fixes_total {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (hdec : Decomposition G Δ) (i : OrbitBlock G Δ)
    {g : GL V} (hg : g ∈ blockGroup G Δ i)
    (hfix : ∀ v ∈ blockSpace G Δ i, g v = v) :
    ∀ v ∈ Submodule.span (ZMod 2) Δ, g v = v := by
  have hle : (⨆ j : OrbitBlock G Δ, blockSpace G Δ j) ≤
      g.toLinearMap.eqLocus LinearMap.id := by
    refine iSup_le fun j v hv => ?_
    by_cases hij : i = j
    · subst j
      exact hfix v hv
    · exact hdec.cross_fix i j hij g hg v hv
  rw [hdec.space_span] at hle
  exact hle

/-- Block kernels lie in the actual two-core of `G`. -/
theorem block_kernel_mem_pCore {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hdec : Decomposition G Δ) (i : OrbitBlock G Δ)
    (g : fixingKernel (blockGroup G Δ i) (blockSpace G Δ i)) :
    (⟨g.val.val, generated_le G i.val g.val.property⟩ : G) ∈ pCore 2 G := by
  apply total_radical_le_pCore h
  refine ⟨block_kernel_fixes_total hdec i g.val.property g.property, ?_⟩
  intro v
  exact (Submodule.span_mono (block_subset h i))
    (generated_le_quotientFixer G i.val g.val.property v)

/-- In particular, the kernel of the root restriction is killed by `G → G/O₂(G)`. -/
theorem root_kernel_mem_pCore {G : Subgroup (GL V)} [Finite G] {Δ : Set V}
    (h : Hypotheses G Δ) (hdec : Decomposition G Δ) (i : OrbitBlock G Δ)
    {x : V} (hx : x ∈ i.val)
    (g : fixingKernel (rootGroup G x) (blockSpace G Δ i)) :
    (⟨g.val.val, rootGroup_le G x g.val.property⟩ : G) ∈ pCore 2 G := by
  exact block_kernel_mem_pCore h hdec i
    ⟨⟨g.val.val, rootGroup_le_generated G hx g.val.property⟩, g.property⟩

end CFSG.Quasithin.ChapterG.Section03.LocalRank
