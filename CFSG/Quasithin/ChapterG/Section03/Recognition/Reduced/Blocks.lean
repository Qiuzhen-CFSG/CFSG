module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced
public import CFSG.Quasithin.ChapterG.Section03.Recognition.Boundary
public import CFSG.Quasithin.ChapterG.Section03.Decomposition.OrbitGeometry
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# Reduction of canonical blocks to faithful root orbits

Each canonical block is already an orbit of its own root-generated group.
Cross-fixation, proved using the intrinsic TI-pair theorem, puts its restriction
kernel in the normal binary radical of the total orbit span. Therefore the
trivial-two-core hypothesis makes the actual block restriction faithful.

The block group is normal in the generated group, which is normal in the
original group. These two relative-normality steps, followed by the faithful
restriction isomorphism, justify triviality of the two-core of the block image.
Its centers form a spanning orbit, generate the image through actual roots,
and retain the source lower bound of four on every root-group order.
None of these reductions assumes full action, decomposition, or semisimplicity.

Source: Aschbacher--Smith G.3.1, printed pp.337--338, with the separate
trivial-two-core guard for the actual faithful acting group.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)} {Δ : Set V}

/-- The source quotient-rank hypothesis forces at least four actual roots. -/
theorem source_large_roots [Finite G] (h : Hypotheses G Δ) {x : V} (hx : x ∈ Δ) :
    2 < Nat.card (rootGroup G x) := by
  let f : rootGroup G x → rootQuotientImage G x := fun a =>
    ⟨QuotientGroup.mk' (pCore 2 G) ⟨a.val, a.property.1⟩,
      ⟨⟨a.val, a.property.1⟩, a.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, hay⟩ := y.property
    exact ⟨⟨a.val, ha⟩, Subtype.ext hay⟩
  have hc : Nat.card (rootQuotientImage G x) ≤ Nat.card (rootGroup G x) :=
    Nat.card_le_card_of_surjective f hf
  let : IsElementaryAbelian 2 (rootQuotientImage G x) :=
    rootQuotientImage_elementaryAbelian G x
  by_contra hn
  have hr := IsElementaryAbelian.rank_le_of_card_le (p := 2) (n := 1)
    (rootQuotientImage G x) (hc.trans (not_lt.mp hn))
  have := h.rank_gt_one x hx
  omega

/-- A canonical block is already an orbit of its own root-generated group. -/
theorem block_eq_own_orbit [Finite G] (h : Hypotheses G Δ)
    (i : OrbitBlock G Δ) {x : V} (hx : x ∈ i.val) :
    i.val = MulAction.orbit (blockGroup G Δ i) x := by
  have hstable (b : GL V) (hb : b ∈ blockGroup G Δ i) {z : V} (hz : z ∈ i.val) :
      b z ∈ i.val := DecompositionProof.block_mem_smul i hz
        ⟨b, blockGroup_le_generated h i hb⟩
  have hrep (g : GL V) (hg : g ∈ generated G Δ) :
      ∃ b ∈ blockGroup G Δ i, ∀ z ∈ i.val, b z = g z := by
    refine Subgroup.iSup_induction _
      (C := fun g : GL V => ∃ b ∈ blockGroup G Δ i, ∀ z ∈ i.val, b z = g z)
      hg ?_ ⟨1, (blockGroup G Δ i).one_mem, by intro z hz; rfl⟩ ?_
    · intro y a ha
      refine Subgroup.iSup_induction _
        (C := fun g : GL V => ∃ b ∈ blockGroup G Δ i, ∀ z ∈ i.val, b z = g z)
        ha ?_ ⟨1, (blockGroup G Δ i).one_mem, by intro z hz; rfl⟩ ?_
      · intro hy t ht
        by_cases hyi : y ∈ i.val
        · exact ⟨t, rootGroup_le_generated G hyi ht, by intro z hz; rfl⟩
        · exact ⟨1, (blockGroup G Δ i).one_mem,
            fun z hz => (h.root_fixes_other_block i hy hyi ht z hz).symm⟩
      · rintro a b ⟨a', ha', hea⟩ ⟨b', hb', heb⟩
        refine ⟨a' * b', (blockGroup G Δ i).mul_mem ha' hb', ?_⟩
        intro z hz
        change a' (b' z) = a (b z)
        rw [hea _ (hstable b' hb' hz), heb z hz]
    · rintro a b ⟨a', ha', hea⟩ ⟨b', hb', heb⟩
      refine ⟨a' * b', (blockGroup G Δ i).mul_mem ha' hb', ?_⟩
      intro z hz
      change a' (b' z) = a (b z)
      rw [hea _ (hstable b' hb' hz), heb z hz]
  ext y
  constructor
  · intro hy
    rw [orbitBlock_eq_orbit i hx] at hy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    obtain ⟨b, hb, he⟩ := hrep g.val g.property
    exact MulAction.mem_orbit_iff.mpr ⟨⟨b, hb⟩, he x hx⟩
  · intro hy
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hy
    exact hstable g.val g.property hx

/-- Even before recognition, the kernel of a block action lies in `O₂(G)`. -/
theorem block_kernel_mem_twoCore [Finite G] (h : Hypotheses G Δ)
    (i : OrbitBlock G Δ) (g : blockGroup G Δ i)
    (hg : spanAction G i.val g = 1) :
    (⟨g.val, generated_le G i.val g.property⟩ : G) ∈ pCore 2 G := by
  apply h.radical_span_le_twoCore
  refine ⟨?_, fun v => (Submodule.span_mono (block_subset h i))
    (generated_le_quotientFixer G i.val g.property v)⟩
  have hfix : ∀ v ∈ blockSpace G Δ i, g.val v = v := by
    intro v hv
    exact congrArg (fun e : GL (blockSpace G Δ i) => (e ⟨v, hv⟩ : V)) hg
  have hle : (⨆ j : OrbitBlock G Δ, blockSpace G Δ j) ≤
      g.val.toLinearMap.eqLocus LinearMap.id := by
    apply iSup_le
    intro j v hv
    by_cases hij : i = j
    · subst j
      exact hfix v hv
    · exact DecompositionProof.blocks_cross_fix h hij g.val g.property v hv
  rw [DecompositionProof.blocks_span h] at hle
  exact hle

/-- The two-core guard makes the actual restriction to every block faithful. -/
theorem blockAction_injective [Finite G] (h : Hypotheses G Δ)
    (hcore : pCore 2 G = ⊥) (i : OrbitBlock G Δ) :
    Function.Injective (spanAction G i.val) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  have hm := block_kernel_mem_twoCore h i g hg
  rw [hcore, Subgroup.mem_bot] at hm
  exact Subtype.ext (congrArg (fun z : G => z.val) hm)

private theorem core_eq_bot_of_normal {E : Type*} [Group E]
    (h : pCore 2 E = ⊥) (N : Subgroup E) [N.Normal] : pCore 2 N = ⊥ := by
  have hn : ((pCore 2 N).map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hl : (pCore 2 N).map N.subtype ≤ pCore 2 E :=
    le_sSup ⟨hn, pCore_isPGroup.map N.subtype⟩
  apply (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp
  exact bot_unique (hl.trans_eq h)

private theorem core_eq_bot_of_equiv {E F : Type*} [Group E] [Group F]
    (e : E ≃* F) (h : pCore 2 E = ⊥) : pCore 2 F = ⊥ := by
  rw [← pCore_map_iso 2 e, h, Subgroup.map_bot]

/-- The guard descends to the generated group by relative normality. -/
theorem generated_twoCore_eq_bot [Finite G] (h : Hypotheses G Δ)
    (hcore : pCore 2 G = ⊥) : pCore 2 (generated G Δ) = ⊥ := by
  let N := (generated G Δ).subgroupOf G
  let : N.Normal := generated_normal G Δ h.stable
  exact core_eq_bot_of_equiv (Subgroup.subgroupOfEquivOfLe (generated_le G Δ))
    (core_eq_bot_of_normal hcore N)

/-- Each block group is normal inside the generated group, not necessarily in `G`. -/
theorem block_normal [Finite G] (h : Hypotheses G Δ) (i : OrbitBlock G Δ) :
    ((blockGroup G Δ i).subgroupOf (generated G Δ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (blockGroup_le_generated h i)]
  intro a g ha hg
  have hle : blockGroup G Δ i ≤ (blockGroup G Δ i).comap
      (MulAut.conj g).toMonoidHom := by
    apply iSup_le
    intro x
    apply iSup_le
    intro hx t ht
    exact rootGroup_le_generated G
      (DecompositionProof.block_mem_smul i hx ⟨g, hg⟩)
      (conjugate_mem_rootGroup (generated_le G Δ hg) ht)
  exact hle ha

/-- Two relative-normality steps justify the two-core guard for each block. -/
theorem block_twoCore_eq_bot [Finite G] (h : Hypotheses G Δ)
    (hcore : pCore 2 G = ⊥) (i : OrbitBlock G Δ) :
    pCore 2 (blockGroup G Δ i) = ⊥ := by
  let N := (blockGroup G Δ i).subgroupOf (generated G Δ)
  let : N.Normal := block_normal h i
  exact core_eq_bot_of_equiv (Subgroup.subgroupOfEquivOfLe (blockGroup_le_generated h i))
    (core_eq_bot_of_normal (generated_twoCore_eq_bot h hcore) N)

/-- The faithful block action image has trivial two-core. -/
theorem blockImage_twoCore_eq_bot [Finite G] (h : Hypotheses G Δ)
    (hcore : pCore 2 G = ⊥) (i : OrbitBlock G Δ) :
    pCore 2 (spanAction G i.val).range = ⊥ :=
  core_eq_bot_of_equiv (MonoidHom.ofInjective (blockAction_injective h hcore i))
    (block_twoCore_eq_bot h hcore i)

/-- The centers as vectors of the actual block span. -/
def blockCenters (i : OrbitBlock G Δ) : Set (Submodule.span (ZMod 2) i.val) :=
  {x | x.val ∈ i.val}

/-- Each canonical block supplies a finite, faithful root-generated spanning orbit. -/
theorem block_rootGeneratedOrbit [Finite G] (h : Hypotheses G Δ)
    (hcore : pCore 2 G = ⊥) (i : OrbitBlock G Δ) :
    RootGeneratedOrbit (spanAction G i.val).range (blockCenters i) := by
  let W := Submodule.span (ZMod 2) i.val
  let B := (spanAction G i.val).range
  let : Finite B := Finite.of_surjective (spanAction G i.val).rangeRestrict
    (spanAction G i.val).rangeRestrict_surjective
  have hroot {x : V} (hx : x ∈ i.val) {a : GL V} (ha : a ∈ rootGroup G x) :
      spanAction G i.val ⟨a, rootGroup_le_generated G hx ha⟩ ∈
        rootGroup B (⟨x, Submodule.subset_span hx⟩ : W) := by
    refine ⟨⟨⟨a, rootGroup_le_generated G hx ha⟩, rfl⟩, ?_, ?_⟩
    · intro v hv
      rcases (mem_centerLine_iff (⟨x, Submodule.subset_span hx⟩ : W) v).mp hv with rfl | rfl
      · exact map_zero _
      · exact Subtype.ext (ha.2.1 x (Submodule.mem_span_singleton_self x))
    · intro v
      apply (mem_centerLine_iff _ _).mpr
      rcases (mem_centerLine_iff x (a v - v)).mp (ha.2.2 v) with hz | hz
      · exact Or.inl (Subtype.ext hz)
      · exact Or.inr (Subtype.ext hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx he
    exact h.nonzero x.val (block_subset h i hx) (congrArg Subtype.val he)
  · obtain ⟨x, hxΔ, hi⟩ := i.property
    have hx : x ∈ i.val := hi ▸ MulAction.mem_orbit_self x
    refine ⟨⟨x, Submodule.subset_span hx⟩, ?_⟩
    ext y
    constructor
    · intro hy
      change y.val ∈ i.val at hy
      have hy' := (congrArg (fun S : Set V => y.val ∈ S)
        (block_eq_own_orbit h i hx)).mp hy
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy'
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨spanAction G i.val g, g, rfl⟩, Subtype.ext hg⟩
    · intro hy
      obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hy
      obtain ⟨g, hg⟩ := a.property
      change y.val ∈ i.val
      apply (congrArg (fun S : Set V => y.val ∈ S)
        (block_eq_own_orbit h i hx)).mpr
      refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
      change a.val ⟨x, Submodule.subset_span hx⟩ = y at ha
      rw [← hg] at ha
      exact congrArg Subtype.val ha
  · apply Submodule.map_injective_of_injective W.subtype_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have he : W.subtype '' blockCenters i = i.val := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
    rw [he]
  · apply le_antisymm (generated_le _ _)
    let K := generated B (blockCenters i)
    have hle : generated G i.val ≤
        (K.comap (spanAction G i.val)).map (generated G i.val).subtype := by
      apply iSup_le
      intro x
      apply iSup_le
      intro hx a ha
      exact ⟨⟨a, rootGroup_le_generated G hx ha⟩,
        rootGroup_le_generated B (show (⟨x, Submodule.subset_span hx⟩ : W) ∈ blockCenters i from hx)
          (hroot hx ha), rfl⟩
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, ha, hag⟩ := hle g.property
    have he : a = g := Subtype.ext hag
    exact he ▸ ha
  · intro x hx
    let j : rootGroup G x.val → rootGroup B x := fun a =>
      ⟨spanAction G i.val ⟨a.val, rootGroup_le_generated G hx a.property⟩,
        hroot hx a.property⟩
    have hj : Function.Injective j := by
      intro a b hab
      have he := blockAction_injective h hcore i (congrArg Subtype.val hab)
      exact Subtype.ext (congrArg (fun z : generated G i.val => z.val) he)
    exact (source_large_roots h (block_subset h i hx)).trans_le
      (Nat.card_le_card_of_injective j hj)

end CFSG.Quasithin.ChapterG.Section03.Reduced
