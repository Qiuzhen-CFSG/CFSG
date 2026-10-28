module

public import CFSG.Quasithin.ChapterF.Section02.ExtensionFaithfulness
public import Theory.GroupTheory.HomFromFactorization
import all CFSG.Quasithin.ChapterF.Section02

/-!
# Construction of the amalgam extension

We construct the completion in Aschbacher–Smith, *The Classification of
Quasithin Groups*, F.2.11, printed pp. 268–269, independently of faithfulness.
Source condition (f) is expressed by ambient factorization witnesses and the
intersection equality. Agreement on the intersection lets the least-vertex
action and the inner action descend from a semidirect product at each vertex.
The factorization then proves diagram compatibility and local equivariance.

The vertex images generate exactly `Inn(G) ⊔ image(leastAction)`, which equals
the product in the source because inner automorphisms form a normal subgroup.
The resulting maps supply the interfaces in `ExtensionFaithfulness`; no
faithfulness or centerlessness is needed for this construction.
-/

public section
namespace CFSG.Quasithin.ChapterF
namespace YAmalgam.NormalIn
universe u v w
variable {D : Type u} [PartialOrder D] {Y : Type v} [Group Y]
variable {X : Subgroup Y} {α : YAmalgam D X} {γ : YAmalgam D Y}
variable (h : α.NormalIn γ) {e : D} (he : ∀ d, e ≤ d)
variable {U G : Type w} [Group U] [Group G]
variable (uc : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G)
variable (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ)
variable (hfactor : ∀ d (z : γ.subgroup d), ∃ y : γ.subgroup e,
  ∃ x : α.subgroup d, (y : Y) * (x : X) = (z : Y))
variable (hinter : ∀ d, γ.subgroup e ⊓ (α.subgroup d).map X.subtype =
  (α.subgroup e).map X.subtype)

include hfactor hinter in
private theorem exists_extensionMap (d : D) :
    ∃ ρ : γ.subgroup d →* MulAut G,
      (∀ y, ρ (γ.diagram.map (he d) y) = h.leastAction he uc μ hs y) ∧
      (∀ x, ρ (h.localEquiv d x : γ.subgroup d) = MulAut.conj (μ.map d x)) := by
  let φ : γ.subgroup e →* MulAut (α.subgroup d) :=
    { toFun := fun y => (h.conjugation he y).map d
      map_one' := by rw [map_one]; rfl
      map_mul' := by intros; rw [map_mul]; rfl }
  let j : α.subgroup d →* γ.subgroup d :=
    (localSubgroup (α := α) (γ := γ) d).subtype.comp (h.localEquiv d).toMonoidHom
  apply Theory.GroupTheory.exists_hom_of_factorization φ (γ.diagram.map (he d)) j
    (h.leastAction he uc μ hs) (MulAut.conj.comp (μ.map d))
  · intro y x
    apply Subtype.ext
    change (((h.localEquiv d ((h.conjugation he y).map d x) : γ.subgroup d) : Y)) =
      (y : Y) * ((h.localEquiv d x : γ.subgroup d) : Y) * (y : Y)⁻¹
    simp only [localEquiv_apply, conjugation_apply]
  · intro y x
    change MulAut.conj (μ.map d ((h.conjugation he y).map d x)) = _
    rw [← h.leastAction_map he uc μ hs]
    ext z
    simp only [MonoidHom.comp_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulAut.apply_inv_self]
  · intro y x hyx
    have heq : (y : Y) = ((x : X) : Y) := by
      have hh := congrArg Subtype.val hyx
      change (y : Y) = ((h.localEquiv d x : γ.subgroup d) : Y) at hh
      simpa only [localEquiv_apply] using hh
    have hx : ((x : X) : Y) ∈ (α.subgroup e).map X.subtype := by
      rw [← hinter d]
      exact ⟨heq ▸ y.property, ⟨x, x.property, rfl⟩⟩
    obtain ⟨a, ha, hax⟩ := hx
    let a' : α.subgroup e := ⟨a, ha⟩
    have hy : y = h.leastInclusion a' := by
      apply Subtype.ext
      rw [leastInclusion_apply]
      exact heq.trans hax.symm
    have hx' : x = α.diagram.map (he d) a' := by
      apply Subtype.ext
      exact Subtype.val_injective hax.symm
    rw [hy, h.leastAction_leastInclusion he uc μ hs, hx']
    exact congrArg MulAut.conj (μ.compatible_apply (he d) a').symm
  · intro z
    obtain ⟨y, x, hyx⟩ := hfactor d z
    refine ⟨y, x, ?_⟩
    apply Subtype.ext
    change (y : Y) * ((h.localEquiv d x : γ.subgroup d) : Y) = (z : Y)
    simpa only [localEquiv_apply] using hyx


/-- The extension of the least-vertex action and the local inner action. -/
noncomputable def extensionMap (d : D) : γ.subgroup d →* MulAut G :=
  (h.exists_extensionMap he uc μ hs hfactor hinter d).choose

@[simp] theorem extensionMap_least (d : D) (y : γ.subgroup e) :
    h.extensionMap he uc μ hs hfactor hinter d (γ.diagram.map (he d) y) =
      h.leastAction he uc μ hs y :=
  (h.exists_extensionMap he uc μ hs hfactor hinter d).choose_spec.1 y

@[simp] theorem extensionMap_inner (d : D) (x : α.subgroup d) :
    h.extensionMap he uc μ hs hfactor hinter d (h.localEquiv d x : γ.subgroup d) =
      MulAut.conj (μ.map d x) :=
  (h.exists_extensionMap he uc μ hs hfactor hinter d).choose_spec.2 x

/-- The source formula is independent of the chosen factorization. -/
theorem extensionMap_mul (d : D) (y : γ.subgroup e) (x : α.subgroup d) :
    h.extensionMap he uc μ hs hfactor hinter d
      (γ.diagram.map (he d) y * (h.localEquiv d x : γ.subgroup d)) =
      h.leastAction he uc μ hs y * MulAut.conj (μ.map d x) := by
  rw [map_mul, extensionMap_least, extensionMap_inner]

include hfactor in
private theorem local_factorization (d : D) (z : γ.subgroup d) :
    ∃ y : γ.subgroup e, ∃ x : α.subgroup d,
      γ.diagram.map (he d) y * (h.localEquiv d x : γ.subgroup d) = z := by
  obtain ⟨y, x, hyx⟩ := hfactor d z
  refine ⟨y, x, ?_⟩
  apply Subtype.ext
  change (y : Y) * ((h.localEquiv d x : γ.subgroup d) : Y) = (z : Y)
  simpa only [localEquiv_apply] using hyx

/-- The constructed homomorphisms respect all arrows of the diagram. -/
theorem extensionMap_compatible {d f : D} (hdf : d ≤ f) :
    (h.extensionMap he uc μ hs hfactor hinter f).comp (γ.diagram.map hdf) =
      h.extensionMap he uc μ hs hfactor hinter d := by
  ext z
  obtain ⟨y, x, rfl⟩ := h.local_factorization he hfactor d z
  have hx : γ.diagram.map hdf (h.localEquiv d x : γ.subgroup d) =
      (h.localEquiv f (α.diagram.map hdf x) : γ.subgroup f) := by
    apply Subtype.ext
    change ((h.localEquiv d x : γ.subgroup d) : Y) =
      ((h.localEquiv f (α.diagram.map hdf x) : γ.subgroup f) : Y)
    rw [localEquiv_apply, localEquiv_apply]
    rfl
  simp only [MonoidHom.comp_apply, map_mul, AmalgamDiagram.map_comp_apply,
    hx, extensionMap_least, extensionMap_inner, AmalgamCompletion.compatible_apply]

private theorem localMap_leastConjugation (d : D) (y : γ.subgroup e)
    (n : localSubgroup (α := α) (γ := γ) d) :
    h.localMap μ d (h.localConjugation d (γ.diagram.map (he d) y) n) =
      h.leastAction he uc μ hs y (h.localMap μ d n) := by
  obtain ⟨x, rfl⟩ := (h.localEquiv d).surjective n
  have hx : h.localConjugation d (γ.diagram.map (he d) y) (h.localEquiv d x) =
      h.localEquiv d ((h.conjugation he y).map d x) := by
    apply Subtype.ext
    apply Subtype.ext
    simp only [localConjugation_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      localEquiv_apply, conjugation_apply]
    rfl
  rw [hx, localMap_localEquiv, localMap_localEquiv, leastAction_map]

private theorem localMap_innerConjugation (d : D) (x : α.subgroup d)
    (n : localSubgroup (α := α) (γ := γ) d) :
    h.localMap μ d (h.localConjugation d (h.localEquiv d x : γ.subgroup d) n) =
      MulAut.conj (μ.map d x) (h.localMap μ d n) := by
  have hx : h.localConjugation d (h.localEquiv d x : γ.subgroup d) n =
      h.localEquiv d x * n * (h.localEquiv d x)⁻¹ := by
    apply Subtype.ext
    exact h.localConjugation_apply d _ n
  rw [hx, map_mul, map_mul, map_inv, localMap_localEquiv]
  rfl

/-- Local equivariance, in the precise form used by `extensionMaps_injective`. -/
theorem extensionMap_equivariant (d : D) (z : γ.subgroup d)
    (n : localSubgroup (α := α) (γ := γ) d) :
    h.localMap μ d (h.localConjugation d z n) =
      h.extensionMap he uc μ hs hfactor hinter d z (h.localMap μ d n) := by
  obtain ⟨y, x, rfl⟩ := h.local_factorization he hfactor d z
  rw [map_mul, MulAut.mul_apply, h.localMap_leastConjugation he uc μ hs,
    localMap_innerConjugation, extensionMap_mul, MulAut.mul_apply]


/-- The target group of the extension, before any faithfulness hypothesis. -/
noncomputable def extensionGroup : Subgroup (MulAut G) :=
  (MulAut.conj : G →* MulAut G).range ⊔ (h.leastAction he uc μ hs).range

private theorem extensionMap_mem (d : D) (z : γ.subgroup d) :
    h.extensionMap he uc μ hs hfactor hinter d z ∈ h.extensionGroup he uc μ hs := by
  obtain ⟨y, x, rfl⟩ := h.local_factorization he hfactor d z
  rw [extensionMap_mul]
  apply Subgroup.mul_mem
  · exact (show (h.leastAction he uc μ hs).range ≤ h.extensionGroup he uc μ hs from
      le_sup_right) ⟨y, rfl⟩
  · exact (show (MulAut.conj : G →* MulAut G).range ≤ h.extensionGroup he uc μ hs from
      le_sup_left) ⟨μ.map d x, rfl⟩

/-- The local extension images generate precisely the prescribed target. -/
theorem extensionMap_generated :
    Subgroup.closure (⋃ d, Set.range (h.extensionMap he uc μ hs hfactor hinter d)) =
      h.extensionGroup he uc μ hs := by
  let S := Subgroup.closure (⋃ d, Set.range (h.extensionMap he uc μ hs hfactor hinter d))
  have hmem (d : D) (z : γ.subgroup d) :
      h.extensionMap he uc μ hs hfactor hinter d z ∈ S :=
    Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨d, ⟨z, rfl⟩⟩)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro a ha
    obtain ⟨d, z, rfl⟩ := Set.mem_iUnion.mp ha
    exact h.extensionMap_mem he uc μ hs hfactor hinter d z
  · change (MulAut.conj : G →* MulAut G).range ⊔ (h.leastAction he uc μ hs).range ≤ S
    apply sup_le
    · have hc : Subgroup.closure (⋃ d, Set.range (μ.map d)) ≤
          S.comap (MulAut.conj : G →* MulAut G) := by
        apply (Subgroup.closure_le _).mpr
        intro a ha
        obtain ⟨d, x, rfl⟩ := Set.mem_iUnion.mp ha
        change MulAut.conj (μ.map d x) ∈ S
        rw [← h.extensionMap_inner he uc μ hs hfactor hinter d x]
        exact hmem d _
      rw [μ.generated] at hc
      rintro a ⟨g, rfl⟩
      exact hc (Subgroup.mem_top g)
    · rintro a ⟨y, rfl⟩
      rw [← h.extensionMap_least he uc μ hs hfactor hinter e y]
      exact hmem e _

/-- F.2.11(1), the extension completion; faithfulness is assembled separately. -/
noncomputable def extensionCompletion :
    AmalgamCompletion γ.diagram (h.extensionGroup he uc μ hs) where
  map d := (h.extensionMap he uc μ hs hfactor hinter d).codRestrict _
    (h.extensionMap_mem he uc μ hs hfactor hinter d)
  compatible hdf := by
    apply MonoidHom.ext
    intro z
    apply Subtype.ext
    exact DFunLike.congr_fun (h.extensionMap_compatible he uc μ hs hfactor hinter hdf) z
  generated := by
    apply Subgroup.map_injective (h.extensionGroup he uc μ hs).subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map]
    simp only [Set.image_iUnion, ← Set.range_comp]
    change Subgroup.closure (⋃ d, Set.range (h.extensionMap he uc μ hs hfactor hinter d)) = _
    rw [extensionMap_generated, Subgroup.range_subtype]

@[simp] theorem extensionCompletion_map (d : D) (z : γ.subgroup d) :
    (h.extensionCompletion he uc μ hs hfactor hinter |>.map d z).val =
      h.extensionMap he uc μ hs hfactor hinter d z := by rfl

/-- Every target element has the source's form: an inner automorphism followed
by an element of the least-vertex action. -/
theorem mem_extensionGroup_iff (a : MulAut G) :
    a ∈ h.extensionGroup he uc μ hs ↔
      ∃ g : G, ∃ y : γ.subgroup e,
        MulAut.conj g * h.leastAction he uc μ hs y = a := by
  have hn : (MulAut.conj : G →* MulAut G).range.Normal := by
    constructor
    rintro a ⟨g, rfl⟩ b
    refine ⟨b g, ?_⟩
    ext z
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulAut.apply_inv_self]
  let := hn
  rw [extensionGroup, Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨b, ⟨g, rfl⟩, c, ⟨y, rfl⟩, hbc⟩
    exact ⟨g, y, hbc⟩
  · rintro ⟨g, y, rfl⟩
    exact ⟨_, ⟨g, rfl⟩, _, ⟨y, rfl⟩, rfl⟩

open scoped Pointwise in
/-- The target is the subgroup product `Inn(G) · image(leastAction)` of F.2.11. -/
theorem coe_extensionGroup_eq_product :
    (h.extensionGroup he uc μ hs : Set (MulAut G)) =
      ((MulAut.conj : G →* MulAut G).range : Set (MulAut G)) *
        ((h.leastAction he uc μ hs).range : Set (MulAut G)) := by
  ext a
  rw [Set.mem_mul]
  constructor
  · intro ha
    obtain ⟨g, y, rfl⟩ := (h.mem_extensionGroup_iff he uc μ hs a).mp ha
    exact ⟨_, ⟨g, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨y, rfl⟩, rfl⟩
    exact (h.mem_extensionGroup_iff he uc μ hs _).mpr ⟨g, y, rfl⟩

end YAmalgam.NormalIn
end CFSG.Quasithin.ChapterF
