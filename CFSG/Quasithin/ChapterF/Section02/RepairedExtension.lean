module

public import CFSG.Quasithin.ChapterF.Section02.ExtensionConstruction

/-!
# The repaired extension theorem for amalgams

This completes the sound replacement for Aschbacher–Smith, *The Classification
of Quasithin Groups*, F.2.11 (printed pp. 268–269), as used in F.4.23(5)
(printed pp. 286–287). The unrestricted printed assertion is false; its formal
counterexample remains in `Section02.Obstruction`.

In addition to source conditions (a)–(f), assume `C_{Y_d}(X_d) ≤ Y_e`.
The constructed extension is locally equivariant, so a kernel element
centralizes the smaller vertex. The extra containment puts it in the least
vertex, where condition (e) makes the descended action faithful. This proves
faithfulness of both the extension and its inner restriction. Centerlessness
is needed only to identify the inner completion with the original completion.

`repairedExtension_of_index_le_two` discharges the extra containment from the
finite two-local conditions used in the exceptional Lie-amalgam application:
the smaller vertices have index at most two and two-group centers, and the
least larger vertex is Sylow. The F.4 consumer supplies these local structural
facts; no extension maps or injectivity conclusions are assumed here.
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

/-- Source condition (d), phrased as invariance of the equivalence class,
supplies exactly the stabilization needed for descent. -/
theorem conjugation_mem_kernelStabilizer
    (hstable : ∀ y, Nonempty (CompletionEquivalence ((h.conjugation he y).act μ) μ)) :
    ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ :=
  fun y => (uc.mem_kernelStabilizer_iff μ _).mpr (hstable y)

variable (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ)
variable (hfactor : ∀ d (z : γ.subgroup d), ∃ y : γ.subgroup e,
  ∃ x : α.subgroup d, (y : Y) * (x : X) = (z : Y))
variable (hinter : ∀ d, γ.subgroup e ⊓ (α.subgroup d).map X.subtype =
  (α.subgroup e).map X.subtype)
variable (hμ : μ.Faithful)
variable (hc : (⨅ d, (Subgroup.centralizer
  (((α.subgroup d).map X.subtype : Subgroup Y) : Set Y)).comap
    (γ.subgroup e).subtype) = ⊥)
variable (hcentralizer : ∀ d, Subgroup.centralizer
  (localSubgroup (α := α) (γ := γ) d : Set (γ.subgroup d)) ≤
    (γ.subgroup e).subgroupOf (γ.subgroup d))

include hμ hc hcentralizer in
/-- The actual constructed extension maps are injective under the repaired
local centralizer hypothesis. -/
theorem extensionMap_injective (d : D) :
    Function.Injective (h.extensionMap he uc μ hs hfactor hinter d) :=
  h.extensionMaps_injective he uc μ hs hμ hc
    (h.extensionMap he uc μ hs hfactor hinter)
    (h.extensionMap_equivariant he uc μ hs hfactor hinter)
    (h.extensionMap_least he uc μ hs hfactor hinter) hcentralizer d

include hμ hc hcentralizer in
/-- Repaired F.2.11(1): the constructed completion is faithful. -/
theorem extensionCompletion_faithful :
    (h.extensionCompletion he uc μ hs hfactor hinter).Faithful := by
  intro d x y hxy
  apply h.extensionMap_injective he uc μ hs hfactor hinter hμ hc hcentralizer d
  simpa only [extensionCompletion_map] using congrArg Subtype.val hxy

/-- F.2.11(2): restriction of the constructed completion is the inner action. -/
theorem extensionCompletion_inner (d : D) (x : α.subgroup d) :
    ((h.extensionCompletion he uc μ hs hfactor hinter).map d
      (h.localEquiv d x : γ.subgroup d)).val = (μ.innerCompletion.map d x).val := by
  rw [extensionCompletion_map, extensionMap_inner, AmalgamCompletion.innerCompletion_map]

include h he uc hs hfactor hinter hμ hc hcentralizer in
/-- Repaired F.2.11(3): the inner restriction is a faithful completion even
without centerlessness of the whole completion group. -/
theorem innerCompletion_faithful_of_localCentralizer : μ.innerCompletion.Faithful :=
  h.innerCompletion_faithful_of_extensionMaps μ
    (h.extensionMap he uc μ hs hfactor hinter)
    (h.extensionMap_injective he uc μ hs hfactor hinter hμ hc hcentralizer)
    (h.extensionMap_inner he uc μ hs hfactor hinter)

include hμ hc hcentralizer in
/-- All four conclusions of the sound replacement for F.2.11. The target is
`Inn(G) · image(leastAction)` by `coe_extensionGroup_eq_product`; its completion
and generating maps are constructed, rather than supplied as hypotheses. -/
theorem repairedExtension :
    (h.extensionCompletion he uc μ hs hfactor hinter).Faithful ∧
    (∀ d (x : α.subgroup d),
      ((h.extensionCompletion he uc μ hs hfactor hinter).map d
        (h.localEquiv d x : γ.subgroup d)).val = MulAut.conj (μ.map d x)) ∧
    μ.innerCompletion.Faithful ∧
    (Subgroup.center G = ⊥ → Nonempty (CompletionEquivalence μ μ.innerCompletion)) := by
  refine ⟨h.extensionCompletion_faithful he uc μ hs hfactor hinter hμ hc hcentralizer,
    ?_, h.innerCompletion_faithful_of_localCentralizer he uc μ hs hfactor hinter
      hμ hc hcentralizer, ?_⟩
  · intro d x
    rw [extensionCompletion_map, extensionMap_inner]
  · intro hz
    exact ⟨μ.equivalenceInnerOfCenterEqBot hz⟩

include hμ hc in
/-- The finite two-local version needed in F.4.23(5). Normality is part of `h`;
the Sylow, index, and center assumptions discharge the repair completely. -/
theorem repairedExtension_of_index_le_two [∀ d, Finite (γ.subgroup d)]
    (hi : ∀ d, (localSubgroup (α := α) (γ := γ) d).index ≤ 2)
    (hz : ∀ d, IsPGroup 2 (Subgroup.center (α.subgroup d)))
    (S : ∀ d, Sylow 2 (γ.subgroup d))
    (hS : ∀ d, (S d : Subgroup (γ.subgroup d)) =
      (γ.subgroup e).subgroupOf (γ.subgroup d)) :
    (h.extensionCompletion he uc μ hs hfactor hinter).Faithful ∧
    (∀ d (x : α.subgroup d),
      ((h.extensionCompletion he uc μ hs hfactor hinter).map d
        (h.localEquiv d x : γ.subgroup d)).val = MulAut.conj (μ.map d x)) ∧
    μ.innerCompletion.Faithful ∧
    (Subgroup.center G = ⊥ → Nonempty (CompletionEquivalence μ μ.innerCompletion)) :=
  h.repairedExtension he uc μ hs hfactor hinter hμ hc
    (fun d => h.localCentralizer_le_of_index_le_two d (hi d) (hz d) (S d) (hS d))

end YAmalgam.NormalIn
end CFSG.Quasithin.ChapterF
