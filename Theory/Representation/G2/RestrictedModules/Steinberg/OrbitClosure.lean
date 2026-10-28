module

public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.Span
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.RootA
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.RootB
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.RootC
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.RootD
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.RootE
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.RootF
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.WeylR
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.WeylS
public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.Torus
public import Theory.AtlasPort.LinearGroups.G2.Generation

/-!
# Full G₂ invariance of the binary highest-weight orbit span

The 64 specified binary translates span an invariant subspace of the actual
natural tensor cube over every field of characteristic two. An explicit change
of spanning family gives sparse homogeneous tensors. Their root, Weyl and torus
actions are certified in the imported calculation modules. The generation
theorem for the full split-octonion automorphism group then proves invariance
under every actual model element.

No independence, dimension, fixed-line assertion or tensor-exhaustivity theorem
is used. This supplies the stability step in the concrete construction of the
level-two Steinberg factor in GLS3 2.8.7 and Example 2.8.10(g), used in the proof
of Aschbacher–Smith G.9.3, printed pp.354,356–357. The natural action and group
generation are those of the attributed ATLAS octonion model.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Restricted.Steinberg
variable (F : Type*) [Field F] [CharP F 2]

namespace OrbitClosure

/-- Preservation in both directions, as a subgroup of the actual model. -/
def sparseStabilizer : Subgroup (Model F) where
  carrier := {g | (∀ v ∈ sparseSpan F, ambientAction F g v ∈ sparseSpan F) ∧
    (∀ v ∈ sparseSpan F, ambientAction F g⁻¹ v ∈ sparseSpan F)}
  one_mem' := by
    constructor <;> intro v hv <;>
      simpa only [inv_one, map_one (ambientAction F), Module.End.one_apply] using hv
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro v hv
      simpa only [map_mul (ambientAction F) g h, Module.End.mul_apply] using
        hg.1 _ (hh.1 _ hv)
    · intro v hv
      simpa only [mul_inv_rev, map_mul (ambientAction F) h⁻¹ g⁻¹,
        Module.End.mul_apply] using hh.2 _ (hg.2 _ hv)
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

private theorem rootA_mem_stabilizer (a : F) : rootA a ∈ sparseStabilizer F := by
  have hi : (rootA a)⁻¹ = rootA a := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootA_add, CharTwo.add_self_eq_zero, rootA_zero]
  exact ⟨rootA_preserves F a, by rw [hi]; exact rootA_preserves F a⟩

private theorem rootB_mem_stabilizer (a : F) : rootB a ∈ sparseStabilizer F := by
  have hi : (rootB a)⁻¹ = rootB a := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootB_add, CharTwo.add_self_eq_zero, rootB_zero]
  exact ⟨rootB_preserves F a, by rw [hi]; exact rootB_preserves F a⟩

private theorem rootC_mem_stabilizer (a : F) : rootC a ∈ sparseStabilizer F := by
  have hi : (rootC a)⁻¹ = rootC a := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootC_add, CharTwo.add_self_eq_zero, rootC_zero]
  exact ⟨rootC_preserves F a, by rw [hi]; exact rootC_preserves F a⟩

private theorem rootD_mem_stabilizer (a : F) : rootD a ∈ sparseStabilizer F := by
  have hi : (rootD a)⁻¹ = rootD a := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootD_add, CharTwo.add_self_eq_zero, rootD_zero]
  exact ⟨rootD_preserves F a, by rw [hi]; exact rootD_preserves F a⟩

private theorem rootE_mem_stabilizer (a : F) : rootE a ∈ sparseStabilizer F := by
  have hi : (rootE a)⁻¹ = rootE a := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootE_add, CharTwo.add_self_eq_zero, rootE_zero]
  exact ⟨rootE_preserves F a, by rw [hi]; exact rootE_preserves F a⟩

private theorem rootF_mem_stabilizer (a : F) : rootF a ∈ sparseStabilizer F := by
  have hi : (rootF a)⁻¹ = rootF a := by
    apply inv_eq_of_mul_eq_one_left
    rw [rootF_add, CharTwo.add_self_eq_zero, rootF_zero]
  exact ⟨rootF_preserves F a, by rw [hi]; exact rootF_preserves F a⟩

private theorem weylR_mem_stabilizer : (weylR : Model F) ∈ sparseStabilizer F := by
  have hi : (weylR : Model F)⁻¹ = weylR :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (weylR_sq (K := F)))
  exact ⟨weylR_preserves F, by rw [hi]; exact weylR_preserves F⟩

private theorem weylS_mem_stabilizer : (weylS : Model F) ∈ sparseStabilizer F := by
  have hi : (weylS : Model F)⁻¹ = weylS :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (weylS_sq (K := F)))
  exact ⟨weylS_preserves F, by rw [hi]; exact weylS_preserves F⟩

private theorem torus_mem_stabilizer (l m : Fˣ) : torus l m ∈ sparseStabilizer F := by
  have hi : (torus l m)⁻¹ = torus l⁻¹ m⁻¹ :=
    (map_inv (torusHom (K := F)) (l, m)).symm
  exact ⟨torus_preserves F l m, by rw [hi]; exact torus_preserves F l⁻¹ m⁻¹⟩

private theorem unipotent_le_stabilizer : unipotent (K := F) ≤ sparseStabilizer F := by
  apply (Subgroup.closure_le (sparseStabilizer F)).mpr
  intro g hg
  rcases hg with (((((hg | hg) | hg) | hg) | hg) | hg)
  all_goals obtain ⟨a, rfl⟩ := hg
  · exact rootA_mem_stabilizer F a
  · exact rootB_mem_stabilizer F a
  · exact rootC_mem_stabilizer F a
  · exact rootD_mem_stabilizer F a
  · exact rootE_mem_stabilizer F a
  · exact rootF_mem_stabilizer F a

private theorem rootWeyl_le_stabilizer : rootWeylSubgroup (K := F) ≤ sparseStabilizer F := by
  apply (Subgroup.closure_le (sparseStabilizer F)).mpr
  rintro g (hg | hg)
  · exact unipotent_le_stabilizer F hg
  · rcases hg with rfl | hg
    · exact weylR_mem_stabilizer F
    · rcases hg with rfl
      exact weylS_mem_stabilizer F

/-- The verified model generation theorem extends the calculations to every automorphism. -/
theorem ambientAction_mem_sparseSpan (g : Model F) (v : Ambient F)
    (hv : v ∈ sparseSpan F) : ambientAction F g v ∈ sparseSpan F := by
  have ht : splitTorus (K := F) ≤ sparseStabilizer F := by
    rintro _ ⟨⟨l, m⟩, rfl⟩
    exact torus_mem_stabilizer F l m
  have hg : g ∈ generated (F := F) := by rw [generated_eq_top]; trivial
  have hs : g ∈ sparseStabilizer F :=
    (show generated (F := F) ≤ sparseStabilizer F from
      sup_le (rootWeyl_le_stabilizer F) ht) hg
  exact hs.1 v hv

end OrbitClosure

/-- The span of the 64 explicit binary translates is invariant under the entire
actual octonion automorphism group, uniformly in characteristic two. -/
theorem ambientAction_mem_binarySpan (g : Model F) (v : Ambient F)
    (hv : v ∈ binarySpan F) : ambientAction F g v ∈ binarySpan F := by
  rw [← OrbitClosure.sparseSpan_eq_binarySpan] at hv ⊢
  exact OrbitClosure.ambientAction_mem_sparseSpan F g v hv

/-- The explicit binary span, now with its genuine whole-group invariance proof. -/
def binarySubrepresentation : Subrepresentation (ambientAction F) where
  toSubmodule := binarySpan F
  apply_mem_toSubmodule g := by
    intro v hv
    exact ambientAction_mem_binarySpan F g v hv

end Atlas.G2.Restricted.Steinberg
