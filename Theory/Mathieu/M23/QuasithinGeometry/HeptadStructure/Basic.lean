module

public import Theory.Mathieu.M23.QuasithinGeometry.Design

/-!
# Labelled heptad action and its pointwise kernel

The labels identify the chosen heptad with `Fin 7`. Restricting the actual M23
permutations and transporting along this equivalence defines the action, with
its kernel retained both inside the heptad stabilizer and inside M23.
All maps are compatible with the original permutation action.

Source: Aschbacher--Smith, §5.2, notation preceding Lemma 5.2.17.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry
open scoped Pointwise

/-- The kernel of a set action, included into M23, is its pointwise fixer. -/
theorem mem_setAction_ker_map (S : Finset (Fin 23)) (g : M23) :
    g ∈ (setAction S).ker.map (MulAction.stabilizer M23 S).subtype ↔
      ∀ a ∈ S, g • a = a := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_setAction_ker S h).mp hh
  · intro h
    have hg : g ∈ MulAction.stabilizer M23 S := by
      apply MulAction.mem_stabilizer_finset'.mpr
      intro a ha
      rwa [h a ha]
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, (mem_setAction_ker S _).mpr h, rfl⟩

/-- The source labels, as an equivalence onto the chosen heptad. -/
noncomputable def labelEquiv : Fin 7 ≃ omega :=
  Equiv.ofBijective (fun i => ⟨label i, by
    rw [← label_image]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact label.injective (congrArg Subtype.val h)
    · intro a
      have ha : a.val ∈ Finset.univ.image label := by
        simpa only [label_image] using a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩)

@[simp] theorem labelEquiv_apply (i : Fin 7) : (labelEquiv i).val = label i := rfl

/-- The action on the seven source labels. -/
noncomputable def heptadAction : heptadStabilizer →* Equiv.Perm (Fin 7) :=
  labelEquiv.symm.permCongrHom.toMonoidHom.comp (setAction omega)

/-- Transport to labels agrees with the actual permutation in M23. -/
@[simp] theorem heptadAction_apply (g : heptadStabilizer) (i : Fin 7) :
    label (heptadAction g i) = (g : M23) • label i := by
  change (labelEquiv (labelEquiv.symm (setAction omega g (labelEquiv i)))).val = _
  rw [labelEquiv.apply_symm_apply]
  rfl

/-- The pointwise heptad kernel, as a subgroup of the heptad stabilizer. -/
noncomputable def heptadKernel : Subgroup heptadStabilizer := heptadAction.ker

instance heptadKernel_normal : heptadKernel.Normal := MonoidHom.normal_ker _

/-- Labelling does not change the restriction kernel. -/
theorem heptadKernel_eq_ker : heptadKernel = (setAction omega).ker := by
  exact MonoidHom.ker_mulEquiv_comp (setAction omega) labelEquiv.symm.permCongrHom

/-- Pointwise characterization using ambient points. -/
theorem mem_heptadKernel (g : heptadStabilizer) :
    g ∈ heptadKernel ↔ ∀ a ∈ omega, (g : M23) • a = a := by
  rw [heptadKernel_eq_ker]
  exact mem_setAction_ker omega g

/-- Pointwise characterization using the seven source labels. -/
theorem mem_heptadKernel_iff_labels (g : heptadStabilizer) :
    g ∈ heptadKernel ↔ ∀ i, (g : M23) • label i = label i := by
  rw [mem_heptadKernel]
  constructor
  · intro h i
    exact h _ (labelEquiv i).property
  · intro h a ha
    obtain ⟨i, hi⟩ := labelEquiv.surjective ⟨a, ha⟩
    have hi' : label i = a := congrArg Subtype.val hi
    rw [← hi']
    exact h i

/-- The same kernel, included into the actual M23 group. -/
noncomputable def heptadKernelAmbient : Subgroup M23 :=
  heptadKernel.map heptadStabilizer.subtype

theorem heptadKernelAmbient_le : heptadKernelAmbient ≤ heptadStabilizer := by
  rintro g ⟨h, _, rfl⟩
  exact h.property

/-- Membership in the ambient kernel requires exactly pointwise fixation. -/
theorem mem_heptadKernelAmbient (g : M23) :
    g ∈ heptadKernelAmbient ↔ ∀ a ∈ omega, g • a = a := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_heptadKernel h).mp hh
  · intro h
    have hg : g ∈ heptadStabilizer := by
      apply MulAction.mem_stabilizer_finset'.mpr
      intro a ha
      rwa [h a ha]
    exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, (mem_heptadKernel _).mpr h, rfl⟩

/-- Pointwise heptad fixers stabilize every subset of the heptad. -/
theorem heptadKernelAmbient_le_stabilizer {S : Finset (Fin 23)} (hS : S ⊆ omega) :
    heptadKernelAmbient ≤ MulAction.stabilizer M23 S := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  rwa [(mem_heptadKernelAmbient g).mp hg a (hS ha)]

/-- In particular the pointwise kernel is contained in the four-set stabilizer. -/
theorem heptadKernelAmbient_le_fourStabilizer : heptadKernelAmbient ≤ fourStabilizer :=
  heptadKernelAmbient_le_stabilizer lambda_subset_omega

end Sporadic.Mathieu.M23Geometry
