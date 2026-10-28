module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.Representative
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The elementary kernel of an M23 involution centralizer

Restrict the seven-point heptad action to the certified involution centralizer.
The involution belongs to the abelian heptad kernel, so that entire kernel lies
in its centralizer. The restricted kernel is therefore the same concrete E16,
with its binary coordinates and self-centralizing property retained. The known
centralizer order 2688 gives an action image of order 168 and a genuine short
exact sequence. Identification of that image with PSL3(2) is a separate result;
no splitting or isomorphism follows merely from its order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(6),
printed p.1171; the concrete geometry also occurs in 5.2.21, printed p.657.
-/

@[expose] public section
noncomputable section

open Subgroup
namespace Sporadic.Mathieu.M23Geometry.InvolutionCentralizer

/-- Centralizer of the certified eight-transposition involution. -/
abbrev representativeCentralizer := centralizer ({involutionRepresentative} : Set M23)

/-- Every centralizer element preserves the actual fixed heptad. -/
theorem representative_le_heptad : representativeCentralizer ≤ heptadStabilizer := by
  simpa only [fixedHeptad_involutionRepresentative, involutionHeptad, heptadStabilizer,
    omega] using centralizer_le_fixedHeptad_stabilizer involutionRepresentative

/-- Inclusion into the stabilizer of the fixed heptad. -/
def toHeptad : representativeCentralizer →* heptadStabilizer :=
  inclusion representative_le_heptad

/-- The actual centralizer action on the seven labelled fixed points. -/
noncomputable def action : representativeCentralizer →* Equiv.Perm (Fin 7) :=
  heptadAction.comp toHeptad

/-- The pointwise kernel inside the centralizer. -/
noncomputable abbrev kernel := action.ker

/-- The representative involution is itself a binary translation. -/
def markedTranslation : heptadKernel :=
  ⟨⟨involutionRepresentative,
    representative_le_heptad (mem_centralizer_singleton_iff.mpr rfl)⟩, by
      apply (mem_heptadKernel _).mpr
      intro a ha
      exact (involutionRepresentative_fixed_iff a).mpr ha⟩

/-- The abelian heptad kernel centralizes the representative. -/
def kernelInclusion : heptadKernel →* representativeCentralizer where
  toFun u := ⟨u.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg (fun v : heptadKernel => v.val.val)
      (heptadKernel_mul_comm u markedTranslation))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restricting to the centralizer leaves the pointwise heptad kernel intact. -/
noncomputable def kernelEquiv : heptadKernel ≃* kernel where
  toFun u := ⟨kernelInclusion u, u.property⟩
  invFun u := ⟨toHeptad u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Actual elementary abelian coordinates for the centralizer kernel. -/
noncomputable def elementaryKernelEquiv :
    (Fin 4 → Multiplicative (ZMod 2)) ≃* kernel :=
  (MulEquiv.funMultiplicative (Fin 4) (ZMod 2)).symm.trans
    (heptadBinaryEquiv.trans kernelEquiv)

theorem kernel_card : Nat.card kernel = 16 :=
  (Nat.card_congr kernelEquiv.symm.toEquiv).trans heptadKernel_card

theorem kernel_isTwoGroup : IsPGroup 2 kernel :=
  heptadKernel_isTwoGroup.of_surjective kernelEquiv.toMonoidHom kernelEquiv.surjective

/-- Faithfulness of the heptad complement action excludes extra centralizers. -/
theorem kernel_selfCentralizing :
    centralizer (kernel : Set representativeCentralizer) ≤ kernel := by
  intro g hg
  apply heptadKernel_selfCentralizing
  intro u hu
  exact congrArg toHeptad
    (hg (kernelInclusion ⟨u, hu⟩) (show kernelInclusion ⟨u, hu⟩ ∈ kernel from hu))

theorem action_range_card : Nat.card action.range = 168 := by
  have hc := kernel.card_mul_index
  rw [kernel_card, involutionRepresentative_centralizer_card] at hc
  rw [← index_ker]
  change kernel.index = 168
  omega

/-- The exact extension by the actual seven-point action image. -/
noncomputable def extension :
    GroupExtension (Fin 4 → Multiplicative (ZMod 2)) representativeCentralizer action.range where
  inl := kernel.subtype.comp elementaryKernelEquiv.toMonoidHom
  rightHom := action.rangeRestrict
  inl_injective := kernel.subtype_injective.comp elementaryKernelEquiv.injective
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ elementaryKernelEquiv.surjective,
      ← MonoidHom.range_eq_map, range_subtype, MonoidHom.ker_rangeRestrict]
  rightHom_surjective := action.rangeRestrict_surjective

end Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
