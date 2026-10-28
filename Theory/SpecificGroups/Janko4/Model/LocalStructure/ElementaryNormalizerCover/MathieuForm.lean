module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.FormReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuBranch
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.HallActors

/-!
# The intrinsic zero form on the native Mathieu kernel

The marked second-class seed is orthogonal to the whole native kernel E: every
kernel element belongs to the actual residual of its full centralizer. The
intrinsic form radical is normalized by max1, and E is the normal closure of
this very seed inside max1. Consequently the radical equals E and the intrinsic
form is zero, without any additional finite certificate or supplied form.

Restriction and ambient conjugation give zero form for every subgroup of every
E-conjugate. A nontrivial nonsingular elementary subgroup therefore has nontrivial
image under the literal Mathieu quotient whenever it is placed in max1. This
supplies the nontrivial-image premise at the start of the nonsingular image
analysis; the remaining image configurations and their centralizers still need
their source calculations.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Corollary 1.1.4,
p.487, and Sections 2.2--2.3, pp.489--492. The seed and its normal closure are
the certified ATLAS max1 words, and residual membership uses the full ambient
second involution centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB

instance embeddedKernel_elementary : IsElementaryAbelian 2 embeddedKernel := by
  let : IsElementaryAbelian 2 kernel := localKernel_elementary _ _
  exact IsElementaryAbelian.map max1.subtype

/-- Normal generation by the second-class seed puts the whole native Mathieu
kernel in the radical of its intrinsic form. -/
theorem embeddedKernel_formRadical_eq : formRadical embeddedKernel = embeddedKernel := by
  apply le_antisymm (formRadical_le _)
  have hnorm : max1 ≤ normalizer (formRadical embeddedKernel : Set Model) := by
    rw [← embedded_localKernel_normalizer_eq_max1]
    exact normalizer_le_formRadical_normalizer _
  let : ((formRadical embeddedKernel).subgroupOf max1).Normal :=
    normal_subgroupOf_of_le_normalizer hnorm
  have hseed : (InvolutionCentralizers.Second.seed : Model) ∈ formRadical embeddedKernel := by
    refine ⟨mem_map_of_mem _ (Cardinality.localKernelSeed_mem _ _), ?_⟩
    intro y hy
    obtain ⟨u,hu,rfl⟩ := hy
    apply (outerValue_eq_zero_iff _ _ ?_).mpr (innerRelated_second_kernel u hu)
    intro he
    have ho := InvolutionCentralizers.Second.seed_order
    simp [he] at ho
  have hk : kernel ≤ (formRadical embeddedKernel).subgroupOf max1 := by
    apply normalClosure_le_normal
    rw [Set.singleton_subset_iff]
    exact hseed
  intro z hz
  obtain ⟨u,hu,rfl⟩ := hz
  exact hk hu

/-- The actual order-2048 kernel has zero intrinsic form; this is not an
arbitrary alternating form chosen on an abstract elementary carrier. -/
theorem embeddedKernel_intrinsicForm_zero : intrinsicElementaryForm embeddedKernel = 0 := by
  ext x y
  have hx : (x.toMul : Model) ∈ formRadical embeddedKernel :=
    embeddedKernel_formRadical_eq.symm ▸ x.toMul.property
  exact hx.2 y.toMul y.toMul.property

/-- Every subgroup of a literal conjugate of the native kernel has zero form. -/
theorem intrinsicForm_zero_of_le_conjugate_kernel
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (g : Model)
    (hXE : X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom) :
    intrinsicElementaryForm X = 0 := by
  ext x y
  obtain ⟨u,hu,heu⟩ := hXE x.toMul.property
  obtain ⟨v,hv,hev⟩ := hXE y.toMul.property
  change outerValue x.toMul y.toMul = 0
  rw [← heu,← hev]
  change outerValue ((MulAut.conj g) u) ((MulAut.conj g) v) = 0
  rw [outerValue_equiv]
  have hh := congrArg (fun B : LinearMap.BilinForm (ZMod 2) (Additive embeddedKernel) =>
    B (Additive.ofMul ⟨u,hu⟩) (Additive.ofMul ⟨v,hv⟩)) embeddedKernel_intrinsicForm_zero
  exact hh

/-- A nontrivial nonsingular elementary group cannot lie in any native E-conjugate. -/
theorem nonsingular_not_le_conjugate_kernel
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hX : X ≠ ⊥)
    (hns : (intrinsicElementaryForm X).Nondegenerate) (g : Model) :
    ¬ X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom := by
  intro hXE
  have hz := intrinsicForm_zero_of_le_conjugate_kernel X g hXE
  apply hX
  apply eq_bot_iff.mpr
  intro x hx
  have he := hns.1 (Additive.ofMul (⟨x,hx⟩ : X)) (by intro y; simp only [hz,LinearMap.zero_apply])
  exact mem_bot.mpr (congrArg (fun w : Additive X => (w.toMul : Model)) he)

/-- In the actual Mathieu quotient used by KW Section 2.3, the image of a
nontrivial nonsingular subgroup is nontrivial. Both maps are literal. -/
theorem nonsingular_mathieu_image_ne_bot
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hX : X ≠ ⊥)
    (hns : (intrinsicElementaryForm X).Nondegenerate) (hXM : X ≤ max1) :
    (X.subgroupOf max1).map MathieuHallActors.projection ≠ ⊥ := by
  intro hz
  have hk := (Subgroup.map_eq_bot_iff _).mp hz
  rw [MathieuHallActors.projection_ker] at hk
  have hXE : X ≤ embeddedKernel := by
    intro x hx
    exact mem_map_of_mem max1.subtype (hk (show (⟨x,hXM hx⟩ : max1) ∈ X.subgroupOf max1 from hx))
  apply nonsingular_not_le_conjugate_kernel X hX hns 1
  have hid : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by
    ext z
    simp
  rw [hid,map_id]
  exact hXE

end Janko4.LocalStructure.ElementaryNormalizerCover
