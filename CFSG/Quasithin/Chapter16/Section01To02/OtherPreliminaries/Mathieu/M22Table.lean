module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry

/-!
# Intrinsic M₂₂ table infrastructure

The source row 16.1.5(5), printed p.1171, uses actual kernel and quotient
groups.  This module records the two reusable constructions needed by its
assembly: turning a surjective homomorphism with a specified kernel into a
`GroupExtension`, and excluding components from a self-centralizing normal
two-kernel.  The latter is instantiated for every inner M₂₂ involution using
the checked fixed-hexad kernel.  The outer quotient rows and the full
involution classification remain model calculations for the source assembly.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

open Subgroup Theory.GroupTheory Sporadic.Mathieu
open scoped Pointwise

/-- Package a specified kernel equivalence as an actual group extension. -/
noncomputable def m22_groupExtension_of_surjective_kernel_equiv
    {N E Q : Type*} [Group N] [Group E] [Group Q]
    (f : E →* Q) (hf : Function.Surjective f)
    (e : N ≃* f.ker) : GroupExtension N E Q where
  inl := f.ker.subtype.comp e.toMonoidHom
  rightHom := f
  inl_injective := f.ker.subtype_injective.comp e.injective
  range_inl_eq_ker_rightHom := by
    apply le_antisymm
    · intro x hx
      rcases MonoidHom.mem_range.mp hx with ⟨y, rfl⟩
      change f.ker.subtype (e y) ∈ f.ker
      exact (e y).property
    · intro x hx
      obtain ⟨y, hy⟩ := e.surjective ⟨x, hx⟩
      apply MonoidHom.mem_range.mpr
      refine ⟨y, ?_⟩
      change (e y : E) = x
      exact congrArg Subtype.val hy
  rightHom_surjective := hf

/-- A self-centralizing normal two-kernel excludes every component. -/
theorem m22_no_component_of_normal_selfCentralizing_twoSubgroup
    {C : Type*} [Group C] [Finite C]
    (Q : Subgroup C) (hQn : Q.Normal) (hQp : IsPGroup 2 Q)
    (hself : centralizer (Q : Set C) ≤ Q) (K : Subgroup C) :
    ¬ IsComponent C K := by
  let _ := hQn
  intro hK
  let _ := hK.2
  let _ : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let _ : Nontrivial K :=
    (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKQ : K ≤ Q := by
    rcases hK.normal_dichotomy Q with hle | hc
    · exact hle
    · exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans hself
  let _ : Group.IsNilpotent K := (hQp.to_le hKQ).isNilpotent
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- Every inner M₂₂ involution centralizer has no components. -/
theorem m22_inner_fixedSubgroup_no_components (g : M22) (hg : orderOf g = 2) :
    ¬ ∃ K, IsComponent (MulAut.conj g).fixedSubgroup K := by
  rw [MulAut.fixedSubgroup_conj]
  let B : Finset (Fin 22) := m22FixedPoints g
  let Q₀ : Subgroup M22 := m22HexadPointwiseKernel B
  let C : Subgroup M22 := centralizer ({g} : Set M22)
  let Q : Subgroup C := Q₀.subgroupOf C
  have hB : B ∈ m22Blocks := by
    simpa [B] using m22FixedPoints_mem_blocks g hg
  have hQn : Q.Normal := by
    simpa [Q, Q₀, C, B] using m22FixedPoints_kernel_normal g hg
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (Q₀.subgroupOf C)
    rw [show Q₀.subgroupOf C = comap C.subtype Q₀ from rfl]
    exact (m22HexadPointwiseKernel_isTwoGroup hB).comap_subtype
  have hself : centralizer (Q : Set C) ≤ Q := by
    intro x hx
    have hcomm : (x : M22) ∈ centralizer (Q₀ : Set M22) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hyC : y ∈ C :=
        (m22FixedPoints_kernel_le_centralizer g hg) hy
      let y' : Q := ⟨⟨y, hyC⟩, hy⟩
      have hxy := hx y' y'.property
      exact congrArg Subtype.val hxy
    have hxQ₀ : x.1 ∈ Q₀ :=
      m22HexadPointwiseKernel_selfCentralizing hB hcomm
    change (x : M22) ∈ Q₀
    exact hxQ₀
  intro h
  obtain ⟨K, hK⟩ := h
  exact m22_no_component_of_normal_selfCentralizing_twoSubgroup Q hQn hQp hself K hK

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
