module

public import Theory.Representation.BinaryNaturalDual.FourActors.A2Module.Actors
public import Theory.Representation.BinaryNaturalDual.FourActors.Swapping
public import Theory.Representation.BinaryNaturalDual.RadicalCore

/-!
# Natural geometry forces the mixed actor's dual fixed module

The inputs concern only the natural four-space: a radical two-space, the
fixed spaces of nontransvections, and the three distinct transvection axes.
Rank–nullity makes the natural displacement image of a nontransvection the
whole two-space. Duality then identifies the common dual fixed space with
its annihilator. One nontransvection supplies the entire paired fixed module
as its displacement image. No dual, displacement, or core conclusion is an input.

These are conditional geometric deductions for Aschbacher–Smith H.9.3(6),
printed pp.391–392 (PDF pp.402–403). The source assembly must supply Geometry.
-/

@[expose] public section
namespace BinaryNaturalDual.FourActors.A2Module.CoreReduction
open BinaryLinear BinaryLinear.OuterCyclic Subgroup

/-- Conditional inputs concerning only the natural four-space. -/
structure Geometry (U : Submodule (ZMod 2) X) : Prop where
  dimension : Module.finrank (ZMod 2) U = 2
  radical : innerPreimage B2 ≤ BinaryLinear.radical U
  other_fixed : ∀ g ∈ innerPreimage B2, g ≠ 1 → ¬ IsTransvection g →
    BinaryNaturalDual.fixedSpace g = U
  marking : ∀ g : G, IsTransvection g ↔
    (linearAlternatingEquiv g).val.cycleType = {2, 2, 2, 2}
  transvection_dimension : ∀ g : G, IsTransvection g →
    Module.finrank (ZMod 2) (BinaryNaturalDual.fixedSpace g) = 3
  distinct_axes : Function.Injective (fun i : Fin 3 => BinaryNaturalDual.fixedSpace (axisLinear i))

namespace Geometry

variable {U : Submodule (ZMod 2) X} (h : Geometry U)

private theorem dimension_X : Module.finrank (ZMod 2) X = 4 := by
  simp [X, BinaryLinear.OuterCyclic.Space]

private theorem dimension_V : Module.finrank (ZMod 2) V = 8 := by
  simp [V, CoordinateSpace, Space, Module.finrank_prod, BinaryLinear.OuterCyclic.Space]

include h

/-- One specified nontransvection in the inner actor. -/
theorem other_exists : ∃ g ∈ innerPreimage B2, g ≠ 1 ∧ ¬ IsTransvection g := by
  refine ⟨linearWord 3, (mem_innerPreimage_B2_iff _).mpr ⟨3, rfl⟩, ?_, ?_⟩
  · intro he
    have := linearWord_injective (he.trans linearWord_zero.symm)
    exact (by decide : (3 : Fin 8) ≠ 0) this
  · have he : linearWord 3 = axisLinear 0 * axisLinear 1 := linearWord_eq_products 3
    rw [he]
    exact axisLinear_mul_not_transvection h.marking (by decide)

/-- The radical fixes U pointwise; any nontransvection cuts the common space down to U. -/
theorem naturalFixed_eq : naturalFixed B2 = U := by
  apply le_antisymm
  · obtain ⟨g, hg, hg1, hgt⟩ := h.other_exists
    intro x hx
    rw [← h.other_fixed g hg hg1 hgt, mem_fixedSpace]
    exact (mem_naturalFixed B2 x).mp hx g hg
  · intro x hx
    exact (mem_naturalFixed B2 x).mpr fun g hg => (h.radical hg).1 x hx

/-- A nontransvection in B2 has all of U as its natural displacement image. -/
theorem other_range_eq {g : G} (hg : g ∈ innerPreimage B2)
    (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    LinearMap.range (g.toLinearMap - LinearMap.id) = U := by
  have hk : (g.toLinearMap - LinearMap.id).ker = U := by
    rw [← h.other_fixed g hg hg1 hgt]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply, sub_eq_zero, mem_fixedSpace]
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, rfl⟩
    exact (h.radical hg).2 x
  · have hr := (g.toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
    rw [hk, h.dimension, dimension_X] at hr
    rw [h.dimension]
    exact Nat.add_right_cancel hr

omit h in
/-- Dual fixed vectors annihilate the literal natural displacement image. -/
theorem dual_fixed_eq_ann_range (g : G) :
    BinaryNaturalDual.fixedSpace g.symm.dualMap =
      (LinearMap.range (g.toLinearMap - LinearMap.id)).dualAnnihilator := by
  ext f
  rw [mem_fixedSpace, Submodule.mem_dualAnnihilator]
  constructor
  · intro hf y hy
    obtain ⟨x, rfl⟩ := hy
    have he := LinearMap.congr_fun hf (g x)
    change f (g.symm (g x)) = f (g x) at he
    simpa only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      map_sub, LinearEquiv.symm_apply_apply, sub_eq_zero] using he.symm
  · intro hf
    apply LinearMap.ext
    intro x
    have he := hf _ (LinearMap.mem_range_self (g.toLinearMap - LinearMap.id) (g.symm x))
    change f (g (g.symm x) - g.symm x) = 0 at he
    change f (g.symm x) = f x
    exact (sub_eq_zero.mp (by simpa only [map_sub, LinearEquiv.apply_symm_apply] using he)).symm

/-- Each nonidentity nontransvection fixes exactly ann(U) on the dual. -/
theorem other_dual_fixed_eq {g : G} (hg : g ∈ innerPreimage B2)
    (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    BinaryNaturalDual.fixedSpace g.symm.dualMap = U.dualAnnihilator := by
  rw [dual_fixed_eq_ann_range, h.other_range_eq hg hg1 hgt]

/-- The common dual fixed space is forced by natural displacements. -/
theorem dualFixed_eq : dualFixed B2 = U.dualAnnihilator := by
  apply le_antisymm
  · obtain ⟨g, hg, hg1, hgt⟩ := h.other_exists
    intro f hf
    rw [← h.other_dual_fixed_eq hg hg1 hgt, mem_fixedSpace]
    exact (mem_dualFixed B2 f).mp hf g hg
  · intro f hf
    apply (mem_dualFixed B2 f).mpr
    intro g hg
    apply (mem_fixedSpace _ _).mp
    rw [dual_fixed_eq_ann_range]
    apply (Submodule.mem_dualAnnihilator f).mpr
    rintro y ⟨x, rfl⟩
    exact (Submodule.mem_dualAnnihilator f).mp hf _ ((h.radical hg).2 x)

/-- The natural and dual common fixed spaces form the actual fixed module. -/
theorem actorFixed_eq (d : CoordinateAction 4) :
    actorFixed d B2 = U.prod U.dualAnnihilator := by
  rw [actorFixed_eq_prod d (A := B2) (show B2 ≤ inner from inf_le_right), h.naturalFixed_eq, h.dualFixed_eq]

theorem naturalFixed_dimension : Module.finrank (ZMod 2) (naturalFixed B2) = 2 := by
  rw [h.naturalFixed_eq, h.dimension]

theorem dualFixed_dimension : Module.finrank (ZMod 2) (dualFixed B2) = 2 := by
  rw [h.dualFixed_eq]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [h.dimension, dimension_X] at hd
  omega

theorem actorFixed_dimension (d : CoordinateAction 4) :
    Module.finrank (ZMod 2) (actorFixed d B2) = 4 := by
  rw [h.actorFixed_eq d, finrank_prod_dualAnnihilator, dimension_X]

theorem other_dual_fixed_eq_common {g : G} (hg : g ∈ innerPreimage B2)
    (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    BinaryNaturalDual.fixedSpace g.symm.dualMap = dualFixed B2 := by
  rw [h.other_dual_fixed_eq hg hg1 hgt, h.dualFixed_eq]

/-- Inner displacements are confined to the four-dimensional common fixed module. -/
theorem inner_displacement_mem (d : CoordinateAction 4) {b : M} (hb : b ∈ B2) (v : V) :
    d.representation b v - v ∈ actorFixed d B2 := by
  obtain ⟨g, rfl⟩ := hb.2
  rw [h.actorFixed_eq d, d.on_inner, naturalDualRepresentation_apply]
  refine ⟨(h.radical hb).2 v.1, ?_⟩
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro x hx
  change v.2 (g.symm x) - v.2 x = 0
  have hi : g.symm x = x := ((BinaryLinear.radical U).inv_mem (h.radical hb)).1 x hx
  rw [hi, sub_self]

/-- The fixed space of each nontransvection is already the common fixed module. -/
theorem other_actor_fixed_eq (d : CoordinateAction 4) {g : G}
    (hg : g ∈ innerPreimage B2) (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    BinaryNaturalDual.fixedSpace (action d (MulAut.conj g)) = actorFixed d B2 := by
  rw [h.actorFixed_eq d]
  rw [← h.other_dual_fixed_eq hg hg1 hgt]
  conv_rhs => lhs; rw [← h.other_fixed g hg hg1 hgt]
  ext ⟨x, f⟩
  simp only [mem_fixedSpace, action_apply, d.on_inner, naturalDualRepresentation_apply,
    Prod.mk.injEq, Submodule.mem_prod]

/-- A single nontransvection supplies the whole inner displacement module. -/
theorem other_actor_range_eq (d : CoordinateAction 4) {g : G}
    (hg : g ∈ innerPreimage B2) (hg1 : g ≠ 1) (hgt : ¬ IsTransvection g) :
    LinearMap.range (d.representation (MulAut.conj g) - LinearMap.id) = actorFixed d B2 := by
  have hk : (d.representation (MulAut.conj g) - LinearMap.id).ker = actorFixed d B2 := by
    rw [← h.other_actor_fixed_eq d hg hg1 hgt]
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, mem_fixedSpace, action_apply]
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, rfl⟩
    exact h.inner_displacement_mem d hg v
  · have hr := (d.representation (MulAut.conj g) - LinearMap.id).finrank_range_add_finrank_ker
    rw [hk, h.actorFixed_dimension d, dimension_V] at hr
    rw [h.actorFixed_dimension d]
    exact Nat.add_right_cancel hr

end Geometry
end BinaryNaturalDual.FourActors.A2Module.CoreReduction
