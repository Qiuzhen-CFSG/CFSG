module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Uses the ATLAS exceptional-isomorphism construction, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
import all Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic

/-!
# The marked two-plane under the exceptional A₈ equivalence

The bivector e₀ ∧ e₁ corresponds, in the retained hyperbolic basis of the
ATLAS deleted module, to the class of 11110000. Its linear stabilizer is the
stabilizer of span(e₀,e₁). A permutation fixes its deleted class exactly when
it preserves the unordered partition {0123,4567}.

The internal import is intentional: it proves the action equation for the
existing `alt8EquivPSL4Two`, whose implementation is private, without changing
that shared construction or choosing another exceptional equivalence. Only
the marked equivalence and its subgroup equality are exported here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.32(4), printed pp.1132–1133. The two end nodes of A₃ give the
stabilizer of a two-dimensional subspace.
-/

noncomputable section
open Atlas.Order20160A8 Atlas.Comparisons.Exceptional
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
public abbrev A8 := alternatingGroup (Fin 8)
public abbrev V := Fin 4 → ZMod 2

/-- The coordinate two-plane spanned by e₀ and e₁. -/
public def plane : Submodule (ZMod 2) V where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' hu hv := ⟨by simp [Pi.add_apply, hu.1, hv.1], by simp [Pi.add_apply, hu.2, hv.2]⟩
  smul_mem' a v hv := ⟨by simp [Pi.smul_apply, hv.1], by simp [Pi.smul_apply, hv.2]⟩

private def planeEquiv : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] plane where
  toFun v := ⟨![v 0, v 1, 0, 0], by constructor <;> rfl⟩
  invFun w := ![w.val 0, w.val 1]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv w := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact w.property.1.symm
    · exact w.property.2.symm
  map_add' u v := by apply Subtype.ext; ext i; fin_cases i <;> simp
  map_smul' a v := by apply Subtype.ext; ext i; fin_cases i <;> simp

/-- The marked plane has dimension two, hence is the end-node parabolic plane. -/
public theorem plane_finrank : Module.finrank (ZMod 2) plane = 2 := by
  rw [← planeEquiv.finrank_eq]
  simp

private theorem plane_expansion (v : plane) :
    v.val = v.val 0 • Pi.single 0 1 + v.val 1 • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp [v.property.1, v.property.2]

private theorem mem_parabolic_iff (g : BinaryLinear.GL V) :
    g ∈ BinaryLinear.parabolic plane ↔
      g (Pi.single 0 1) ∈ plane ∧ g (Pi.single 1 1) ∈ plane := by
  constructor
  · intro h
    exact ⟨(h _).mpr (by constructor <;> simp),
      (h _).mpr (by constructor <;> simp)⟩
  · intro h
    have hs (v : plane) : g v.val ∈ plane := by
      rw [plane_expansion v, map_add, map_smul, map_smul]
      exact plane.add_mem (plane.smul_mem _ h.1) (plane.smul_mem _ h.2)
    let f : plane → plane := fun v => ⟨g v.val, hs v⟩
    have hf : Function.Injective f := by
      intro u v he
      exact Subtype.ext (g.injective (congrArg Subtype.val he))
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨g v, hv⟩
      have he : w.val = v := g.injective (congrArg Subtype.val hw)
      exact he ▸ w.property
    · intro hv
      exact hs ⟨v, hv⟩

private theorem wedge_test : ∀ u v : V,
    Bivectors.wedge u v = Pi.single 0 1 ↔
      (u ∈ plane ∧ v ∈ plane ∧ u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v) := by
  change ∀ u v : V, Bivectors.wedge u v = Pi.single 0 1 ↔
    ((u 2 = 0 ∧ u 3 = 0) ∧ (v 2 = 0 ∧ v 3 = 0) ∧ u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v)
  decide +kernel

private theorem exterior_fixed_iff (s : SL(4, ZMod 2)) :
    Bivectors.exteriorMap s.val (Pi.single 0 1) = Pi.single 0 1 ↔
      BinaryLinear.OuterCyclic.slEquivLinear 4 s ∈ BinaryLinear.parabolic plane := by
  let g := BinaryLinear.OuterCyclic.slEquivLinear 4 s
  have he : Bivectors.exteriorMap s.val (Pi.single 0 1) =
      Bivectors.wedge (g (Pi.single 0 1)) (g (Pi.single 1 1)) := by
    rw [← Bivectors.wedge_basis 0, Bivectors.exteriorMap_wedge]
    rfl
  rw [he, wedge_test, mem_parabolic_iff]
  have h0 : g (Pi.single 0 1) ≠ 0 := by
    exact fun h => (by decide : (Pi.single 0 1 : V) ≠ 0) (g.map_eq_zero_iff.mp h)
  have h1 : g (Pi.single 1 1) ≠ 0 := by
    exact fun h => (by decide : (Pi.single 1 1 : V) ≠ 0) (g.map_eq_zero_iff.mp h)
  have hne : g (Pi.single 0 1) ≠ g (Pi.single 1 1) := by
    exact fun h => (by decide : (Pi.single 0 1 : V) ≠ Pi.single 1 1) (g.injective h)
  tauto

private def word : DeletedEight.evenCode :=
  ⟨![1,1,1,1,0,0,0,0], by
    change (∑ i : Fin 8, (![1,1,1,1,0,0,0,0] : Fin 8 → ZMod 2) i) = 0
    decide⟩

private theorem difference_test : ∀ a b c d : Fin 8,
    word.val a - word.val b = word.val c - word.val d ↔
      (a.val / 4 = c.val / 4 ↔ b.val / 4 = d.val / 4) := by
  decide +kernel

private theorem deleted_fixed_iff (p : Equiv.Perm (Fin 8)) :
    DeletedEight.quotientPerm p (Submodule.Quotient.mk word) =
      Submodule.Quotient.mk word ↔ p ∈ fourStabilizer := by
  change (Submodule.Quotient.mk (DeletedEight.evenPerm p word) : DeletedEight.W) =
    Submodule.Quotient.mk word ↔ _
  rw [Submodule.Quotient.eq, DeletedEight.constants, Submodule.mem_span_singleton]
  have hi : p⁻¹ ∈ fourStabilizer ↔ p ∈ fourStabilizer := fourStabilizer.inv_mem_iff
  rw [← hi, mem_fourStabilizer]
  constructor
  · rintro ⟨a, ha⟩ i j
    apply (difference_test _ _ _ _).mp
    have hh (k : Fin 8) := congrArg (fun v : DeletedEight.evenCode => v.val k) ha
    exact (hh i).symm.trans (hh j)
  · intro h
    refine ⟨word.val (p.symm 0) - word.val 0, ?_⟩
    apply Subtype.ext
    ext i
    simpa only [Submodule.coe_smul, Pi.smul_apply, DeletedEight.oneWord, smul_eq_mul,
      mul_one, Submodule.coe_sub, Pi.sub_apply, DeletedEight.evenPerm_apply, Equiv.Perm.inv_def] using
      (difference_test _ _ _ _).mpr (h 0 i)

private theorem split_mark :
    DeletedEight.splitEquiv (Exterior.coordinates (Pi.single 0 (1 : ZMod 2))) =
      Submodule.Quotient.mk word := by
  change Submodule.Quotient.mk (DeletedEight.intoEven _) = Submodule.Quotient.mk word
  congr 1
  apply Subtype.ext
  decide +kernel

private theorem action_compare (a : alternatingGroup (Fin 8)) :
    DeletedEight.orthogonalHom a.val = Exterior.toOrthogonal
      (sl4TwoEquivPSL.symm (alt8EquivPSL4Two a)) := by
  simp only [alt8EquivPSL4Two, psl4TwoEquivAlt8, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  change symmetricEquivOrthogonal a.val = Exterior.toOrthogonal (sl4TwoEquivAlt8.symm a)
  have h := congrArg Subtype.val (sl4TwoEquivAlt8.apply_symm_apply a)
  change symmetricEquivOrthogonal.symm (Exterior.toOrthogonal (sl4TwoEquivAlt8.symm a)) = a.val at h
  exact (congrArg symmetricEquivOrthogonal h).symm.trans (by simp)

private theorem orthogonal_fixed_iff (p : Equiv.Perm (Fin 8)) :
    (DeletedEight.orthogonalHom p).val (Exterior.coordinates (Pi.single 0 (1 : ZMod 2))) =
      Exterior.coordinates (Pi.single 0 1) ↔ p ∈ fourStabilizer := by
  change DeletedEight.splitEquiv.symm (DeletedEight.quotientPerm p
    (DeletedEight.splitEquiv (Exterior.coordinates (Pi.single 0 1)))) = _ ↔ _
  rw [LinearEquiv.symm_apply_eq, split_mark]
  exact deleted_fixed_iff p

private theorem matrix_fixed_iff (s : SL(4, ZMod 2)) :
    (Exterior.toOrthogonal s).val (Exterior.coordinates (Pi.single 0 (1 : ZMod 2))) =
      Exterior.coordinates (Pi.single 0 1) ↔
      BinaryLinear.OuterCyclic.slEquivLinear 4 s ∈ BinaryLinear.parabolic plane := by
  change Exterior.coordinates (Bivectors.exteriorMap s.val
    (Exterior.coordinates.symm (Exterior.coordinates (Pi.single 0 1)))) = _ ↔ _
  rw [LinearEquiv.symm_apply_apply, Exterior.coordinates.injective.eq_iff]
  exact exterior_fixed_iff s

/-- The existing ATLAS equivalence followed by the binary matrix action. -/
public def equiv : A8 ≃* BinaryLinear.GL V :=
  alt8EquivPSL4Two.trans (sl4TwoEquivPSL.symm.trans (BinaryLinear.OuterCyclic.slEquivLinear 4))

/-- This particular equivalence identifies the actual even four-block subgroup. -/
public theorem parabolic_comap : (BinaryLinear.parabolic plane).comap equiv.toMonoidHom =
    fourStabilizer.subgroupOf (alternatingGroup (Fin 8)) := by
  ext a
  change BinaryLinear.OuterCyclic.slEquivLinear 4
    (sl4TwoEquivPSL.symm (alt8EquivPSL4Two a)) ∈ BinaryLinear.parabolic plane ↔ _
  rw [← matrix_fixed_iff, ← action_compare, orthogonal_fixed_iff]
  rfl
end Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
