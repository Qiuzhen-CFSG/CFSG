module

public import Theory.Representation.BinaryNaturalDual.FiveActors.OuterConjugacy
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Equivariance

/-!
# The literal fixed-space isomorphism for an outer involution

The inner/graph description exchanges the natural and dual summands. The
binary diagonal equivalence identifies the natural five-space with the
actual fixed kernel and displacement image. Its formula intertwines the
actual inner centralizer action.

Source: Aschbacher–Smith, H.9.2(1), printed p.390 (PDF p.401).
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic
open BinaryNaturalDual.AdaptedPair
namespace BinaryNaturalDual.FiveActors.ModuleGeometry
abbrev V := CoordinateSpace 5
abbrev naturalSpace : Submodule (ZMod 2) V :=
  LinearMap.range (LinearMap.inl (ZMod 2) X (Module.Dual (ZMod 2) X))
abbrev dualSpace : Submodule (ZMod 2) V :=
  LinearMap.range (LinearMap.inr (ZMod 2) X (Module.Dual (ZMod 2) X))

variable (d : CoordinateAction 5)

theorem linearAction_inner_pair (g : G) (v : V) :
    linearAction d (MulAut.conj g) v = (g v.1, g.symm.dualMap v.2) :=
  (d.on_inner g v).trans (naturalDualRepresentation_apply g v)

theorem action_involutive (t : M) (ht : t ^ 2 = 1) :
    Function.Involutive (linearAction d t) := by
  intro v
  have h := congrArg (fun a : M => linearAction d a v) ht
  simpa only [pow_two, map_mul, LinearEquiv.mul_apply, map_one, LinearEquiv.coe_one, id_eq] using h

theorem outer_swaps (t : M) (hout : t ∉ L) :
    (∀ u ∈ naturalSpace, linearAction d t u ∈ dualSpace) ∧
    (∀ u ∈ dualSpace, linearAction d t u ∈ naturalSpace) := by
  obtain ⟨g, hi | hg⟩ := inner_graph (Or.inr rfl) t
  · exact (hout (hi ▸ ⟨g, rfl⟩)).elim
  rw [hg]
  constructor
  · rintro _ ⟨w, rfl⟩
    refine ⟨dotProductEquiv (ZMod 2) (Fin 5) (g w), ?_⟩
    change (0, _) = linearAction d (graphLinear 5 * MulAut.conj g) (w, 0)
    rw [map_mul, LinearEquiv.mul_apply, linearAction_inner_pair, linearAction_apply, d.on_graph]
    simp [coordinateSwap_apply]
  · rintro _ ⟨f, rfl⟩
    refine ⟨(dotProductEquiv (ZMod 2) (Fin 5)).symm (g.symm.dualMap f), ?_⟩
    change (_, 0) = linearAction d (graphLinear 5 * MulAut.conj g) (0, f)
    rw [map_mul, LinearEquiv.mul_apply, linearAction_inner_pair, linearAction_apply, d.on_graph]
    simp [coordinateSwap_apply]

noncomputable def diagonal (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    X ≃ₗ[ZMod 2] fixedSpace (linearAction d t) :=
  (LinearEquiv.ofInjective (LinearMap.inl (ZMod 2) X (Module.Dual (ZMod 2) X))
    LinearMap.inl_injective).trans
      (diagonalEquiv LinearMap.isCompl_range_inl_inr (linearAction d t)
        (action_involutive d t ht) (outer_swaps d t hout).1 (outer_swaps d t hout).2)

@[simp] theorem diagonal_apply (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) (w : X) :
    (diagonal d t ht hout w : V) = (w, 0) + d.representation t (w, 0) := rfl

theorem fixed_eq_displacement (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    fixedSpace (linearAction d t) = LinearMap.range (d.representation t - LinearMap.id) :=
  fixedSpace_eq_displacement LinearMap.isCompl_range_inl_inr (linearAction d t)
    (action_involutive d t ht) (outer_swaps d t hout).1 (outer_swaps d t hout).2

theorem fixed_finrank (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L) :
    Module.finrank (ZMod 2) (fixedSpace (linearAction d t)) = 5 := by
  rw [← (diagonal d t ht hout).finrank_eq]
  simp [X, BinaryLinear.OuterCyclic.Space]

noncomputable def centralizerNatural (t : M) : innerCentralizer t →* G :=
  t.fixedSubgroup.subtype.comp (fixedInnerCentralizerEquiv t).symm.toMonoidHom

@[simp] theorem centralizerNatural_inner (t : M) (a : innerCentralizer t) :
    MulAut.conj (centralizerNatural t a) = a.val :=
  congrArg Subtype.val ((fixedInnerCentralizerEquiv t).apply_symm_apply a)

theorem diagonal_equivariance (t : M) (ht : t ^ 2 = 1) (hout : t ∉ L)
    (a : innerCentralizer t) (w : X) :
    (diagonal d t ht hout (centralizerNatural t a w) : V) =
      d.representation a.val (diagonal d t ht hout w) := by
  have hc : Function.Commute (linearAction d a.val) (linearAction d t) := by
    intro v
    have h := congrArg (fun b : M => linearAction d b v)
      (Subgroup.mem_centralizer_singleton_iff.mp a.property.2)
    simpa only [map_mul, LinearEquiv.mul_apply] using h
  change _ = linearAction d a.val ((w, 0) + linearAction d t (w, 0))
  rw [diagonal_equivariant _ _ hc]
  have he : linearAction d a.val (w, 0) = (centralizerNatural t a w, 0) := by
    rw [← centralizerNatural_inner t a, linearAction_inner_pair]
    simp
  rw [he]
  rfl
end BinaryNaturalDual.FiveActors.ModuleGeometry
