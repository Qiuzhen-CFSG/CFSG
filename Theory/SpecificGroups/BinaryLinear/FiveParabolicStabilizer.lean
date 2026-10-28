module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.GroupTheory.InnerStabilizerAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Inner stabilizer actions on binary five-dimensional end parabolics

Every automorphism of GL₅(2) is inner or inverse transpose times inner.
A graph-type automorphism carrying a point stabilizer to itself would make
that point stabilizer preserve a hyperplane. Subspace-stabilizer rigidity
would then identify a line with a hyperplane, contradicting dimension five.
The inner conjugator belongs to the point stabilizer by the same rigidity.
Inverse transpose transports hyperplane stabilizers to point stabilizers.

The result concerns the actual embedded stabilizers. It does not recognize
an arbitrary Sylow-normalizer overgroup or its solvable residual as an end
parabolic. That separate recognition is required in A.3.12(5).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.12(5),
printed p.47, and the proof of 1.3.9, printed p.514; the ambient automorphism
classification is supplied by `BinaryLinear.OuterCyclic`.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear.FiveParabolicStabilizer
open OuterCyclic

private theorem line_ne_bot {v : Space 5} (hv : v ≠ 0) :
    Submodule.span (ZMod 2) {v} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hv

private theorem line_ne_top {v : Space 5} (hv : v ≠ 0) :
    Submodule.span (ZMod 2) {v} ≠ ⊤ := by
  intro he
  have hd := finrank_span_singleton (K := ZMod 2) hv
  rw [he, finrank_top] at hd
  norm_num [Space] at hd

private theorem fixes_of_mem {v : Space 5} (hv : v ≠ 0) {g : LinearGroup 5}
    (hg : g ∈ parabolic (Submodule.span (ZMod 2) {v})) : g v = v := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    ((hg v).mpr (Submodule.mem_span_singleton_self v))
  have ha0 : a ≠ 0 := by
    intro hz
    exact hv (g.map_eq_zero_iff.mp (by simpa [hz] using ha.symm))
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  simpa [ha1] using ha.symm

private theorem mem_of_fixes {v : Space 5} {g : LinearGroup 5} (h : g v = v) :
    g ∈ parabolic (Submodule.span (ZMod 2) {v}) := by
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨a, g.injective (by simpa [h] using ha)⟩
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simpa [map_smul, h] using Submodule.smul_mem
      (Submodule.span (ZMod 2) {v}) a (Submodule.mem_span_singleton_self v)

private theorem pointParabolic_map_conj {v : Space 5} (hv : v ≠ 0) (g : LinearGroup 5) :
    (parabolic (Submodule.span (ZMod 2) {v})).map (MulAut.conj g).toMonoidHom =
      parabolic (Submodule.span (ZMod 2) {g v}) := by
  have hgv : g v ≠ 0 := fun h => hv (g.map_eq_zero_iff.mp h)
  rw [← normalizer_radical (line_ne_bot hv), ← normalizer_radical (line_ne_bot hgv),
    map_equiv_normalizer_eq]
  change normalizer ((pointRadical 5 v).map (MulAut.conj g).toMonoidHom : Set (LinearGroup 5)) = _
  rw [pointRadical_map_conj]
  rfl

private theorem inner_mem_of_stabilizes {v : Space 5} (hv : v ≠ 0) (g : LinearGroup 5)
    (h : (parabolic (Submodule.span (ZMod 2) {v})).map (MulAut.conj g).toMonoidHom =
      parabolic (Submodule.span (ZMod 2) {v})) :
    g ∈ parabolic (Submodule.span (ZMod 2) {v}) := by
  rw [pointParabolic_map_conj hv] at h
  have he := FourParabolicAction.parabolic_le_imp_eq (line_ne_bot hv) (line_ne_top hv) h.le
  apply mem_of_fixes
  have hgv : g v ∈ Submodule.span (ZMod 2) {v} :=
    he ▸ Submodule.mem_span_singleton_self (g v)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hgv
  have ha0 : a ≠ 0 := by
    intro hz
    exact hv (g.map_eq_zero_iff.mp (by simpa [hz] using ha.symm))
  have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
  simpa [ha1] using ha.symm

private def dotFunctional (v : Space 5) : Space 5 →ₗ[ZMod 2] ZMod 2 :=
  dotProductBilin (ZMod 2) (ZMod 2) v

private theorem dotFunctional_ne_zero {v : Space 5} (hv : v ≠ 0) :
    dotFunctional v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := LinearMap.congr_fun h (Pi.single i 1)
  simpa [dotFunctional, dotProductBilin, dotProduct_single] using hi

private theorem ker_ne_bot {f : Space 5 →ₗ[ZMod 2] ZMod 2} : f.ker ≠ ⊥ := by
  intro hker
  have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  norm_num [Space] at hd

private theorem not_graph_stabilizes_point {v : Space 5} (hv : v ≠ 0) (g : LinearGroup 5) :
    (parabolic (Submodule.span (ZMod 2) {v})).map
      (graphLinear 5 * MulAut.conj g).toMonoidHom ≠
        parabolic (Submodule.span (ZMod 2) {v}) := by
  intro h
  have hc : (graphLinear 5 * MulAut.conj g).toMonoidHom =
      (graphLinear 5).toMonoidHom.comp (MulAut.conj g).toMonoidHom := rfl
  rw [hc, ← map_map, pointParabolic_map_conj hv] at h
  let f := dotFunctional v
  have hf : f ≠ 0 := dotFunctional_ne_zero hv
  have hle : parabolic (Submodule.span (ZMod 2) {g v}) ≤ parabolic f.ker := by
    intro s hs y
    have hfix : graphLinear 5 s v = v := fixes_of_mem hv (h ▸ mem_map_of_mem _ hs)
    have he := graphLinear_dotProduct s v y
    rw [hfix] at he
    change f (s y) = f y at he
    change f (s y) = 0 ↔ f y = 0
    rw [he]
  have he := FourParabolicAction.parabolic_le_imp_eq (ker_ne_bot (f := f))
    (mt LinearMap.ker_eq_top.mp hf) hle
  have hd := f.finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le f.range
  have hgv : g v ≠ 0 := fun hz => hv (g.map_eq_zero_iff.mp hz)
  rw [← he, finrank_span_singleton hgv] at hd
  norm_num [Space] at hd hr
  omega

/-- A point stabilizer in GL₅(2) admits only inner ambient stabilizer actions. -/
theorem point_hasInnerStabilizerAction {v : Space 5} (hv : v ≠ 0) :
    (parabolic (Submodule.span (ZMod 2) {v})).HasInnerStabilizerAction := by
  intro α hα
  obtain ⟨g, rfl | rfl⟩ := inner_graph (Or.inr rfl) α
  · exact ⟨g, inner_mem_of_stabilizes hv g hα, fun x _ => rfl⟩
  · exact (not_graph_stabilizes_point hv g hα).elim

/-- Inverse transpose transports a hyperplane stabilizer to a point stabilizer. -/
theorem hyperplane_map_graph {f : Space 5 →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    ∃ v : Space 5, v ≠ 0 ∧ (parabolic f.ker).map (graphLinear 5).toMonoidHom =
      parabolic (Submodule.span (ZMod 2) {v}) := by
  obtain ⟨v, hv, he⟩ := graph_hyperplaneRadical (Or.inr rfl) f hf
  refine ⟨v, hv, ?_⟩
  rw [← normalizer_radical (ker_ne_bot (f := f)), map_equiv_normalizer_eq]
  change normalizer ((hyperplaneRadical 5 f).map (graphLinear 5).toMonoidHom : Set (LinearGroup 5)) = _
  rw [he]
  exact normalizer_radical (line_ne_bot hv)

/-- The same stabilizer-action assertion holds for hyperplanes. -/
theorem hyperplane_hasInnerStabilizerAction {f : Space 5 →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) :
    (parabolic f.ker).HasInnerStabilizerAction := by
  apply Subgroup.HasInnerStabilizerAction.of_map (graphLinear 5)
  obtain ⟨v, hv, he⟩ := hyperplane_map_graph hf
  rw [he]
  exact point_hasInnerStabilizerAction hv

/-- An actual end-node parabolic, preserving its embedding in GL₅(2). -/
def IsEndParabolic (A : Subgroup (LinearGroup 5)) : Prop :=
  (∃ v : Space 5, v ≠ 0 ∧ A = parabolic (Submodule.span (ZMod 2) {v})) ∨
    (∃ f : Space 5 →ₗ[ZMod 2] ZMod 2, f ≠ 0 ∧ A = parabolic f.ker)

/-- Both end-node classes have inner stabilizer action. -/
theorem IsEndParabolic.hasInnerStabilizerAction {A : Subgroup (LinearGroup 5)}
    (hA : IsEndParabolic A) : A.HasInnerStabilizerAction := by
  rcases hA with ⟨v, hv, rfl⟩ | ⟨f, hf, rfl⟩
  · exact point_hasInnerStabilizerAction hv
  · exact hyperplane_hasInnerStabilizerAction hf

end BinaryLinear.FiveParabolicStabilizer
