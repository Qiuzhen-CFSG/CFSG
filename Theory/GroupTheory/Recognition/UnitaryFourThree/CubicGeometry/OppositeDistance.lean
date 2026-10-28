module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.AxisFusion
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# The original opposite orbit lies at distance two

The other cubic axis is a common neighbor of W and the selected opposite
cubic. Its fusion was proved from the original reflected marking. The
SL₂(3) conjugator carrying W to the opposite cubic centralizes that axis,
so the conjugate of V supplies the second edge. The two endpoints are
not collinear, hence their graph distance is exactly two.

All D-conjugates retain this distance. Together with the free orbit of
order 243, this gives a literal subset of the source distance-two sphere
and its lower bound. The common normalizer of the selected endpoints is
exactly the original order-48 complement.
Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.10(6)–(7), p.248.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem opposite_cubic_common_neighbor {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    Y ∈ c.neighbors c.otherAxis := by
  obtain ⟨g, hg, he⟩ := c.oppositeFactor_cubic_conjugate hYL hY
  have hgA : g ∈ Subgroup.centralizer (c.otherAxis : Set G) :=
    (centralizer_le (show c.otherAxis ≤ c.J from le_sup_right))
      ((le_centralizer_iff.mp c.special_centralizes_oppositeFactor) hg)
  have hfix : c.otherAxis.conjBy g = c.otherAxis :=
    mem_normalizer_iff_map_conj_eq.mp ((centralizer_le_normalizer _) hgA)
  have hYA : Y ≠ c.otherAxis := by
    intro hh
    exact c.opposite_cubic_not_collinear hYL hY hne (hh ▸ c.otherAxis_neighbor)
  refine ⟨c.cubic_in_oppositeFactor_is_point hYL hY, hYA, c.V.conjBy g,
    c.line_conjugate_mem c.line_mem g, ?_, ?_⟩
  · rw [← hfix]
    exact map_mono c.otherAxis_le_kernel
  · rw [← he]
    exact map_mono c.line_le_kernel

theorem opposite_cubic_distance_two {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W) :
    c.collinearity.edist ⟨c.W, c.point_mem⟩
      ⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩ = 2 := by
  apply c.collinearity.edist_eq_two_iff.mpr
  refine ⟨fun hh => hne (congrArg Subtype.val hh).symm,
    c.opposite_cubic_not_collinear hYL hY hne, ?_⟩
  refine ⟨⟨c.otherAxis, c.otherAxis_is_point⟩, c.otherAxis_neighbor, ?_⟩
  exact c.collinearity.adj_symm (c.opposite_cubic_common_neighbor hYL hY hne)

theorem opposite_cubic_conjugate_distance_two {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (d : G) (hd : d ∈ c.D) :
    c.collinearity.edist ⟨c.W, c.point_mem⟩
      ⟨Y.conjBy d, c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d⟩ = 2 := by
  have hdn : d ∈ normalizer (c.W : Set G) := c.complement_product.ge (mem_sup_left hd)
  have hw : c.W.conjBy d = c.W := mem_normalizer_iff_map_conj_eq.mp hdn
  have hwi : c.W.conjBy d⁻¹ = c.W := mem_normalizer_iff_map_conj_eq.mp (inv_mem hdn)
  have hne' : Y.conjBy d ≠ c.W := by
    intro he
    have hh := congrArg (fun A : Subgroup G => A.conjBy d⁻¹) he
    exact hne (by simpa only [conjBy_inv, hwi] using hh)
  have hn : Y.conjBy d ∉ c.neighbors c.W := by
    intro hh
    have hm := c.neighbor_conjugate hh d⁻¹
    rw [conjBy_inv, hwi] at hm
    exact c.opposite_cubic_not_collinear hYL hY hne hm
  have hWA := c.neighbor_conjugate c.otherAxis_neighbor d
  rw [hw] at hWA
  have hYA := c.neighbor_conjugate (c.opposite_cubic_common_neighbor hYL hY hne) d
  apply c.collinearity.edist_eq_two_iff.mpr
  refine ⟨fun hh => hne' (congrArg Subtype.val hh).symm, hn, ?_⟩
  exact ⟨⟨c.otherAxis.conjBy d, c.point_conjugate_mem c.otherAxis_is_point d⟩,
    hWA, c.collinearity.adj_symm hYA⟩

theorem distance_two_sphere_card_lower : 243 ≤ Nat.card
    {U : c.points // c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} := by
  classical
  obtain ⟨Y, hYL, hY, hne, -, -⟩ := c.exists_complement_fixed_opposite_cubic
  let O := {U : Subgroup G // ∃ d ∈ c.D, U = Y.conjBy d}
  have ho (U : O) : U.val ∈ c.points := by
    obtain ⟨d, hd, he⟩ := U.property
    rw [he]
    exact c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d
  have ht (U : O) : c.collinearity.edist ⟨c.W, c.point_mem⟩ ⟨U.val, ho U⟩ = 2 := by
    obtain ⟨d, hd, he⟩ := U.property
    have hu : (⟨U.val, ho U⟩ : c.points) =
        ⟨Y.conjBy d, c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d⟩ :=
      Subtype.ext he
    rw [hu]
    exact c.opposite_cubic_conjugate_distance_two hYL hY hne d hd
  let f : O → {U : c.points // c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2} :=
    fun U => ⟨⟨U.val, ho U⟩, ht U⟩
  have hf : Function.Injective f := fun U U' he =>
    Subtype.ext (congrArg (fun a => a.val.val) he)
  have hh := Nat.card_le_card_of_injective f hf
  rwa [c.opposite_cubic_orbit_card hYL hY hne] at hh

theorem opposite_cubic_common_normalizer {Y : Subgroup G}
    (hYL : Y ≤ c.oppositeFactor) (hY : Nat.card Y = 3) (hne : Y ≠ c.W)
    (hK : c.K ≤ normalizer (Y : Set G)) :
    normalizer (c.W : Set G) ⊓ normalizer (Y : Set G) = c.K := by
  have hn : c.K ≤ normalizer (c.D : Set G) :=
    (c.complement_le.trans inf_le_right).trans (CubicLine.normalizer_normalizes_oddKernel c.W)
  apply le_antisymm
  · intro x hx
    have hm : x ∈ (c.D : Set G) * (c.K : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left c.D c.K hn, ← c.complement_product]
      exact hx.1
    obtain ⟨d, hd, k, hk, he⟩ := hm
    change d * k = x at he
    have hdN : d ∈ normalizer (Y : Set G) := by
      have hh := (normalizer (Y : Set G)).mul_mem hx.2 ((normalizer (Y : Set G)).inv_mem (hK hk))
      rw [← he, mul_inv_cancel_right] at hh
      exact hh
    have hd0 : d ∈ (⊥ : Subgroup G) := c.opposite_cubic_odd_stabilizer hYL hY hne ▸ ⟨hd, hdN⟩
    rw [← he, mem_bot.mp hd0, one_mul]
    exact hk
  · exact le_inf (c.complement_le.trans inf_le_right) hK

theorem exists_opposite_distance_two :
    ∃ Y : c.points, c.collinearity.edist ⟨c.W, c.point_mem⟩ Y = 2 ∧
      normalizer (c.W : Set G) ⊓ normalizer (Y.val : Set G) = c.K ∧
      Nonempty ((c.W ⊔ Y.val : Subgroup G) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      c.D ⊓ normalizer (Y.val : Set G) = ⊥ ∧
      Nat.card {U : Subgroup G // ∃ d ∈ c.D, U = Y.val.conjBy d} = 243 := by
  obtain ⟨Y, hYL, hY, hne, hgen, hK⟩ := c.exists_complement_fixed_opposite_cubic
  exact ⟨⟨Y, c.cubic_in_oppositeFactor_is_point hYL hY⟩,
    c.opposite_cubic_distance_two hYL hY hne,
    c.opposite_cubic_common_normalizer hYL hY hne hK,
    hgen.symm ▸ c.oppositeFactor_model, c.opposite_cubic_odd_stabilizer hYL hY hne,
    c.opposite_cubic_orbit_card hYL hY hne⟩

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
