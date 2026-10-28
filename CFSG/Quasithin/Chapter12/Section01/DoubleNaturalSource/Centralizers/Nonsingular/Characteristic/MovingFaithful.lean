module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Moving
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceStabilizers

/-!
# The nonsingular moving subgroup has trivial residual fixed subgroup

The marked nonsingular moving space is ker(f) plus ann(x), while the
residual fixed space consists of the two complementary marked lines.
Their intersection is zero. The actual action quotient and commutator
comparison transport this to C_[W,L_w](L_w) = 1 in the original group.
The ordinary-component application is in `FourComponents`.
Source: Aschbacher--Smith, H.9.1(4) and 12.1.1, printed pp.390,788.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

omit [Finite G] in
private theorem nonsingular_moving_fixed_disjoint
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    Disjoint (S.setup.moving (Additive.ofMul w))
      (S.setup.fixed (S.setup.residual (Additive.ofMul w))) := by
  have hv : S.setup.quadratic (Additive.ofMul w) = 1 := by rwa [S.quadratic_eq]
  have hs := S.setup.nonsingular_structure hv
  have hc := S.setup.nonsingular_complement_actions hv
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro z hz
  have hm := Submodule.mem_map_of_mem (f := S.setup.model.coordinates.toLinearMap) hz.1
  have hf := Submodule.mem_map_of_mem (f := S.setup.model.coordinates.toLinearMap) hz.2
  rw [hs.2.2.2.2,BinaryNaturalDual.AdaptedPair.mem_movingSpace] at hm
  rw [hs.2.2.2.1] at hf
  apply S.setup.model.coordinates.injective
  rw [map_zero]
  apply Prod.ext
  · exact (disjoint_iff.mp hc.1.disjoint).le ⟨hf.1,hm.1⟩
  · exact (disjoint_iff.mp hc.2.1.disjoint).le ⟨hf.2,hm.2⟩

include S in
/-- The literal moving subgroup has no nonidentity element centralizing the point residual. -/
theorem nonsingular_moving_centralizer_residual
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    ⁅componentOrbit V (T : Subgroup G),B.pointResidual w⁆ ⊓
      centralizer (B.pointResidual w : Set G) = ⊥ := by
  let W := componentOrbit V (T : Subgroup G)
  apply bot_unique
  intro x hx
  have hmov := hx.1
  rw [←S.moving_eq_ambient_commutator w] at hmov
  obtain ⟨z,hz,rfl⟩ := hmov
  have hf : Additive.ofMul z ∈ S.setup.fixed (S.setup.residual (Additive.ofMul w)) := by
    intro a
    have ha : a.val ∈ (B.actionProjection.comp
        (inclusion (B.pointResidual_le_normalizer w))).range :=
      (S.pointResidual_action_range w).symm ▸ a.property
    obtain ⟨r,hr⟩ := ha
    change S.setup.representation a.val (Additive.ofMul z) = Additive.ofMul z
    rw [←hr,S.representation_eq]
    apply Additive.toMul.injective
    apply Subtype.ext
    change (r : G) * (z : G) * (r : G)⁻¹ = (z : G)
    have hc : (r : G) * (z : G) = (z : G) * (r : G) := hx.2 (r : G) r.property
    rw [hc,mul_inv_cancel_right]
  have hh := (disjoint_iff.mp (S.nonsingular_moving_fixed_disjoint w hw)).le ⟨hz,hf⟩
  have hz0 : Additive.ofMul z = 0 := hh
  exact congrArg (fun v : Additive W => (v.toMul : G)) hz0

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
