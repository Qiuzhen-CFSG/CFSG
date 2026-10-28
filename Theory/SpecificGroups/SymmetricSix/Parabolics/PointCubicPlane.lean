module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.PolarActions

/-!
# Cubic point stabilizers move incident symplectic planes

The cycle (234) fixes the duad {0,1} and moves the syntheme
{{0,1},{2,3},{4,5}}. The actual A₆ flag transitivity transports this
calculation to any nonzero vector on any isotropic binary plane. The final
statement uses the original polar linear action and supplies a vector moved
out of the plane. Only the displayed six-letter identities are computed.

This is the model obstruction used by the HS action in 14.3.32 to exclude
its A₆ and S₆ rows. Source: Aschbacher--Smith, printed p.1004, with the
binary symplectic geometry of I.5.4 and I.5.8--9, printed pp.420--422.
-/

public section

set_option backward.isDefEq.respectTransparency false
open Subgroup Matrix
namespace Theory.SpecificGroups.SymmetricSix.PointCubicPlane
private def a : A6 := ⟨Equiv.swap 2 3 * Equiv.swap 3 4, by decide⟩
private theorem cube : a^3=1 := by decide +kernel
private theorem point_fixed : a • duadPolarEquiv 0 = duadPolarEquiv 0 := by
  change a.val • duadPolarEquiv 0 = duadPolarEquiv 0
  rw [← duadPolarEquiv_equivariant]
  congr 1
  apply duadSet_injective
  rw [duadSet_smul]
  decide +kernel
private theorem plane_moved : a • synthemePolarEquiv 0 ≠ synthemePolarEquiv 0 := by
  change a.val • synthemePolarEquiv 0 ≠ synthemePolarEquiv 0
  rw [← synthemePolarEquiv_equivariant]
  intro he
  have hh := synthemePolarEquiv.injective he
  rw [synthemeAct_eq_iff] at hh
  revert hh
  decide +kernel

/-- Every incident binary polar flag has a cubic in A₆ fixing its point and moving its plane. -/
theorem exists_cubic (v : BinaryPoint) (W : BinaryLine) (hv : v.val ∈ W.val) :
    ∃ b : A6, b^3=1 ∧ b • v=v ∧ b • W ≠ W := by
  obtain ⟨g,hg,hw⟩ := a6_polar_flag_transitive (duadPolarEquiv 0) v
    (synthemePolarEquiv 0) W ((polar_incidence_equivalence 0 0).mp (by decide)) hv
  refine ⟨g*a*g⁻¹,?_,?_,?_⟩
  · rw [show g*a*g⁻¹ = MulAut.conj g a by rfl,←map_pow,cube,map_one]
  · rw [←hg,mul_smul,mul_smul,inv_smul_smul,point_fixed]
  · rw [←hw,mul_smul,mul_smul,inv_smul_smul]
    exact fun hh => plane_moved ((MulAction.injective g) hh)

/-- In literal matrix coordinates, the point-fixing cubic moves a vector out of the plane. -/
theorem exists_matrix_cubic (v : NaturalModule) (hv : v ≠ 0)
    (W : Submodule (ZMod 2) NaturalModule) (hd : Module.finrank (ZMod 2) W=2)
    (hiso : ∀ x∈W, ∀ y∈W, polarForm x y=0) (hvw : v∈W) :
    ∃ b : A6, b^3=1 ∧ polarAction b.val v=v ∧
      ∃ w∈W, polarAction b.val w ∉ W := by
  obtain ⟨b,hb,hvfix,hm⟩ := exists_cubic ⟨v,hv⟩ ⟨W,hd,hiso⟩ hvw
  refine ⟨b,hb,?_,?_⟩
  · exact (polarAction_point b.val ⟨v,hv⟩).trans (congrArg Subtype.val hvfix)
  · by_contra! hn
    apply hm
    apply Subtype.ext
    change (b.val • (show BinaryLine from ⟨W,hd,hiso⟩)).val = W
    rw [polarLine_smul_val]
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨w,hw,rfl⟩
      exact hn w hw
    · have hi : Function.Injective (polarLinearMap b.val) := by
        intro x y he
        change polarAction b.val x = polarAction b.val y at he
        have he' := congrArg (polarAction b.val⁻¹) he
        simpa only [← polarAction_mul,inv_mul_cancel,polarAction_one] using he'
      exact (W.equivMapOfInjective (polarLinearMap b.val) hi).finrank_eq.symm
end Theory.SpecificGroups.SymmetricSix.PointCubicPlane
