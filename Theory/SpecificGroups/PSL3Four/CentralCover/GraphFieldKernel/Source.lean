module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphFieldKernel.Squares
public import Theory.GroupTheory.PerfectCentralCoverSquareAction
public import Theory.Frattini.PGroup

/-!
# I.2.2(3b): graph-field on every elementary central cover of PSL₃(4)

The proved square-displacement theorem descends the actual universal lift
through the original perfect central covering map. The resulting involutory
automorphism induces inverse transpose times Frobenius and fixes the full
kernel pointwise. Applying it to the original marked central quotient gives
the last assertion of I.2.2(3b) from the literal center two-group and trivial
Frattini hypotheses, without a chosen Klein-four kernel or a chosen lift.

Source: Aschbacher–Smith I.2.2(3b), printed pp.409–410.
-/

public section
open PerfectCentralCovering Subgroup
namespace Matrix.PSL3Four.CentralCover.GraphFieldKernel
open ExtendedCentralizer.CoverCentralizers.DiagonalCenter
open ExtendedCentralizer.ProjectiveFixer
private instance : Group.IsPerfect PSL := Atlas.psl_perfect (F := F) 3 (by decide)
universe u
variable {E : Type u} [Group E] [Group.IsPerfect E]

/-- Actual graph-field action through an arbitrary perfect elementary central cover. -/
theorem exists_graphField_lift (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hexp : ∀ z ∈ f.ker,z^2=1) :
    ∃ a : MulAut E, (∀ x, f (a x)=graphField (f x)) ∧
      (∀ z ∈ f.ker,a z=z) ∧ a^2=1 := by
  apply exists_involutory_lift_of_universal_square_displacements graphField
    (universalLift graphField) (universalLift_compatible graphField)
    universalLift_graphField_sq _ f hf hc hexp
  intro z
  obtain ⟨w,hw⟩ := graphField_displacement_is_square z
  exact ⟨w,congrArg Subtype.val hw⟩

/-- The original center and central-quotient marking supply the elementary-kernel input. -/
theorem source_graphField_fixes_center [Finite E]
    (e : (E ⧸ center E) ≃* PSL) (hz : IsPGroup 2 (center E))
    (hphi : frattini (center E)=⊥) :
    ∃ a : MulAut E,
      (∀ x, e (QuotientGroup.mk (a x))=graphField (e (QuotientGroup.mk x))) ∧
      (∀ z ∈ center E,a z=z) ∧ a^2=1 := by
  let f : E →* PSL := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker=center E := by
    ext x
    change e (QuotientGroup.mk x)=1 ↔ x∈center E
    rw [←e.map_one,e.injective.eq_iff,QuotientGroup.eq_one_iff]
  let : Fact (IsPGroup 2 (center E)) := ⟨hz⟩
  let : IsElementaryAbelian 2 (center E) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  obtain ⟨a,ha,hfix,h2⟩ := exists_graphField_lift f hf hk.le (fun z h =>
    elemPow_eq_one_of_isElementaryAbelian z (hk ▸ h))
  exact ⟨a,ha,fun z h => hfix z (hk.symm ▸ h),h2⟩
end Matrix.PSL3Four.CentralCover.GraphFieldKernel
