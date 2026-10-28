module

public import Theory.SpecificGroups.AlternatingSix.TwoPrimaryInvolutionData
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CentralExtensionCommutingPair
public import Theory.Mathieu.M22.Properties.HexadFourSquare

/-!
# Lifting the actual A₆ hexad complement in a two-primary cover

The proved A₆ covering calculation bounds a perfect two-primary kernel by two;
in its nontrivial case every involution lies in the kernel. The native hexad
section has two independent involutions with a commuting square root in M₂₂.
Their lifts therefore commute, excluding the nontrivial A₆ double cover in
the derived subgroup of the section's full preimage. This constructs a lift
of the specified, naturally marked native section.

This holds for every finite central two-group extension, without a prescribed
kernel order or an assumed splitting. It is a local step toward the multiplier
bound in Aschbacher–Smith I.1.3(4), printed p.407; the source's quartic hexad
argument is I.2.2(6), printed p.412. A₆ covering data come from GLS3 5.2.3–4.
-/

public section
namespace Sporadic.Mathieu.M22UniversalMultiplier
open PerfectCentralCovering Subgroup Theory.GroupTheory GLS3.Chapter5
open scoped Pointwise
universe u

private theorem alternating_six_twoPrimary_data :
    CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6)) :=
  AlternatingSix.twoPrimaryInvolutionData

/-- The native naturally marked A₆ complement lifts through every finite
central extension of M₂₂ with two-group kernel. -/
theorem exists_hexadSection_lift
    {E : Type u} [Group E] [Finite E] (f : E →* M22)
    (hf : Function.Surjective f) (hc : f.ker ≤ center E) (hp : IsPGroup 2 f.ker)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ s : alternatingGroup (Fin 6) →* E,
      f.comp s = (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let j := (MulAction.stabilizer M22 B).subtype.comp (m22HexadSection hB)
  have hj : Function.Injective j :=
    (MulAction.stabilizer M22 B).subtype_injective.comp (m22HexadSection_injective hB)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, r, hr, hrb⟩ :=
    M22HexadFourSquare.section_hasSquare hB
  apply CentralExtension.exists_lift_of_commuting_involution_lifts
    alternating_six_twoPrimary_data f hf hc hp j hj a b ha hb ha1 hb1 hab
  intro x y hx hy
  exact CentralExtension.commute_lifts_of_commuting_square_root f hf hc
    (j a) (j b) r hr (by rw [← map_pow, hb, map_one]) hrb x y hx hy
end Sporadic.Mathieu.M22UniversalMultiplier
