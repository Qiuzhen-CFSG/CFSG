module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.SourceSimplicity
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.IncomingPointKernel
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.ReverseIsogeny
public import Theory.AlgebraicGroup.Simple.Basic
public import Theory.AlgebraicGroup.Semisimple.IsogenySource

/-!
# Universality of the concrete Spin carrier from semisimple centers

The source of an incoming connected isogeny is semisimple. Center containment
in its maximal torus places the entire kernel in the constructed coroot-torus
lift, where the actual coordinate calculation makes the incoming map injective.
The proved characteristic-power descent then produces a reverse isogeny.
Only the shared semisimple-center theorem remains as an earlier source input;
no representation hypothesis or regular inverse of Frobenius is assumed.
Source: GLS3 1.9.5(h), 1.10.4(b), 1.10.5 and 1.12.5(b).
-/

public section
namespace Triality.SimplyConnected
open Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The actual universal-version property, retaining only the shared center theorem. -/
theorem source_universal_of_semisimple_centers
    (hcenter : ∀ (H : Variety k) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
      ∀ T : ClosedSubgroup H, IsMaximalTorus T →
        Subgroup.center (Variety.Point H) ≤ T.toSubgroup) :
    IsUniversalVersion (groupVariety k) := by
  have hs := (source_simple k).semisimple
  refine ⟨hs, ?_⟩
  intro H _ hH φ hφ
  exact exists_reverse_isogeny_of_injective k hH φ hφ
    (incoming_isogeny_injective_of_center_le_maximalTorus k hH φ hφ
      (hcenter H (isogeny_source_semisimple φ hφ hH hs)))

end Triality.SimplyConnected
