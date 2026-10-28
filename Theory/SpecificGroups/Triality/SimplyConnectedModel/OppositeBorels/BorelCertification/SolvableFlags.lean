module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.Triangular
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.SolvableFlags.Representation
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.SolvableFlags.Classification

/-!
# Triangularity of connected solvable overgroups of the Spin candidates

Restrict the regular natural Spin representation to the given closed subgroup
and apply Lie–Kolchin. The contained candidate forces its invariant flag to
be one of the two coordinate flags differing at the middle hyperbolic pair.
The quadratic-form calculation shows that preservation of either flag forces
the prescribed triangular support. No geometric premise remains, and no
triangular saturation or prior Borel maximality is used.

Source: GLS3, Theorem 1.11.2 (`refs/KGroup/GLS3/Chapter1.tex`) and
Steinberg (6.2)(a) (`refs/KGroup/GLS3/Chapter2St2.tex`). The parent Borel
certification combines this result with triangular saturation to establish
maximal connected solvability of the concrete candidates.
-/

@[expose] public section
open Theory Theory.AlgebraicGroup
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
local instance solvableOvergroupCarrierAlgebraicGroup (S : ClosedSubgroup (groupVariety k)) : AlgebraicGroup S.carrierVariety :=
  S.carrierAlgebraicGroup

/-- Every point of a connected solvable closed overgroup of either signed
candidate has the candidate's prescribed upper-triangular natural matrix. -/
theorem connected_solvable_overgroup_triangular (negative : Bool)
    (S : ClosedSubgroup (groupVariety k))
    (hc : _root_.IsConnected (S : Set (Points k)))
    (hs : Group.IsSolvable (Variety.Point S.carrierVariety))
    (hBS : candidate k negative ≤ S) (g : Points k) (hg : g ∈ S) :
    tTriangular 8 (matrix k negative g) := by
  obtain ⟨F, hF⟩ := SolvableFlags.exists_invariant_flag k S hc hs
  obtain ⟨alternate, rfl⟩ := SolvableFlags.candidate_invariant_flag k negative F
    (fun x hx => hF x (hBS hx))
  exact SolvableFlags.triangular_of_preserves_flagOrder k negative alternate g (hF g hg)

end Triality.SimplyConnected.OppositeBorels.BorelCertification
