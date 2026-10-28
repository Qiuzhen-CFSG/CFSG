module
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Comparing intrinsic and embedded two-core centers

If the embedded two-core is a specified subgroup R, and its embedded center
centralizes the original subgroup B, then Z(O₂(B)) is central in B. The
proof transports the center through the literal subtype isomorphism.

Source application: Aschbacher--Smith 10.2.9, pp.750--751, for the short
G₂ and arms triality parabolics.
-/

public section
namespace Subgroup
/-- Centrality of the embedded core center implies intrinsic centrality. -/
theorem center_pCore_map_le_center_of_embedded
    {H : Type*} [Group H] (B R : Subgroup H) (hR : B.pCoreIn 2 = R)
    (hc : (center R).map R.subtype ≤ centralizer (B : Set H)) :
    (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  let e : pCore 2 B ≃* R :=
    ((pCore 2 B).equivMapOfInjective B.subtype B.subtype_injective).trans
      (MulEquiv.subgroupCongr hR)
  rintro _ ⟨z,hz,rfl⟩
  apply mem_center_iff.mpr
  intro b
  have he : e z ∈ center R := by
    apply mem_center_iff.mpr
    intro r
    obtain ⟨w,rfl⟩ := e.surjective r
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hz w)
  exact Subtype.ext (hc (mem_map_of_mem R.subtype he) b b.property)

end Subgroup
