module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ModelRestriction
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.AttractorComparison

/-!
# Literal stabilizers and centralizer intersections

Borel self-normalization makes the stabilizer map injective on a Borel orbit.
Restriction along the actual centralizer inclusion translates stabilizer
equality into equality of pointwise-centralizer intersections in the original
group. These are the final subgroup identifications in Borel IV, 13.12.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open Variety.Geometric
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X : Variety.Geometric k}
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

theorem pointStabilizer_smul_eq_conjugate (A : MorphicAction G X) (x : Point X)
    (g : Variety.Point G) : A.pointStabilizer (A.toMulAction.smul g x) =
      (A.pointStabilizer x).conjugate g := by
  apply SetLike.coe_injective
  ext a
  change a ∈ (A.pointStabilizer (A.toMulAction.smul g x)).toSubgroup ↔
    a ∈ (A.pointStabilizer x).conjugate g
  rw [A.mem_pointStabilizer, ClosedSubgroup.mem_conjugate_iff, A.mem_pointStabilizer]
  let := A.toMulAction
  change a • (g • x) = g • x ↔ (g⁻¹ * a * g) • x = x
  constructor
  · intro h
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun z : Point X => g⁻¹ • z) h
  · intro h
    simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : Point X => g • z) h

theorem point_eq_of_borel_stabilizer_eq (hG : Variety.IsConnected G)
    (A : MorphicAction G X) (x y : Point X)
    (hB : IsBorelSubgroup (A.pointStabilizer x))
    (hy : ∃ g : Variety.Point G, A.toMulAction.smul g x = y)
    (he : A.pointStabilizer y = A.pointStabilizer x) : y = x := by
  obtain ⟨g,rfl⟩ := hy
  let := A.toMulAction
  have h := orbit_points_eq_of_conjugate_borels_eq hG (A.pointStabilizer x) hB x
    (fun a => (A.mem_pointStabilizer x a).symm) g 1 (by
      rw [ClosedSubgroup.conjugate_one, ← pointStabilizer_smul_eq_conjugate]
      exact he)
  exact h.trans (one_smul (Variety.Point G) x)

omit [IsAlgClosed k] in
theorem centralizer_preimage_eq_iff_pointwiseCentralizer_eq
    (S B C : ClosedSubgroup G) :
    S.centralizer.inclusion.closedSubgroupPreimage B =
      S.centralizer.inclusion.closedSubgroupPreimage C ↔
      B.pointwiseCentralizer S = C.pointwiseCentralizer S := by
  constructor
  · intro he
    apply SetLike.coe_injective
    ext g
    change (g ∈ B ∧ g ∈ S.centralizer) ↔ (g ∈ C ∧ g ∈ S.centralizer)
    constructor
    · rintro ⟨hb,hg⟩
      refine ⟨?_,hg⟩
      have hp : S.centralizer.pointEquiv.symm ⟨g,hg⟩ ∈
          S.centralizer.inclusion.closedSubgroupPreimage B := hb
      rw [he] at hp
      exact hp
    · rintro ⟨hc,hg⟩
      refine ⟨?_,hg⟩
      have hp : S.centralizer.pointEquiv.symm ⟨g,hg⟩ ∈
          S.centralizer.inclusion.closedSubgroupPreimage C := hc
      rw [← he] at hp
      exact hp
  · intro he
    apply SetLike.coe_injective
    ext g
    change S.centralizer.includePoint g ∈ B ↔ S.centralizer.includePoint g ∈ C
    have hg := (S.centralizer.pointEquiv g).property
    constructor
    · intro hb
      have hp : S.centralizer.includePoint g ∈ B.pointwiseCentralizer S := ⟨hb,hg⟩
      rw [he] at hp
      exact hp.1
    · intro hc
      have hp : S.centralizer.includePoint g ∈ C.pointwiseCentralizer S := ⟨hc,hg⟩
      rw [← he] at hp
      exact hp.1
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
