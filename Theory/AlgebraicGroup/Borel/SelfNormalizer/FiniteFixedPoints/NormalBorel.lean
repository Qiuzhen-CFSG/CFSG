module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Bor1.CompleteNormalOrbitFixedPoint

/-!
# A normal Borel of a connected algebraic group is the whole group

Borel conjugacy transports the constructed complete model to the given normal
Borel. Every point stabilizer in that model is its literal conjugate and hence
the Borel itself. A closed orbit with normal stabilizer is a point: the genuine
normal affine quotient maps regularly and bijectively to the smooth orbit;
normalization transfers completeness to the quotient, whose affine identity
map is constant. Thus the Borel contains every group point.

This supplies the tail after `G = N_G(B)` in Borel, *Linear Algebraic Groups*,
Theorem 11.16(iii), `refs/KGroup/Bor1/Chapter4.tex`, line 229. Normality is
assumed only for this tail, and is discharged by the normalizer calculation
in the finite fixed-torus assembly.
-/

universe u
namespace Theory.AlgebraicGroup.BorelSelfNormalizer
open BorelGeometricConjugacy Bor1 Variety.Geometric
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

public theorem completeModel_stabilizer_eq_conjugate
    {B : ClosedSubgroup G} (M : CompleteModel B) (x : Point M.variety)
    (g : Variety.Point G) (hg : borelHomogeneousSpace.projection B g = M.pointEquiv x) :
    M.action.pointStabilizer x = B.conjugate g := by
  apply SetLike.ext
  intro s
  change s ∈ (M.action.pointStabilizer x).toSubgroup ↔ s ∈ (B.conjugate g).toSubgroup
  rw [M.action.mem_pointStabilizer]
  rw [← M.pointEquiv.injective.eq_iff, M.equivariant, ← hg]
  rw [Subtype.ext_iff]
  change s • (borelHomogeneousSpace.projection B g : borelPluckerAmbient B) =
    (borelHomogeneousSpace.projection B g : borelPluckerAmbient B) ↔ _
  rw [borelHomogeneousSpace.projection_coe]
  exact projectivization_fixed_iff_mem_conjugate B g s

/-- A normal Borel in a connected algebraic group is the whole group. -/
public theorem borel_eq_top_of_normal
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (hN : B.toSubgroup.Normal) : B = ClosedSubgroup.top := by
  let := hN
  have hconj (g : Variety.Point G) : B.conjugate g = B := by
    apply B.conjugate_eq_self_of_mem_normalizer g
    change g ∈ Subgroup.normalizer (B.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨R, hR, ⟨M⟩⟩ := exists_borel_completeModel B hB
  obtain ⟨g, hg⟩ := conjugacy hB hR
  have hRB : R = B := hg.trans (hconj g)
  clear hg hR
  subst R
  obtain ⟨x₀⟩ := M.nonempty
  let : Nonempty M.variety.toScheme := ⟨x₀.1 (IsLocalRing.closedPoint k)⟩
  obtain ⟨x, _, hclosed⟩ := M.action.exists_smooth_closed_orbit
  obtain ⟨a, ha⟩ := borelHomogeneousSpace.projection_surjective B (M.pointEquiv x)
  have hstab : M.action.pointStabilizer x = B :=
    (completeModel_stabilizer_eq_conjugate M x a ha).trans (hconj a)
  have hstabNormal : (M.action.pointStabilizer x).toSubgroup.Normal := by
    rwa [hstab]
  have hfix := M.action.fixed_of_isClosed_orbit_of_normal_stabilizer
    hG M.complete x hclosed hstabNormal
  apply SetLike.ext
  intro s
  constructor
  · intro _
    trivial
  · intro _
    change s ∈ B.toSubgroup
    rw [← hstab, M.action.mem_pointStabilizer]
    exact hfix s

end Theory.AlgebraicGroup.BorelSelfNormalizer
