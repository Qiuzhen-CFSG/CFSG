module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Regular
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.Source
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.FiniteBorels
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.ChevalleyAction
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.BorelOrbit
/-!
# Finite fixed points on the actual Borel orbit

A point on an orbit with Borel stabilizer determines the conjugate Borel that
stabilizes it. Borel self-normalization makes this assignment injective. Fixed
points of a subtorus therefore inject into the literal family of Borels
containing that subtorus, which is finite when its centralizer is solvable.

For the separating cocharacter, its image centralizer equals the maximal torus
centralizer and is solvable. The final theorem applies this argument to the
actual rational Chevalley projective action, whose orbit is closed. These are
the geometric inputs to the one-parameter attracting-point construction.

Source: Borel, *Linear Algebraic Groups*, IV, 11.16, 11.18, 13.1 and 13.8,
`refs/KGroup/Bor1/Chapter4.tex`.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X : Type*} [MulAction (Variety.Point G) X]

theorem orbit_points_eq_of_conjugate_borels_eq
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (x : X) (hstab : ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup)
    (a b : Variety.Point G) (he : B.conjugate a = B.conjugate b) : a • x = b • x := by
  let n := a⁻¹ * b
  have hn : B.conjugate n = B := by
    dsimp only [n]
    rw [← ClosedSubgroup.conjugate_conjugate, ← he,
      ClosedSubgroup.conjugate_conjugate, inv_mul_cancel, ClosedSubgroup.conjugate_one]
  have hnN : n ∈ B.normalizer.toSubgroup := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro z
    have hz := B.mem_conjugate_iff n (n * z * n⁻¹)
    rw [hn] at hz
    change (n * z * n⁻¹ ∈ B.toSubgroup ↔ n⁻¹ * (n * z * n⁻¹) * n ∈ B.toSubgroup) at hz
    simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hz.symm
  rw [BorelSelfNormalizer.normalizer_eq hG B hB] at hnN
  have hfix := (hstab n).mpr hnN
  have h := congrArg (fun y : X => a • y) hfix
  simpa only [n, ← mul_smul, mul_inv_cancel_left] using h.symm

theorem finite_fixed_orbit_of_finite_borels
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (x : X) (hstab : ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup)
    (S : ClosedSubgroup G) [Finite (BorelContainingIndex S)] :
    {y : X | (∃ g : Variety.Point G, g • x = y) ∧
      ∀ s : Variety.Point G, s ∈ S.toSubgroup → s • y = y}.Finite := by
  classical
  let F := {y : X | (∃ g : Variety.Point G, g • x = y) ∧
      ∀ s : Variety.Point G, s ∈ S.toSubgroup → s • y = y}
  let g (y : F) := y.2.1.choose
  have hg (y : F) : g y • x = y.1 := y.2.1.choose_spec
  have hle (y : F) : S ≤ B.conjugate (g y) := by
    intro s hs
    apply (B.mem_conjugate_iff (g y) s).mpr
    apply (hstab _).mp
    have he := congrArg (fun z : X => (g y)⁻¹ • z) (y.2.2 s hs)
    rw [← hg y] at he
    simpa only [mul_smul, inv_smul_smul] using he
  let f : F → BorelContainingIndex S := fun y =>
    ⟨B.conjugate (g y), hB.conjugate (g y), hle y⟩
  have hinj : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    rw [← hg y, ← hg z]
    exact orbit_points_eq_of_conjugate_borels_eq hG B hB x hstab _ _ (congrArg Subtype.val he)
  let : Finite F := Finite.of_injective f hinj
  exact Set.toFinite F

theorem finite_fixed_orbit_of_solvable_centralizer
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (x : X) (hstab : ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup)
    (S : ClosedSubgroup G) (hS : IsSubtorus S)
    (hsolv : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety)) :
    {y : X | (∃ g : Variety.Point G, g • x = y) ∧
      ∀ s : Variety.Point G, s ∈ S.toSubgroup → s • y = y}.Finite := by
  let := SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.finite_borels_containing_subtorus_of_solvable_centralizer hG hS hsolv
  exact finite_fixed_orbit_of_finite_borels hG B hB x hstab S

theorem finite_fixed_orbit_of_semiregular_cocharacter
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (x : X) (hstab : ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer) :
    {y : X | (∃ g : Variety.Point G, g • x = y) ∧
      ∀ t : Variety.Point (KMult k), T.includePoint (c.onPoints t) • y = y}.Finite := by
  let S := (T.inclusion.comp c).imageClosedSubgroup
  have hsolv : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety) := by
    rw [hc]
    exact (SemisimpleCenterContainment.CartanGeometry.maximalTorus_centralizer_connected_solvable hG hT).2
  have hf := finite_fixed_orbit_of_solvable_centralizer hG B hB x hstab S
    (morphism_image_isTorus (T.inclusion.comp c) (dVariety_isTorus 1)) hsolv
  apply hf.subset
  rintro y ⟨hy, hfix⟩
  refine ⟨hy, ?_⟩
  rintro s ⟨t, rfl⟩
  exact hfix t

open Variety.Geometric
open scoped LinearAlgebra.Projectivization

/-- The literal Chevalley orbit for a Borel has finitely many fixed points
for the separating semiregular cocharacter. -/
theorem exists_projective_borel_action_with_finite_fixed_orbit
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer) :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (ρ : RationalRepresentation G E)
      (b : Module.Basis (Fin (Module.finrank k E)) k E)
      (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E)),
      IsRationalRepresentation ρ ∧
      (∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
        projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
        Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
          (projectiveSpacePointEquivOf b p)) ∧
      (∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup) ∧
      IsClosed (Set.range (A.orbitMorphismAt x).hom) ∧
      {y : Point (projectiveSpace k E) |
        (∃ g : Variety.Point G, A.toMulAction.smul g x = y) ∧
        ∀ t : Variety.Point (KMult k),
          A.toMulAction.smul (T.includePoint (c.onPoints t)) y = y}.Finite := by
  obtain ⟨E, hEa, hEm, hEf, ρ, b, A, x, hρ, he, hx⟩ :=
    TorusBorelGeneration.exists_projective_action_stabilizer B
  let := A.toMulAction
  exact ⟨E, hEa, hEm, hEf, ρ, b, A, x, hρ, he, hx,
    A.orbit_isClosed_of_borel_fixed hG B hB x (fun g hg => (hx g).mpr hg),
    finite_fixed_orbit_of_semiregular_cocharacter hG B hB x hx T hT c hc⟩


/-- On the actual Borel orbit, the regular cocharacter and the torus have
exactly the same fixed points. -/
theorem cocharacter_fixed_orbit_iff_torus_fixed
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (x : X) (hstab : ∀ g : Variety.Point G, g • x = x ↔ g ∈ B.toSubgroup)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer)
    (y : X) (hy : ∃ g : Variety.Point G, g • x = y) :
    (∀ t : Variety.Point (KMult k), T.includePoint (c.onPoints t) • y = y) ↔
      ∀ t : Variety.Point T.carrierVariety, T.includePoint t • y = y := by
  obtain ⟨g, rfl⟩ := hy
  have hfix (a : Variety.Point G) : a • (g • x) = g • x ↔ a ∈ B.conjugate g := by
    rw [B.mem_conjugate_iff, ← hstab]
    constructor
    · intro ha
      have hh := congrArg (fun z : X => g⁻¹ • z) ha
      simpa only [mul_smul, inv_smul_smul] using hh
    · intro ha
      have hh := congrArg (fun z : X => g • z) ha
      simpa only [mul_smul, smul_inv_smul] using hh
  constructor
  · intro h
    let S := (T.inclusion.comp c).imageClosedSubgroup
    have hSB : S ≤ B.conjugate g := by
      rintro a ⟨t, rfl⟩
      exact (hfix _).mp (h t)
    have hsolv : Group.IsSolvable (Variety.Point S.centralizer.carrierVariety) := by
      rw [hc]
      exact (SemisimpleCenterContainment.CartanGeometry.maximalTorus_centralizer_connected_solvable hG hT).2
    have hCB := SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.centralizer_le_borel_of_solvable
      hG (morphism_image_isTorus (T.inclusion.comp c) (dVariety_isTorus 1)) (hB.conjugate g) hSB hsolv
    intro t
    apply (hfix _).mpr
    apply hCB
    change T.includePoint t ∈ S.centralizer
    rw [hc]
    exact maximalTorus_le_centralizer hT (T.pointEquiv t).property
  · intro h t
    exact h (c.onPoints t)
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
