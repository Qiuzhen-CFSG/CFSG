module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.FiniteFixed
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.Naturality
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.BorelOrbit

/-!
# Comparing attracting Borels through actual projective curves

The diagonal orbit through two points fixed by one Borel is closed. Therefore
two affine curves whose nonzero values belong to that orbit have their endpoint
pair in the same orbit. With equal Borel stabilizers, their endpoint stabilizers
coincide. A semiregular fixed point on the original Borel orbit has a Borel
stabilizer containing the original maximal torus.

These statements provide the model-independent comparison used for B(c) in
Borel, *Linear Algebraic Groups*, IV, 13.8 and 13.11--13.12.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open Variety.Geometric
open Variety.Geometric.ProjectivePolynomialCurve
variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X Y : Variety.Geometric k}

theorem endpoints_mem_common_borel_orbit
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (A : MorphicAction G X) (C : MorphicAction G Y) (x : Point X) (y : Point Y)
    (hx : ∀ b ∈ B.toSubgroup, A.toMulAction.smul b x = x)
    (hy : ∀ b ∈ B.toSubgroup, C.toMulAction.smul b y = y)
    (f : Variety.Geometric.Morphism (polynomialAffineLine k) X)
    (g : Variety.Geometric.Morphism (polynomialAffineLine k) Y)
    (hcurve : ∀ a : k, a ≠ 0 → ∃ s : Variety.Point G,
      A.toMulAction.smul s x = f (affinePoint a) ∧
      C.toMulAction.smul s y = g (affinePoint a)) :
    ∃ s : Variety.Point G,
      A.toMulAction.smul s x = f (affinePoint 0) ∧
      C.toMulAction.smul s y = g (affinePoint 0) := by
  let D := A.generationDiagonal C
  let z := prodPoint x y
  have hfix (b : Variety.Point G) (hb : b ∈ B.toSubgroup) : D.toMulAction.smul b z = z := by
    change (A.generationDiagonal C).toMulAction.smul b (prodPoint x y) = prodPoint x y
    rw [MorphicAction.generationDiagonal_smul, hx b hb, hy b hb]
  have hclosed := D.orbit_isClosed_of_borel_fixed hG B hB z hfix
  let p := Variety.Geometric.Morphism.pair f g
  have hpre : IsClosed (p.hom ⁻¹' Set.range (D.orbitMorphismAt z).hom) :=
    hclosed.preimage p.hom.continuous
  have hmem (a : k) (ha : a ≠ 0) :
      (affinePoint a).1 (IsLocalRing.closedPoint k) ∈ p.hom ⁻¹' Set.range (D.orbitMorphismAt z).hom := by
    change (p (affinePoint a)).1 (IsLocalRing.closedPoint k) ∈ Set.range (D.orbitMorphismAt z).hom
    apply ((D.orbitMorphismAt z).point_mem_range_iff_closedPoint_mem_range _).mp
    obtain ⟨s, hs, ht⟩ := hcurve a ha
    refine ⟨(affinePointEquiv G).symm s, ?_⟩
    rw [D.orbitMorphismAt_apply]
    change (A.generationDiagonal C).toMulAction.smul s (prodPoint x y) = p (affinePoint a)
    rw [MorphicAction.generationDiagonal_smul, hs, ht]
    exact (Variety.Geometric.Morphism.pair_apply f g _).symm
  have hz := affinePoint_mem_of_nonzero hpre hmem 0
  change (p (affinePoint 0)).1 (IsLocalRing.closedPoint k) ∈ Set.range (D.orbitMorphismAt z).hom at hz
  obtain ⟨s, hs⟩ := ((D.orbitMorphismAt z).point_mem_range_iff_closedPoint_mem_range _).mpr hz
  let t := affinePointEquiv G s
  have ht : D.toMulAction.smul t z = p (affinePoint 0) := by
    rw [← D.orbitMorphismAt_apply z t]
    exact ((congrArg (D.orbitMorphismAt z) ((affinePointEquiv G).symm_apply_apply s)).trans hs)
  change (A.generationDiagonal C).toMulAction.smul t (prodPoint x y) = p (affinePoint 0) at ht
  rw [MorphicAction.generationDiagonal_smul, Variety.Geometric.Morphism.pair_apply] at ht
  refine ⟨t, ?_, ?_⟩
  · exact (fst_prodPoint _ _).symm.trans ((congrArg (fst X Y) ht).trans (fst_prodPoint _ _))
  · exact (snd_prodPoint _ _).symm.trans ((congrArg (snd X Y) ht).trans (snd_prodPoint _ _))

theorem endpoint_stabilizers_eq_of_common_borel_curves
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (A : MorphicAction G X) (C : MorphicAction G Y) (x : Point X) (y : Point Y)
    (hx : ∀ b : Variety.Point G, A.toMulAction.smul b x = x ↔ b ∈ B.toSubgroup)
    (hy : ∀ b : Variety.Point G, C.toMulAction.smul b y = y ↔ b ∈ B.toSubgroup)
    (f : Variety.Geometric.Morphism (polynomialAffineLine k) X)
    (g : Variety.Geometric.Morphism (polynomialAffineLine k) Y)
    (hcurve : ∀ a : k, a ≠ 0 → ∃ s : Variety.Point G,
      A.toMulAction.smul s x = f (affinePoint a) ∧
      C.toMulAction.smul s y = g (affinePoint a)) :
    A.pointStabilizer (f (affinePoint 0)) = C.pointStabilizer (g (affinePoint 0)) := by
  obtain ⟨s, hs, ht⟩ := endpoints_mem_common_borel_orbit hG B hB A C x y
    (fun b hb => (hx b).mpr hb) (fun b hb => (hy b).mpr hb) f g hcurve
  rw [← hs, ← ht]
  apply SetLike.coe_injective
  ext a
  change a ∈ (A.pointStabilizer (A.toMulAction.smul s x)).toSubgroup ↔
    a ∈ (C.pointStabilizer (C.toMulAction.smul s y)).toSubgroup
  rw [A.mem_pointStabilizer, C.mem_pointStabilizer]
  have ha : A.toMulAction.smul a (A.toMulAction.smul s x) = A.toMulAction.smul s x ↔
      A.toMulAction.smul (s⁻¹ * a * s) x = x := by
    let := A.toMulAction
    change a • (s • x) = s • x ↔ (s⁻¹ * a * s) • x = x
    constructor
    · intro h
      simpa only [mul_smul, inv_smul_smul] using congrArg (fun z : Point X => s⁻¹ • z) h
    · intro h
      simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : Point X => s • z) h
  have hb : C.toMulAction.smul a (C.toMulAction.smul s y) = C.toMulAction.smul s y ↔
      C.toMulAction.smul (s⁻¹ * a * s) y = y := by
    let := C.toMulAction
    change a • (s • y) = s • y ↔ (s⁻¹ * a * s) • y = y
    constructor
    · intro h
      simpa only [mul_smul, inv_smul_smul] using congrArg (fun z : Point Y => s⁻¹ • z) h
    · intro h
      simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : Point Y => s • z) h
  rw [ha, hb, hx, hy]
/-- The stabilizer of an actual regular-cocharacter-fixed point of the
original Borel orbit is a Borel containing the original maximal torus. -/
theorem isBorel_pointStabilizer_containing_torus
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (A : MorphicAction G X) (x : Point X)
    (hx : ∀ b : Variety.Point G, A.toMulAction.smul b x = x ↔ b ∈ B.toSubgroup)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) (c : ClosedSubgroupTorusCocharacter T)
    (hc : (T.inclusion.comp c).imageClosedSubgroup.centralizer = T.centralizer)
    (y : Point X) (hy : ∃ g : Variety.Point G, A.toMulAction.smul g x = y)
    (hfix : ∀ t : Variety.Point (KMult k), A.toMulAction.smul (T.includePoint (c.onPoints t)) y = y) :
    IsBorelSubgroup (A.pointStabilizer y) ∧ T ≤ A.pointStabilizer y := by
  let := A.toMulAction
  have ht := (cocharacter_fixed_orbit_iff_torus_fixed hG B hB x hx T hT c hc y hy).mp hfix
  refine ⟨?_, ?_⟩
  · obtain ⟨g, rfl⟩ := hy
    have he : A.pointStabilizer (A.toMulAction.smul g x) = B.conjugate g := by
      apply SetLike.coe_injective
      ext a
      change a ∈ (A.pointStabilizer (A.toMulAction.smul g x)).toSubgroup ↔ a ∈ B.conjugate g
      rw [A.mem_pointStabilizer, B.mem_conjugate_iff, ← hx]
      change a • (g • x) = g • x ↔ (g⁻¹ * a * g) • x = x
      constructor
      · intro h
        simpa only [mul_smul, inv_smul_smul] using congrArg (fun z : Point X => g⁻¹ • z) h
      · intro h
        simpa only [mul_smul, smul_inv_smul] using congrArg (fun z : Point X => g • z) h
    rw [he]
    exact hB.conjugate g
  · intro t htT
    apply (A.mem_pointStabilizer y t).mpr
    exact ht (T.pointEquiv.symm ⟨t, htT⟩)
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
