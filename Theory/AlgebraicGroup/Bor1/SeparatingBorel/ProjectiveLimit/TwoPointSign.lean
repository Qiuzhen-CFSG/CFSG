module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.SourceAttractor
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.WeightBounds

/-!
# Selecting the attracting point by a character sign

On an actual projective orbit whose cocharacter fixed locus is contained in
two regular torus-weight points, positivity of their character ratio selects
the first point as the highest attractor. The second point cannot be the
attractor: its exponent would equal the global maximum, contradicting the
larger exponent of the first point. This is the literal sign comparison needed
for the two centralizer orbits in Borel IV, 13.11–13.12.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit

universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

theorem character_ratio_pairing_pos_iff (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (α β : TorusWeight T) :
    0 < characterCocharacterPairing T c (Additive.ofMul (α / β)) ↔
      characterCocharacterPairing T c (Additive.ofMul β) <
        characterCocharacterPairing T c (Additive.ofMul α) := by
  change 0 < characterCocharacterPairing T c (Additive.ofMul α - Additive.ofMul β) ↔ _
  rw [map_sub, sub_pos]

/-- The positive character-ratio endpoint is the actual attracting point,
with the full exact open basin and the original-action affine curves. -/
theorem exists_attractor_at_positive_weight_point
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (x : Point (projectiveSpace k E))
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (wPlus wMinus : E) (α β : TorusWeight T)
    (hwPlus : IsWeightVector ρ T wPlus α) (hwMinus : IsWeightVector ρ T wMinus β)
    (hplus : ∃ g : Variety.Point G, A.toMulAction.smul g x =
      projectivePointOfVector (b₀.equivFun wPlus) (b₀.equivFun.map_ne_zero_iff.mpr hwPlus.1))
    (hcover : ∀ y ∈ fixedOrbit A T c x,
      y = projectivePointOfVector (b₀.equivFun wPlus) (b₀.equivFun.map_ne_zero_iff.mpr hwPlus.1) ∨
      y = projectivePointOfVector (b₀.equivFun wMinus) (b₀.equivFun.map_ne_zero_iff.mpr hwMinus.1))
    (hpositive : 0 < characterCocharacterPairing T c (Additive.ofMul (α / β))) :
    ∃ U : (projectiveSpace k E).toScheme.Opens,
      (projectivePointOfVector (b₀.equivFun wPlus) (b₀.equivFun.map_ne_zero_iff.mpr hwPlus.1)).1
        (IsLocalRing.closedPoint k) ∈ U ∧
      IsOpen {g : Variety.Point G | (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ U} ∧
      (∃ g : Variety.Point G, (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈ U) ∧
      ∀ z : Point (projectiveSpace k E), (∃ g : Variety.Point G, A.toMulAction.smul g x = z) →
        (z.1 (IsLocalRing.closedPoint k) ∈ U ↔
          ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E),
            f (ProjectivePolynomialCurve.affinePoint 0) =
              projectivePointOfVector (b₀.equivFun wPlus) (b₀.equivFun.map_ne_zero_iff.mpr hwPlus.1) ∧
            ∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
              A.toMulAction.smul
                (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) z) := by
  have hfinite : (fixedOrbit A T c x).Finite := by
    apply ((Set.finite_singleton
      (projectivePointOfVector (b₀.equivFun wMinus) (b₀.equivFun.map_ne_zero_iff.mpr hwMinus.1))).insert
      (projectivePointOfVector (b₀.equivFun wPlus) (b₀.equivFun.map_ne_zero_iff.mpr hwPlus.1))).subset
    intro y hy
    rcases hcover y hy with h | h <;> simp only [h, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, or_true]
  obtain ⟨b, χ, hweight⟩ := exists_finite_torus_weight_basis ρ hρ T hT
  obtain ⟨v, hv, rfl⟩ := exists_projective_vector b₀ x
  obtain ⟨M, j, y, hj, hM, hy, hyU, hopen, hne, hcurves, _⟩ :=
    exists_attractor_in_weight_basis ρ hρ hG T c A b₀ b χ he hweight v hv hclosed hfinite
  have hyplus : y = projectivePointOfVector (b₀.equivFun wPlus)
      (b₀.equivFun.map_ne_zero_iff.mpr hwPlus.1) := by
    rcases hcover y hy with h | h
    · exact h
    · have hβ : characterCocharacterPairing T c (Additive.ofMul β) = M :=
        weight_pairing_eq_of_mem_attractor_coordinate ρ T c b₀ b χ hweight j M hj wMinus β hwMinus
          (h ▸ hyU)
      have hα := weight_pairing_le_of_orbit_point ρ T c A b₀ b χ he hweight v hv M hM
        wPlus α hwPlus hplus
      have hlt := (character_ratio_pairing_pos_iff T c α β).mp hpositive
      omega
  refine ⟨projectiveHyperplaneOpen b₀ (b.coord j), hyplus ▸ hyU, hopen, hne, ?_⟩
  intro z hz
  obtain ⟨g, rfl⟩ := hz
  constructor
  · intro hg
    obtain ⟨f, hf, hc⟩ := hcurves g hg
    exact ⟨f, hf.trans hyplus, hc⟩
  · rintro ⟨f, hf, hc⟩
    apply mem_hyperplaneOpen_of_cocharacter_limit ρ T c A b₀ b χ he hweight j _ f hc
    rw [hf, ← hyplus]
    exact hyU

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
