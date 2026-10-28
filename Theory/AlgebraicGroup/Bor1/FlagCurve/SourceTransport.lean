module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.SourceWeights
/-!
# Point identities for the original cocharacter curve

The coordinate-change inverse is evaluated using the proved composition
identity, keeping the polynomial-curve scheme maps opaque during kernel
checking. The nonzero monomial point is exactly the original torus action
in the new weight basis; no orbit or stabilizer is replaced.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
open SeparatingBorel.ProjectiveLimit
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

set_option backward.isDefEq.respectTransparency false

private theorem basisChange_inverse_point
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (p : Point (projectiveSpace k E)) :
    projectiveBasisChange b b₀ (projectiveBasisChange b₀ b p) = p := by
  obtain ⟨v, hv, rfl⟩ := exists_projective_vector b p
  exact (congrArg (fun q => projectiveBasisChange b b₀ q)
    (projectiveBasisChange_vector b₀ b v hv)).trans (projectiveBasisChange_vector b b₀ v hv)

theorem topCurve_basisChange_nonzero
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (M : ℤ) (v : E) (hv : v ≠ 0)
    (h : ∃ i, characterCocharacterPairing T c (Additive.ofMul (χ i)) = M ∧ b.equivFun v i ≠ 0)
    (hM : ∀ i, b.equivFun v i ≠ 0 → characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M)
    (z : k) (hz : z ≠ 0) :
    topCurve (b.equivFun v) (fun l => characterCocharacterPairing T c (Additive.ofMul (χ l))) M h
      (affinePoint z) =
    projectiveBasisChange b b₀ (A.toMulAction.smul
      (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 z hz)⁻¹)))
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv))) := by
  let p := topCurve (b.equivFun v)
    (fun l => characterCocharacterPairing T c (Additive.ofMul (χ l))) M h (affinePoint z)
  have hd : originalTopCurve b₀ b
      (fun l => characterCocharacterPairing T c (Additive.ofMul (χ l))) M v h (affinePoint z) =
      projectiveBasisChange b₀ b p :=
    Variety.Geometric.Morphism.comp_apply_point
      (topCurve (b.equivFun v)
        (fun l => characterCocharacterPairing T c (Additive.ofMul (χ l))) M h)
      (projectiveBasisChange b₀ b) (affinePoint z)
  have hh := originalTopCurve_nonzero ρ T c A b₀ b χ he hweight M v hv h hM z hz
  exact (basisChange_inverse_point b₀ b p).symm.trans
    (congrArg (fun q => projectiveBasisChange b b₀ q) (hd.symm.trans hh))

end Theory.AlgebraicGroup.Bor1.FlagCurve
