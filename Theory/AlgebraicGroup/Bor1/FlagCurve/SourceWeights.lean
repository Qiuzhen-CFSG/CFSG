module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.SourceCurves

/-!
# Nontrivial torus actions have distinct occupied weights

If all occupied weights have the same cocharacter value, the vector equals
its highest-weight projection and its projective point is fixed. Thus a
surjective one-dimensional cocharacter moving the actual source point gives
an occupied positive exponent. This discharges nonconstancy in Borel §13.13.
-/

public noncomputable section

open AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
open SeparatingBorel.ProjectiveLimit
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

set_option backward.isDefEq.respectTransparency false in
theorem exists_occupied_positive_exponent
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (hc : Function.Surjective c.onPoints)
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
    (t : Variety.Point T.carrierVariety)
    (hmove : A.toMulAction.smul (T.includePoint t)
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) ≠
      projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) :
    ∃ i, (M - characterCocharacterPairing T c (Additive.ofMul (χ i))).toNat ≠ 0 ∧
      b.equivFun v i ≠ 0 := by
  by_contra hnone
  have htop : topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v = v := by
    apply b.equivFun.injective
    funext i
    simp only [topVector, LinearEquiv.apply_symm_apply, topCoordinates]
    by_cases hci : b.equivFun v i = 0
    · simp [hci]
    · have hz : (M - characterCocharacterPairing T c (Additive.ofMul (χ i))).toNat = 0 := by
        by_contra hn
        exact hnone ⟨i, hn, hci⟩
      have hi := hM i hci
      have heq : characterCocharacterPairing T c (Additive.ofMul (χ i)) = M := by omega
      simp [heq]
  obtain ⟨z, rfl⟩ := hc t
  exact hmove (by simpa only [htop] using
    topVector_projective_fixed ρ T c A b₀ b χ he hweight M v h z)

end Theory.AlgebraicGroup.Bor1.FlagCurve
