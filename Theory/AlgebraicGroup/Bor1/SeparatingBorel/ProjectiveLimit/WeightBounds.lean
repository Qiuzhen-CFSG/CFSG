module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.Attractor

/-!
# Character bounds at the projective attractor

A nonzero coordinate of a torus weight vector has that same algebraic weight.
Consequently the global maximal exponent retained by the attractor theorem
dominates the character exponent of every torus-fixed point in the original
orbit, and equals the character exponent at the attractor's open coordinate.
These are the sign comparisons used to orient the two fixed points in Borel
IV, 13.11–13.12. The character itself is the genuine regular character supplied
by the fixed-point weight theorem.
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

omit [IsAlgClosed k] [FiniteDimensional k E] in
theorem weight_eq_of_nonzero_coordinate
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (w : E) (η : TorusWeight T)
    (hw : ∀ t : Variety.Point T.carrierVariety,
      (ρ.action (T.includePoint t)).1 w = η.pointCharacter t • w)
    (i : Fin (Module.finrank k E)) (hi : b.equivFun w i ≠ 0) : χ i = η := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  have h := congrArg (fun z => b.equivFun z i) (hw t)
  rw [torus_weight_basis_coordinates ρ T b χ hweight, map_smul,
    Pi.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hi h

theorem weight_pairing_le_of_orbit_point
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
    (v : E) (hv : v ≠ 0) (M : ℤ)
    (hM : ∀ (g : Variety.Point G) i, b.equivFun ((ρ.action g).1 v) i ≠ 0 →
      characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M)
    (w : E) (η : TorusWeight T) (hw : IsWeightVector ρ T w η)
    (horbit : ∃ g : Variety.Point G,
      A.toMulAction.smul g (projectivePointOfVector (b₀.equivFun v)
        (b₀.equivFun.map_ne_zero_iff.mpr hv)) =
        projectivePointOfVector (b₀.equivFun w) (b₀.equivFun.map_ne_zero_iff.mpr hw.1)) :
    characterCocharacterPairing T c (Additive.ofMul η) ≤ M := by
  obtain ⟨g, hg⟩ := horbit
  have hp := congrArg (projectiveSpacePointEquivOf b₀) hg
  rw [he, projectiveSpacePointEquivOf_projectivePointOfVector b₀ v hv,
    projectiveSpacePointEquivOf_projectivePointOfVector b₀ w hw.1,
    Projectivization.map_mk] at hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hp
  have ha0 : a ≠ 0 := by
    intro hz
    have hgv : (ρ.action g).1 v ≠ 0 := (ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv
    apply hgv
    rw [← ha, hz, zero_smul]
  obtain ⟨i, hi⟩ : ∃ i, b.equivFun w i ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using b.equivFun.map_ne_zero_iff.mpr hw.1
  have hη : χ i = η := weight_eq_of_nonzero_coordinate ρ T b χ hweight w η hw.2 i hi
  have hcoord : b.equivFun ((ρ.action g).1 v) i ≠ 0 := by
    rw [← ha, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero ha0 hi
  simpa only [hη] using hM g i hcoord

theorem weight_pairing_eq_of_mem_attractor_coordinate
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (j : Fin (Module.finrank k E)) (M : ℤ)
    (hj : characterCocharacterPairing T c (Additive.ofMul (χ j)) = M)
    (w : E) (η : TorusWeight T) (hw : IsWeightVector ρ T w η)
    (hopen : (projectivePointOfVector (b₀.equivFun w)
      (b₀.equivFun.map_ne_zero_iff.mpr hw.1)).1 (IsLocalRing.closedPoint k) ∈
        projectiveHyperplaneOpen b₀ (b.coord j)) :
    characterCocharacterPairing T c (Additive.ofMul η) = M := by
  have hcoord : b.equivFun w j ≠ 0 :=
    (projectiveHyperplaneOpen_vector_mem_iff b₀ (b.coord j) w hw.1).mp hopen
  have hη := weight_eq_of_nonzero_coordinate ρ T b χ hweight w η hw.2 j hcoord
  simpa only [hη] using hj

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
