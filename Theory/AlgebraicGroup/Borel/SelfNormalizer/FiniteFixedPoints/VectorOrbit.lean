module

public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints.VectorOrbit.AffineAction
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.FiniteFixedPoints.ChevalleyLine
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Tori.CentralMaximalNilpotent.TorusFree.BorelCentralizer.CompleteOrbit

/-!
# Constancy of Borel-fixed vector orbits

A complete Borel homogeneous-space model and Borel conjugacy give a complete
transitive space with stabilizer the given Borel. The regular affine action of
a rational representation then satisfies the diagonal-orbit constancy theorem:
the orbit of a pair projects bijectively to the complete homogeneous orbit.
The smooth target is normal, so normalization makes the irreducible pair orbit
complete, and its projection to affine space is constant.

The final theorem applies this argument to the literal normalizer Chevalley
representation. It discharges the geometric premise in the finite-fixed branch
of Borel, *Linear Algebraic Groups*, Theorem 11.16(iii),
`refs/KGroup/Bor1/Chapter4.tex`, line 229. No normality, separability or regular
descent hypothesis is required.
-/

universe u v
namespace Theory.AlgebraicGroup.BorelSelfNormalizer
open Variety.Geometric Bor1 BorelGeometricConjugacy
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A Borel-fixed point of a regular affine action of a connected group is fixed
by the whole group. -/
public theorem affine_fixed_of_borel_fixed
    {Y : Variety k} (C : MorphicAction G (ofAffine Y))
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (y : Point (ofAffine Y))
    (hy : ∀ b : Variety.Point G, b ∈ B.toSubgroup → C.toMulAction.smul b y = y) :
    ∀ g : Variety.Point G, C.toMulAction.smul g y = y := by
  obtain ⟨B₀, hB₀, ⟨M⟩⟩ := exists_borel_completeModel B hB
  obtain ⟨t, ht⟩ := conjugacy hB₀ hB
  let x : Point M.variety := M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ t)
  have htrans (z : Point M.variety) :
      ∃ g : Variety.Point G, M.action.toMulAction.smul g x = z := by
    obtain ⟨s, hs⟩ := borelHomogeneousSpace.projection_surjective B₀ (M.pointEquiv z)
    refine ⟨s * t⁻¹, M.pointEquiv.injective ?_⟩
    rw [M.equivariant]
    change (s * t⁻¹) • (M.pointEquiv (M.pointEquiv.symm
      (borelHomogeneousSpace.projection B₀ t))) = M.pointEquiv z
    rw [Equiv.apply_symm_apply, ← borelHomogeneousSpace.projection_mul,
      inv_mul_cancel_right]
    exact hs
  have hstab (b : Variety.Point G) (hb : M.action.toMulAction.smul b x = x) :
      b ∈ B.toSubgroup := by
    rw [ht]
    apply (projectivization_fixed_iff_mem_conjugate B₀ t b).mp
    have hp := congrArg M.pointEquiv hb
    rw [M.equivariant] at hp
    change b • M.pointEquiv (M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ t)) =
      M.pointEquiv (M.pointEquiv.symm (borelHomogeneousSpace.projection B₀ t)) at hp
    rw [Equiv.apply_symm_apply] at hp
    exact congrArg (fun q : borelHomogeneousSpace B₀ => (q : borelPluckerAmbient B₀)) hp
  exact M.action.fixed_on_affine_of_complete_transitive C hG M.complete x htrans y
    (fun b hb => hy b (hstab b hb))

/-- In a finite-dimensional rational representation of a connected group,
every vector fixed by a Borel subgroup is fixed by the whole group. -/
public theorem rationalRepresentation_fixed_of_borel_fixed
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (d : V) (hd : ∀ b : Variety.Point G, b ∈ B.toSubgroup → (ρ.action b).1 d = d) :
    ∀ g : Variety.Point G, (ρ.action g).1 d = d := by
  classical
  let b := (Module.finBasis k V).reindex (Equiv.ulift.{u}.symm)
  let C := vectorAffineAction ρ hρ b
  let y := (vectorAffinePointEquiv b).symm d
  have hy (g : Variety.Point G) (hg : g ∈ B.toSubgroup) :
      C.toMulAction.smul g y = y := by
    apply (vectorAffinePointEquiv b).injective
    dsimp only [C, y]
    rw [vectorAffineAction_apply, Equiv.apply_symm_apply, hd g hg]
  have hall := affine_fixed_of_borel_fixed C hG B hB y hy
  intro g
  have h := congrArg (vectorAffinePointEquiv b) (hall g)
  dsimp only [C, y] at h
  simpa only [vectorAffineAction_apply, Equiv.apply_symm_apply] using h

/-- The exact vector-orbit constancy premise of the finite-fixed Chevalley branch
of Borel 11.16(iii), with all geometric hypotheses discharged. -/
public theorem normalizerChevalley_fixed_of_borel_fixed
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (d : NormalizerChevalleySpace B)
    (hd : ∀ b : Variety.Point G, b ∈ B.toSubgroup →
      ((normalizerChevalleyRepresentation B).action b).1 d = d) :
    ∀ g : Variety.Point G, ((normalizerChevalleyRepresentation B).action g).1 d = d := by
  exact rationalRepresentation_fixed_of_borel_fixed
    (normalizerChevalleyRepresentation B) (normalizerChevalleyRepresentation_isRational B)
    hG B hB d hd

end Theory.AlgebraicGroup.BorelSelfNormalizer
