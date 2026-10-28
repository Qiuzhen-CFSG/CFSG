module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.TorusCurve
public import Theory.AlgebraicGroup.Dimension.Torus
public import Theory.AlgebraicGroup.Variety.SmoothIrreducibleNormal
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.BorelOrbit

/-!
# The actual one-dimensional Borel orbit is the projective line

The original projective Borel orbit is closed, irreducible and smooth, hence
normal. A dimension-one torus admits an actual multiplicative-group
isomorphism. A moved orbit point supplies the nonconstant torus curve inside
the same orbit. The preceding monomial-curve theorem produces the literal
scheme isomorphism over the original field, without a separability premise.

Source: Borel, Linear Algebraic Groups, §13.13(3–4). The rank-one source
producer supplies precisely the dimension and movement hypotheses below.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]
set_option backward.isDefEq.respectTransparency false

theorem projective_borel_orbit_iso_projectiveLine
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E))
    (he : ∀ g p, projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (hfix : ∀ g ∈ B.toSubgroup, A.toMulAction.smul g x = x)
    (hdim : dimension (A.orbitSubvariety x).toGeometric = 1)
    (hmove : ∃ (t : Variety.Point T.carrierVariety) (g : Variety.Point G),
      A.toMulAction.smul (T.includePoint t) (A.toMulAction.smul g x) ≠ A.toMulAction.smul g x) :
    ∃ e : (A.orbitSubvariety x).toGeometric.toScheme ≅ (projectiveLine k).toScheme,
      e.hom ≫ (projectiveLine k).structureMap = (A.orbitSubvariety x).toGeometric.structureMap := by
  have hclosed := A.orbit_isClosed_of_borel_fixed hG B hB x hfix
  have hirr := A.orbitSubvariety_isIrreducible_of_isClosed hG x hclosed
  have hn := isNormal_of_isIrreducible_of_smooth (A.orbitSubvariety x).toGeometric
    hirr (A.orbitSubvariety_smooth x)
  have : IsClosedImmersion (A.orbitSubvariety x).inclusion.hom :=
    A.orbitSubvariety_isClosedImmersion x hclosed
  obtain ⟨n, ⟨c⟩⟩ := hT
  have hnc : n = 1 := by
    have hd := algebraicGroupIso_dimension_eq c
    rw [dVariety_dimension_eq, hdimT] at hd
    exact_mod_cast hd
  subst n
  obtain ⟨t, g, ht⟩ := hmove
  obtain ⟨v, hv, hy⟩ := exists_projective_vector b (A.toMulAction.smul g x)
  refine exists_projectiveLine_iso_of_torus_curve hirr hn hdim (A.orbitSubvariety x).inclusion
    ρ hρ T ⟨1, ⟨c⟩⟩ c.hom c.toMulEquiv.surjective A b he v hv ?_ t ?_
  · intro s
    apply ((A.orbitSubvariety x).inclusion.point_mem_range_iff_closedPoint_mem_range _).mpr
    rw [A.orbitSubvariety_range]
    apply (A.point_mem_orbit_range_iff x _).mpr
    refine ⟨T.includePoint s * g, ?_⟩
    exact (A.toMulAction.mul_smul (T.includePoint s) g x).trans
      (congrArg (fun p => A.toMulAction.smul (T.includePoint s) p) hy)
  · simpa only [hy] using ht

end Theory.AlgebraicGroup.Bor1.FlagCurve
