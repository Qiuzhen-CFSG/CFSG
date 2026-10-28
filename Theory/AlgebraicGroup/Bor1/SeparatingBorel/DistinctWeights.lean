module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.Opposite
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.WeightBounds
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.OrbitLine

/-!
# The two fixed-point characters are distinct

On a connected closed projective orbit with only two cocharacter-fixed
points, choose the largest weights for a parameter and its inverse. If the
two fixed points had the same torus character, these two bounds would force
every orbit vector into the same cocharacter eigenspace. The proved
one-dimensional highest-weight span would then make the entire projective
orbit constant, contradicting the two distinct orbit points.

All weights, curves and orbit vectors come from the original rational action.
Source: Borel, *Linear Algebraic Groups*, IV, 13.3, 13.8 and 13.11(3).
-/

public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel
open ProjectiveLimit
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

theorem two_fixed_point_weights_ne
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (v w : E) (α β : TorusWeight T)
    (hv : IsWeightVector ρ T v α) (hw : IsWeightVector ρ T w β)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv.1))).hom))
    (hworb : ∃ g : Variety.Point G,
      A.toMulAction.smul g (projectivePointOfVector (b₀.equivFun v)
        (b₀.equivFun.map_ne_zero_iff.mpr hv.1)) =
      projectivePointOfVector (b₀.equivFun w) (b₀.equivFun.map_ne_zero_iff.mpr hw.1))
    (hne : projectivePointOfVector (b₀.equivFun w) (b₀.equivFun.map_ne_zero_iff.mpr hw.1) ≠
      projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv.1))
    (htwo : ∀ y ∈ fixedOrbit A T c
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv.1)),
      y = projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv.1) ∨
      y = projectivePointOfVector (b₀.equivFun w) (b₀.equivFun.map_ne_zero_iff.mpr hw.1)) : α ≠ β := by
  intro hab
  subst β
  obtain ⟨b, χ, hweight⟩ := exists_finite_torus_weight_basis ρ hρ T hT
  let x := projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv.1)
  let z := projectivePointOfVector (b₀.equivFun w) (b₀.equivFun.map_ne_zero_iff.mpr hw.1)
  have hfinite : (fixedOrbit A T c x).Finite :=
    (Set.toFinite ({x,z} : Set (Point (projectiveSpace k E)))).subset (by
      intro y hy
      rcases htwo y hy with hp | hp
      · exact Set.mem_insert_iff.mpr (Or.inl hp)
      · exact Set.mem_insert_of_mem x (Set.mem_singleton_iff.mpr hp))
  have hneg : fixedOrbit A T (oppositeCocharacter T c) x ⊆ fixedOrbit A T c x := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro t
    simpa only [oppositeCocharacter_apply, inv_inv] using hy.2 t⁻¹
  obtain ⟨M,j,y,hj,hM,hy,hyU,_,_,_,hline⟩ :=
    exists_attractor_in_weight_basis ρ hρ hG T c A b₀ b χ he hweight v hv.1 hclosed hfinite
  obtain ⟨N,l,q,hl,hN,hq,hqU,_,_,_,_⟩ :=
    exists_attractor_in_weight_basis ρ hρ hG T (oppositeCocharacter T c) A b₀ b χ he hweight
      v hv.1 hclosed (hfinite.subset hneg)
  have hMeq : characterCocharacterPairing T c (Additive.ofMul α) = M := by
    rcases htwo y hy with hp | hp
    · rw [hp] at hyU
      exact weight_pairing_eq_of_mem_attractor_coordinate ρ T c b₀ b χ hweight j M hj v α hv hyU
    · rw [hp] at hyU
      exact weight_pairing_eq_of_mem_attractor_coordinate ρ T c b₀ b χ hweight j M hj w α hw hyU
  have hNeq : characterCocharacterPairing T (oppositeCocharacter T c) (Additive.ofMul α) = N := by
    rcases htwo q (hneg hq) with hp | hp
    · rw [hp] at hqU
      exact weight_pairing_eq_of_mem_attractor_coordinate ρ T (oppositeCocharacter T c)
        b₀ b χ hweight l N hl v α hv hqU
    · rw [hp] at hqU
      exact weight_pairing_eq_of_mem_attractor_coordinate ρ T (oppositeCocharacter T c)
        b₀ b χ hweight l N hl w α hw hqU
  have hMN : N = -M := by
    rw [characterCocharacterPairing_opposite, hMeq] at hNeq
    exact hNeq.symm
  have hcoord (g : Variety.Point G) i (hi : b.equivFun ((ρ.action g).1 v) i ≠ 0) :
      characterCocharacterPairing T c (Additive.ofMul (χ i)) = M := by
    have hp := hM g i hi
    have hn := hN g i hi
    rw [characterCocharacterPairing_opposite, hMN] at hn
    omega
  have htop (g : Variety.Point G) :
      topCoordinates (b.equivFun ((ρ.action g).1 v))
        (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M =
          b.equivFun ((ρ.action g).1 v) := by
    funext i
    by_cases hi : b.equivFun ((ρ.action g).1 v) i = 0
    · simp only [topCoordinates, hi, ite_self]
    · exact if_pos (hcoord g i hi)
  have hline' : Module.finrank k (Submodule.span k
      (Set.range fun g : Variety.Point G => b.equivFun ((ρ.action g).1 v))) = 1 := by
    have heq : (fun g : Variety.Point G =>
        topCoordinates (b.equivFun ((ρ.action g).1 v))
          (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M) =
        (fun g : Variety.Point G => b.equivFun ((ρ.action g).1 v)) := funext htop
    rw [heq] at hline
    exact hline
  obtain ⟨g,hg⟩ := hworb
  exact hne (hg.symm.trans (orbit_constant_of_coordinate_span_finrank_one ρ A b₀ b he v hv.1 hline' g))
end Theory.AlgebraicGroup.Bor1.SeparatingBorel
