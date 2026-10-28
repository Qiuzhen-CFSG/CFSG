module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.CurveInputs
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.RealizedCurve
public import Theory.AlgebraicGroup.Bor1.FlagCurve.SourceOrbit

/-!
# The intrinsic geometry of a semisimple group of rank one

For a connected semisimple algebraic group with a maximal torus of dimension
one, the unipotent radical of any containing Borel has dimension one. Two
distinct Borels containing the same maximal torus intersect in that torus.

The actual projective Borel orbit has dimension one and a nontrivial torus
action. Its proved monomial-curve normalization gives an isomorphism with P¹.
The original action is then realized by an algebraic morphism to PGL₂, and
the finite central kernel and explicit unipotent stabilizer calculations
give the two conclusions. All curve and action-realization premises are
discharged; no separability or rank-one classification assumption is used.

Source: Borel, Linear Algebraic Groups, IV, §§13.13–13.14. These are the
intrinsic inputs for the actual radical quotient in §13.15.
-/

public section

noncomputable section
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

theorem rank_one_geometry
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hTB : T≤B) (hV : IsUnipotentRadicalOf B V) :
    Variety.dimension V.carrierVariety=1 ∧
      ∀ C : ClosedSubgroup G,IsBorelSubgroup C → T≤C → C≠B → B.inter C=T := by
  obtain ⟨E,hEa,hEm,hEf,ρ,b,A,x,hρ,he,hstab,hdim,hmove⟩ :=
    exists_projective_rank_one_curve_inputs hG T hT hdimT B hB
  obtain ⟨e,he'⟩ := FlagCurve.projective_borel_orbit_iso_projectiveLine hG.1 T hT.1 hdimT
    B hB ρ hρ b A x he (fun g hg => (hstab g).mpr hg) hdim hmove
  exact rank_one_geometry_of_borel_curve_iso hG T B V hT hdimT hB hTB hV A x hstab e he'

theorem unipotentRadical_dimension_eq_one
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hTB : T≤B) (hV : IsUnipotentRadicalOf B V) :
    Variety.dimension V.carrierVariety=1 :=
  (rank_one_geometry hG T B V hT hdimT hB hTB hV).1

theorem common_torus_borel_intersection
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B C : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hTB : T≤B)
    (hC : IsBorelSubgroup C) (hTC : T≤C) (hne : C≠B) : B.inter C=T := by
  obtain ⟨V,hV,_⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  exact (rank_one_geometry hG T B V hT hdimT hB hTB hV).2 C hC hTC hne

theorem common_torus_borel_intersection_isSubtorus
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B C : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (hTB : T≤B) (hTC : T≤C) (hne : B≠C) : IsSubtorus (B.inter C) := by
  rw [common_torus_borel_intersection hG T B C hT hdimT hB hTB hC hTC hne.symm]
  exact hT.1
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
