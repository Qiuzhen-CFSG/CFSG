module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.OrbitTransport
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.SourceConsequences
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Realization

/-!
# Realizing the Borel curve and deriving rank-one geometry

The actual orbit-to-P¹ isomorphism transports the original regular action
and its exact Borel stabilizer. The general P¹ action theorem then constructs
the algebraic-group morphism to PGL₂; no realization premise remains. The
finite-kernel and unipotent calculations prove both the radical dimension
and the common-torus intersection conclusion. Only the independently owned
curve isomorphism from Borel §13.13(4) remains an explicit input here.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
open Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {X : Variety.Geometric k}
local instance : MulAction (Variety.Point (pgl2Variety (k := k))) (Point (projectiveLine k)) :=
  pgl2ProjectiveLinePointMulAction

theorem exists_pgl2_borel_realization_of_curve_iso
    (hG : Variety.IsConnected G) (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (A : MorphicAction G X) (x : Point X)
    (hstab : ∀ g : Variety.Point G,A.toMulAction.smul g x=x ↔ g∈B.toSubgroup)
    (e : (A.orbitSubvariety x).toGeometric.toScheme ≅ (projectiveLine k).toScheme)
    (he : e.hom ≫ (projectiveLine k).structureMap=(A.orbitSubvariety x).toGeometric.structureMap) :
    ∃ (φ : AlgebraicGroup.Morphism G (pgl2Variety (k := k))) (p : Point (projectiveLine k)),
      ∀ g : Variety.Point G,φ.onPoints g • p=p ↔ g∈B.toSubgroup := by
  obtain ⟨D,p,hD⟩ := A.exists_projectiveLine_borel_action_of_curve_iso hG B hB x hstab e he
  obtain ⟨φ,hφ,_⟩ := ProjectiveLineAutomorphisms.existsUnique_algebraicGroupMorphism_of_morphicAction D
  refine ⟨φ,p,fun g => ?_⟩
  have h := hφ g p
  change φ.onPoints g • p=D.toMulAction.smul g p at h
  rw [h]
  exact hD g

theorem rank_one_geometry_of_borel_curve_iso
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (hB : IsBorelSubgroup B) (hTB : T≤B) (hV : IsUnipotentRadicalOf B V)
    (A : MorphicAction G X) (x : Point X)
    (hstab : ∀ g : Variety.Point G,A.toMulAction.smul g x=x ↔ g∈B.toSubgroup)
    (e : (A.orbitSubvariety x).toGeometric.toScheme ≅ (projectiveLine k).toScheme)
    (he : e.hom ≫ (projectiveLine k).structureMap=(A.orbitSubvariety x).toGeometric.structureMap) :
    Variety.dimension V.carrierVariety=1 ∧
      ∀ C : ClosedSubgroup G,IsBorelSubgroup C → T≤C → C≠B → B.inter C=T := by
  obtain ⟨φ,p,hφ⟩ := exists_pgl2_borel_realization_of_curve_iso hG.1 B hB A x hstab e he
  exact ⟨unipotentRadical_dimension_eq_one_of_pgl2_realization hG T B V hT hdimT hB hTB hV φ p hφ,
    fun C hC hTC hne => common_torus_borel_intersection_of_pgl2_realization
      hG T B V C hT hdimT hB hTB hV hC hTC hne φ p hφ⟩
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
