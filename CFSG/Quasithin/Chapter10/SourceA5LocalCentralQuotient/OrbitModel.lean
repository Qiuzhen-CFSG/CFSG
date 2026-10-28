module
public import CFSG.Quasithin.Chapter10.SourceA5LocalCentralQuotient.OrbitComparison
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedTypes

/-!
# Descent of original orbit models to the marked local actor

An equivalence on the original central orbit span identifies the local
central quotient with the same model. The marked projection onto A₅ × A₅
is surjective, so equivariance on the original orbit subgroup descends to
the product embedded in the unchanged actor H/C_H(V). This shared adapter
serves both the natural and mixed moved-seed branches.

Source: Aschbacher–Smith, D.3.5, printed pp. 195–196, with the literal
central-quotient identification from 3.2.2(3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance orbitModelElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.moduleSubgroup := D.module_elementary

/-- An original central-orbit model descends to the same marked product in
 the unchanged local actor. -/
theorem source_local_quotient_model_equiv
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (μ : Representation (ZMod 2) (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) W) :
    let U := D.moduleSubgroup.subgroupOf (localJoin T L)
    let := (source_parabolic_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set (localJoin T L)))
    ∀ τ : Representation (ZMod 2) ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))
      (Additive (sourceLocalCentralQuotient D)),
      (∀ (m : localJoin T L) (v : D.moduleSubgroup),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D) v)) =
          Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D)
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.join_normalizes_module m.property) v).mp
                v.property⟩)) →
      ∀ i : (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) →*
          ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L))),
        (∀ x : localOrbit T L,
          i (originalA5ProductProjection D e hn ht htn x) =
            q (inclusion (show localOrbit T L ≤ localJoin T L from le_sup_left) x)) →
        (((centralTypeAction (ReducedNormal.representation (localJoin T L))
            ((localOrbit T L).subgroupOf (localJoin T L))
            ((T : Subgroup G).subgroupOf (localJoin T L)) D.homogeneous.normalizes).span
              (originalSeedCentralImage D)).toRepresentation.Equiv
          (μ.comp ((originalSeedProductQuotient D e hn ht htn).toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L))))))) →
        Nonempty (Representation.Equiv (τ.comp i) μ) := by
  dsimp only
  let := (source_parabolic_module_reduced D).normal
  intro τ hτ i hi b
  obtain ⟨a,_⟩ := source_local_quotient_orbit_image_equiv D τ hτ
  have hspan : (centralTypeAction (ReducedNormal.representation (localJoin T L))
      ((localOrbit T L).subgroupOf (localJoin T L))
      ((T : Subgroup G).subgroupOf (localJoin T L)) D.homogeneous.normalizes).span
        (originalSeedCentralImage D) = sourceLocalOrbitImage D := by
    apply Subrepresentation.toSubmodule_injective
    rw [centralTypeAction_span]
    exact (source_local_orbit_image_eq_centralOrbitSpan D).symm
  have b' : (sourceLocalOrbitImage D).toRepresentation.Equiv
      (μ.comp ((originalSeedProductQuotient D e hn ht htn).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L)))))) := by
    rwa [hspan] at b
  let c := a.symm.trans b'
  refine ⟨Representation.Equiv.mk c.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := originalA5ProductProjection_surjective D e hn ht htn g
  let y : (localOrbit T L).subgroupOf (localJoin T L) :=
    ⟨⟨x.val,(show localOrbit T L ≤ localJoin T L from le_sup_left) x.property⟩,x.property⟩
  have he := Representation.IntertwiningMap.isIntertwining _ _ c.toIntertwiningMap y v
  change c (τ (i (originalA5ProductProjection D e hn ht htn x)) v) =
    μ (originalA5ProductProjection D e hn ht htn x) (c v)
  rw [hi]
  exact he

end CFSG.Quasithin.Chapter10
