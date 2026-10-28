module
public import CFSG.Quasithin.Chapter10.SourceA5MovedSeedTypes
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbitModels
public import Theory.Representation.AlternatingFiveMovedPair.NaturalTypes
/-!
# The natural pair on the original moved-seed orbit

The two natural tensor types form one automorphism orbit. Homogeneous
uniqueness and movement of the original seed force exactly one copy of each
in its central orbit span. The resulting model uses the original A₅-product
quotient followed by one fixed concrete SL₂(4) marking on both factors.

Source: Aschbacher–Smith D.3.5, printed pp. 195–196.
-/
@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))

/-- The original central seed orbit with its literal L₀ action. -/
noncomputable abbrev originalSeedCentralOrbit :=
  (centralTypeAction (ReducedNormal.representation (localJoin T L))
    ((localOrbit T L).subgroupOf (localJoin T L))
    ((T : Subgroup G).subgroupOf (localJoin T L)) D.homogeneous.normalizes).span
      (originalSeedCentralImage D)

theorem source_a5_seed_orbit_ne (hproper : D.seed ≠ D.moduleSubgroup) :
    orbitSpan (ReducedNormal.representation (localJoin T L))
      ((T : Subgroup G).subgroupOf (localJoin T L)) D.seedSpace ≠ D.seedSpace := by
  intro he
  apply hproper
  rw [D.module_eq_subspaceImage,he]
  rfl

/-- A model marking of the original quotient seed inflates along the same
original characteristic quotient, rather than a newly selected marking. -/
noncomputable def source_a5_seed_model_inflation
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (μ : Representation (ZMod 2) (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) W)
    (b : (originalA5SeedAction D e hn ht htn).Equiv μ) :
    (originalSeedCentralImage D).toRepresentation.Equiv
      (μ.comp ((originalSeedProductQuotient D e hn ht htn).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L)))))) := by
  refine Representation.Equiv.mk b.toLinearEquiv ?_
  intro x
  apply LinearMap.ext
  intro v
  have he := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap
    ((originalSeedProductQuotient D e hn ht htn) (QuotientGroup.mk' _ x)) v
  rw [originalSeedProductQuotient_apply,originalA5SeedAction_apply] at he
  exact he

/-- A moved natural seed has exactly the two complementary natural tensor
constituents on its actual central orbit span. -/
theorem source_a5_moved_natural_central_orbit
    (hproper : D.seed ≠ D.moduleSubgroup)
    (base : alternatingGroup (Fin 5) ≃* SL2FourNatural.SL)
    (b : Bool)
    (eb : (originalA5SeedAction D e hn ht htn).Equiv
      ((AlternatingFiveMovedPair.NaturalTypes.model b).comp
        (base.prodCongr base).toMonoidHom)) :
    Nonempty ((originalSeedCentralOrbit D).toRepresentation.Equiv
      (AlternatingFiveMovedPair.Natural.action.comp
        (((originalSeedProductQuotient D e hn ht htn).trans
          (base.prodCongr base)).toMonoidHom.comp
            (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L))))))) := by
  let q := (originalSeedProductQuotient D e hn ht htn).trans (base.prodCongr base)
  let f := q.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 ((localOrbit T L).subgroupOf (localJoin T L))))
  let μ := AlternatingFiveMovedPair.NaturalTypes.model
  let b' : (originalSeedCentralImage D).toRepresentation.Equiv ((μ b).comp f) :=
    source_a5_seed_model_inflation D e hn ht htn _ eb
  have htypes (a : MulAut (SL2FourNatural.SL × SL2FourNatural.SL)) :
      Nonempty (Representation.Equiv ((μ b).comp a.toMonoidHom) (μ b)) ∨
      Nonempty (Representation.Equiv ((μ b).comp a.toMonoidHom) (μ (!b))) := by
    obtain ⟨c,hc⟩ := AlternatingFiveMovedPair.NaturalTypes.model_automorphism_types a b
    cases b <;> cases c
    · exact Or.inl hc
    · exact Or.inr hc
    · exact Or.inr hc
    · exact Or.inl hc
  obtain ⟨a⟩ := D.homogeneous.central_span_equiv_pair
    (ReducedNormal.representation (localJoin T L)) (pCore 2 _) q (μ b) (μ (!b))
    b' (source_a5_seed_orbit_ne D hproper) htypes
  cases b
  · exact ⟨a⟩
  · let flip : Representation.Equiv (((μ true).prod (μ false)).comp f)
        (AlternatingFiveMovedPair.Natural.action.comp f) :=
      Representation.Equiv.mk (LinearEquiv.prodComm (ZMod 2) _ _) (by
        intro x
        apply LinearMap.ext
        intro v
        rfl)
    exact ⟨a.trans flip⟩
end CFSG.Quasithin.Chapter10
