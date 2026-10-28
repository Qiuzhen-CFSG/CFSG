module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowInner
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveComponentAction
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveComponentEquivalence
import all CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedGeometry

/-!
# Excluding the exterior-five row on the literal moved chosen seed

The common cubic actor lies in the actual component and is an offender on
every constituent. A center-free SL₅ seed image identifies that component
with SL₅ itself. Ten-dimensional irreducible recognition and the incompatible
exterior-square/cube offender calculation therefore identify the chosen seed
with its moved constituent for the unchanged component action. Transport
through the original subspace inclusions contradicts homogeneous selection.

The final source and structural applications are in
`SeedAlternativesMovedSylowExteriorAssembly`. Covered-A₆ exclusion and
full-normalizer exhaustion remain separate local obligations of qt-baumann-fsu.
Source: Aschbacher--Smith D.3.5(5), printed p.196, used in 3.2.5 and12.2.2.
The internal import reuses the established central-image transport without
changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem orbitComponent_equiv_SL5 (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (e : D.componentImage ≃* SL5TenDimensional.Group) :
    Nonempty (D.orbitComponent ≃* SL5TenDimensional.Group) := by
  let := D.orbitComponent_quasisimple h
  let R := restrictedSubgroup D.orbitRepresentation D.orbitSeed D.orbitComponent
  let j : R ≃* D.componentImage :=
    (D.orbitSeedActionEquiv.groupEquiv.subgroupMap R).trans
      (MulEquiv.subgroupCongr D.orbitSeedActionEquiv_component)
  have hz : center R = ⊥ := center_eq_bot_of_model_equiv (j.trans e)
    SL5TenDimensional.center_eq_bot
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot _).mpr
    (restrictedSubgroup_ne_bot D.orbitRepresentation D.orbitSeed
      D.orbitSeed_isIrrPlus.choose
      (D.orbitSeed_isIrrPlus.not_le_fixedSpace D.orbitRepresentation))
  have hi := restrictedActionSurjection_injective_of_center_free D.orbitRepresentation
    D.orbitComponent D.orbitSeed D.orbitSeed_isIrrPlus.choose
    (subspaceImageRepresentation_injective _ _)
    (orbitSpan_faithfulOrbit_eq_top _ D.space) hz
  exact ⟨(MulEquiv.ofBijective (restrictedActionSurjection D.orbitRepresentation
    D.orbitSeed D.orbitComponent D.orbitSeed_isIrrPlus.choose)
    ⟨hi,restrictedActionSurjection_surjective _ _ _ _⟩).trans (j.trans e)⟩

theorem orbitSeed_equiv_translate_of_exterior (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions)
    (e : D.componentImage ≃* SL5TenDimensional.Group)
    (hd : Module.finrank (ZMod 2) D.space = 10)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hcu : IsCubic D.orbitRepresentation A)
    (hb : fixedCodim D.orbitRepresentation A ≤ 2 * rank A)
    (t : D.orbitActor) :
    Nonempty (Representation.Equiv
      (invariantSubspace D.orbitRepresentation D.orbitComponent D.orbitSeed
        D.orbitSeed_isIrrPlus.choose).toRepresentation
      (invariantSubspace D.orbitRepresentation D.orbitComponent
        (D.orbitSeed.map (D.orbitRepresentation t))
        (D.orbitSeed_isIrrPlus.map_normalizer D.orbitRepresentation
          (le_normalizer_of_normal (mem_top t))).choose).toRepresentation) := by
  let ρ := D.orbitRepresentation
  let K := D.orbitComponent
  let I := D.orbitSeed
  let J := I.map (ρ t)
  have hJ := D.orbitSeed_isIrrPlus.map_normalizer ρ
    (show t ∈ normalizer (K : Set D.orbitActor) from le_normalizer_of_normal (mem_top t))
  let j : K ≃* SL5TenDimensional.Group := Classical.choice (D.orbitComponent_equiv_SL5 h e)
  have hI10 : Module.finrank (ZMod 2) I = 10 :=
    D.orbitSeedActionEquiv.linearEquiv.finrank_eq.trans hd
  have hJ10 : Module.finrank (ZMod 2) J = 10 := (finrank_map_action ρ I t).trans hI10
  have hAK := D.cubic_le_component_of_exceptional h hc hm hex A hA hcu hb
  have hi : I ∈ subspaceOrbit ρ ⊤ I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hiB := (D.cubic_best_on_seed_orbit_of_exceptional h hc hm hex A hA hcu hb I hi).2.le
  have hjB := (D.cubic_best_on_seed_orbit_of_exceptional h hc hm hex A hA hcu hb J
    ⟨⟨t,mem_top t⟩,rfl⟩).2.le
  exact invariant_equiv_of_common_budget_SL5 ρ K I J D.orbitSeed_isIrrPlus hJ
    (D.orbit_fixedSpace_eq_bot hc) j hI10 hJ10 A hA hAK hiB hjB

/-- The ten-dimensional SL₅ row cannot occur on a moved chosen seed. -/
theorem seed_not_exterior_of_moved (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : cubicRatio D.orbitRepresentation ≤ 2)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions)
    (e : D.componentImage ≃* SL5TenDimensional.Group)
    (hd : Module.finrank (ZMod 2) D.space = 10) : False := by
  obtain ⟨A,hA,hcu,hb⟩ := (cubicRatio_le_nat_iff D.orbitRepresentation 2).mp hq
  obtain ⟨t,ht,hnt,_⟩ := D.exists_moved_conjugate_geometry h hc hm
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let ρ := reducedRepresentation H
  let t' : (T : Subgroup G).subgroupOf H := ⟨⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩,ht⟩
  let a := invariantActionHom ρ D.orbitSpace (orbitSpan_invariant _ ⊤ D.space) t'.val
  let I := D.orbitSeed
  let J := I.map (D.orbitRepresentation a)
  have hJ := D.orbitSeed_isIrrPlus.map_normalizer D.orbitRepresentation
    (show a ∈ normalizer (D.orbitComponent : Set D.orbitActor) from
      le_normalizer_of_normal (mem_top a))
  have hi' : X ≤ subspaceStabilizer ρ (I.map D.orbitSpace.subtype) := by
    rw [D.orbitSeed_map]
    exact D.irrPlus.invariant
  have hj' : X ≤ subspaceStabilizer ρ (J.map D.orbitSpace.subtype) := by
    rw [D.orbitSeed_map_action]
    exact (D.irrPlus.isIrrPlus.map_normalizer ρ (D.irrPlus.normalizes t'.property)).choose
  obtain ⟨E⟩ := D.orbitSeed_equiv_translate_of_exterior h hc hm hex e hd A hA hcu hb a
  obtain ⟨F⟩ := nested_invariant_equiv ρ D.orbitSpace X D.orbitSpace_component_invariant
    I J D.orbitSeed_isIrrPlus.choose hJ.choose hi' hj' E
  have hs := same_central_images ρ X (I.map D.orbitSpace.subtype) (J.map D.orbitSpace.subtype)
    hi' hj' F.toLinearEquiv
    (fun x v => IntertwiningMap.isIntertwining _ _ F.toIntertwiningMap x v)
  have he : SameModule (quotientImage ρ X D.space D.irrPlus.invariant)
      (quotientImage ρ X (D.space.map (ρ t'.val))
        (D.irrPlus.isIrrPlus.map_normalizer ρ (D.irrPlus.normalizes t'.property)).choose) := by
    have himap : I.map D.orbitSpace.subtype = D.space := D.orbitSeed_map
    have hjmap : J.map D.orbitSpace.subtype = D.space.map (ρ t'.val) := D.orbitSeed_map_action t'.val
    simpa only [himap,hjmap] using hs
  have heq := D.irrPlus.eq_of_isomorphic_conjugate ρ t' he
  have hg := congrArg (ReducedNormal.subspaceImage H) heq
  change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H t'.val)) =
    ReducedNormal.subspaceImage H D.space at hg
  have himage : ReducedNormal.subspaceImage H D.space = V := D.image_eq
  rw [ReducedNormal.subspaceImage_map,himage] at hg
  exact hnt (mem_normalizer_iff_map_conj_eq.mpr hg)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
