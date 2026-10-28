module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowInner
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveComponentEquivalence
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTripleSixComponent
import all CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedGeometry

/-!
# Excluding the covered-A₆ row on the literal moved chosen seed

The odd-center multiplier bound makes the component faithful on the actual
six-dimensional seed. The common cubic actor lies in that component and is
an offender on both the seed and every translate. Hexacode recognition gives
an intertwiner with the component unchanged. Transport through the original
subspace inclusions then contradicts homogeneous selection of a moved seed.

The source and structural applications are in
`SeedAlternativesMovedSylowTripleSixAssembly`. Full-normalizer exhaustion
remains with qt-baumann-fsu. Source: Aschbacher--Smith D.3.5(5), printed p.196,
used in 3.2.5 and 12.2.2. The internal import reuses the established
central-image transport without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem orbitSeed_faithful_tripleSix (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction D.seedRepresentation D.componentImage) :
    Nonempty (D.orbitComponent ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      Function.Injective (invariantSubspace D.orbitRepresentation D.orbitComponent D.orbitSeed
        D.orbitSeed_isIrrPlus.choose).toRepresentation := by
  let := D.orbitComponent_quasisimple h
  let := D.componentImage_quasisimple h.quasisimple
  let R := restrictedSubgroup D.orbitRepresentation D.orbitSeed D.orbitComponent
  let j : R ≃* D.componentImage :=
    (D.orbitSeedActionEquiv.groupEquiv.subgroupMap R).trans
      (MulEquiv.subgroupCongr D.orbitSeedActionEquiv_component)
  have hc : Nat.card (center D.componentImage) = 3 :=
    (Nat.card_congr a.centerEquiv.toEquiv).trans (Nat.card_zmod 3)
  exact restricted_tripleSix_faithful D.orbitRepresentation D.orbitComponent
    D.orbitSeed D.orbitSeed_isIrrPlus.choose (D.orbit_twoCore_eq_bot h)
    j a.quotientEquiv hc

private theorem orbitSeed_equiv_translate_tripleSix_of_budgets (D : ChosenModule T L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (e : D.orbitComponent ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hi : Function.Injective (invariantSubspace D.orbitRepresentation D.orbitComponent
      D.orbitSeed D.orbitSeed_isIrrPlus.choose).toRepresentation)
    (hd : Module.finrank (ZMod 2) D.orbitSeed = 6)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hAK : A ≤ D.orbitComponent) (t : D.orbitActor)
    (hbi : fixedCodim (subspaceImageRepresentation D.orbitRepresentation D.orbitSeed)
      (restrictedSubgroup D.orbitRepresentation D.orbitSeed A) ≤ rank A)
    (hbj : fixedCodim (subspaceImageRepresentation D.orbitRepresentation
        (D.orbitSeed.map (D.orbitRepresentation t)))
      (restrictedSubgroup D.orbitRepresentation
        (D.orbitSeed.map (D.orbitRepresentation t)) A) ≤ rank A) :
    Nonempty (Representation.Equiv
      (invariantSubspace D.orbitRepresentation D.orbitComponent D.orbitSeed
        D.orbitSeed_isIrrPlus.choose).toRepresentation
      (invariantSubspace D.orbitRepresentation D.orbitComponent
        (D.orbitSeed.map (D.orbitRepresentation t))
        (D.orbitSeed_isIrrPlus.map_normalizer D.orbitRepresentation
          (le_normalizer_of_normal (mem_top t))).choose).toRepresentation) := by
  exact invariant_equiv_of_common_budget_tripleSix D.orbitRepresentation D.orbitComponent
    D.orbitSeed t D.orbitSeed_isIrrPlus
    (D.orbitSeed_isIrrPlus.map_normalizer D.orbitRepresentation
      (le_normalizer_of_normal (mem_top t)))
    (D.orbit_fixedSpace_eq_bot hc) e hd hi A hA hAK hbi hbj

theorem orbitSeed_equiv_translate_of_tripleSix (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hq : quadraticRatio D.seedRepresentation = 1)
    (hgen : offenderSubgroup D.seedRepresentation = D.componentImage)
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction D.seedRepresentation D.componentImage)
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
  let e : K ≃* Atlas.Codes.HexEvenAutomorphisms :=
    Classical.choice (D.orbitSeed_faithful_tripleSix h a).1
  have hi := (D.orbitSeed_faithful_tripleSix h a).2
  have hI6 : Module.finrank (ZMod 2) I = 6 :=
    D.orbitSeedActionEquiv.linearEquiv.finrank_eq.trans a.dimension
  have hex : D.SeedSieveExceptions := ⟨hq,hgen,Or.inl ⟨a⟩⟩
  have hAK := D.cubic_le_component_of_exceptional h hc hm hex A hA hcu hb
  have himem : I ∈ subspaceOrbit ρ ⊤ I := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hiB := (D.cubic_best_on_seed_orbit_of_exceptional h hc hm hex A hA hcu hb I himem).2.le
  have hjB := (D.cubic_best_on_seed_orbit_of_exceptional h hc hm hex A hA hcu hb J
    ⟨⟨t,mem_top t⟩,rfl⟩).2.le
  exact D.orbitSeed_equiv_translate_tripleSix_of_budgets hc e hi hI6 A hA hAK t hiB hjB

/-- The six-dimensional covered-A₆ row cannot occur on a moved chosen seed. -/
theorem seed_not_tripleSix_of_moved (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : cubicRatio D.orbitRepresentation ≤ 2)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hseed : quadraticRatio D.seedRepresentation = 1)
    (hgen : offenderSubgroup D.seedRepresentation = D.componentImage)
    (a : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction D.seedRepresentation D.componentImage) : False := by
  obtain ⟨A,hA,hcu,hb⟩ := (cubicRatio_le_nat_iff D.orbitRepresentation 2).mp hq
  obtain ⟨t,ht,hnt,_⟩ := D.exists_moved_conjugate_geometry h hc hm
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let ρ := reducedRepresentation H
  let t' : (T : Subgroup G).subgroupOf H := ⟨⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩,ht⟩
  let b := invariantActionHom ρ D.orbitSpace (orbitSpan_invariant _ ⊤ D.space) t'.val
  let I := D.orbitSeed
  let J := I.map (D.orbitRepresentation b)
  have hJ := D.orbitSeed_isIrrPlus.map_normalizer D.orbitRepresentation
    (show b ∈ normalizer (D.orbitComponent : Set D.orbitActor) from
      le_normalizer_of_normal (mem_top b))
  have hi' : X ≤ subspaceStabilizer ρ (I.map D.orbitSpace.subtype) := by
    rw [D.orbitSeed_map]
    exact D.irrPlus.invariant
  have hj' : X ≤ subspaceStabilizer ρ (J.map D.orbitSpace.subtype) := by
    rw [D.orbitSeed_map_action]
    exact (D.irrPlus.isIrrPlus.map_normalizer ρ (D.irrPlus.normalizes t'.property)).choose
  obtain ⟨E⟩ := D.orbitSeed_equiv_translate_of_tripleSix h hc hm hseed hgen a A hA hcu hb b
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
