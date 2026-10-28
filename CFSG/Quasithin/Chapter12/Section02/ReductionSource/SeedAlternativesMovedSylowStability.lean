module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowSieveAssembly
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveStability
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTransport

/-!
# Exceptional-row stabilization on the literal chosen seed

The triple-six and exterior-five rows have small best offenders. A moved
constituent would therefore exceed the common cubic actor's codimension
budget, so that actor stabilizes every homogeneous constituent. Ratio one
then makes it best on every constituent. Three independent constituents
would again exceed the budget, giving exactly two literal Sylow conjugates.

All faithful-image and subgroup transports retain the original maps. The
source application is `SeedAlternativesMovedSylowStabilityAssembly`. This
proves the stabilization and two-summand steps, not the remaining exceptional
model exclusion or full-normalizer exhaustion, both owned by qt-baumann-fsu.
Source: Aschbacher--Smith D.3.5(3--5), combined manuscript of 1 March 2004,
printed pp.195--196, used in 3.2.5 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both exceptional source rows have small best offenders on the literal seed. -/
theorem seed_best_rank_small_of_exceptional (D : ChosenModule T L V)
    (hex : D.SeedSieveExceptions) :
    ∀ B, IsBestOffender D.seedRepresentation B →
      rank B + 2 < Module.finrank (ZMod 2) D.space := by
  rcases hex.2.2 with ha | ⟨_,e,hd,hoff⟩
  · obtain ⟨a⟩ := ha
    exact tripleSix_best_rank_small D.seedRepresentation D.componentImage a hex.1
  · exact exteriorFive_best_rank_small D.seedRepresentation D.componentImage hex.2.1 e hd hoff

/-- The nested action image is the original faithful chosen-seed action. -/
def orbitSeedActionEquiv (D : ChosenModule T L V) :
    ActionEquiv (subspaceImageRepresentation D.orbitRepresentation D.orbitSeed)
      D.seedRepresentation :=
  nestedImageActionEquiv (reducedRepresentation (L ⊔ (T : Subgroup G)))
    D.orbitSpace D.space (orbitSpan_invariant _ ⊤ D.space) D.seed_le_orbitSpace

/-- The same cubic actor stabilizes every actual conjugate in either exceptional
row. No independent actor is substituted on another summand. -/
theorem cubic_stabilizes_seed_translates_of_exceptional (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hex : D.SeedSieveExceptions)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hcu : IsCubic D.orbitRepresentation A)
    (hb : fixedCodim D.orbitRepresentation A ≤ 2 * rank A)
    (t : D.orbitActor) :
    A ≤ subspaceStabilizer D.orbitRepresentation
      (D.orbitSeed.map (D.orbitRepresentation t)) := by
  let : IsElementaryAbelian 2 A := hA.2
  let ρ := D.orbitRepresentation
  let I := D.orbitSeed.map (ρ t)
  have hi : sSupIndep (subspaceOrbit ρ A I) := by
    apply (D.orbitSeed_independent hc ⊤).mono
    rintro _ ⟨b,rfl⟩
    exact ⟨⟨b*t,mem_top _⟩,subspace_map_mul ρ D.orbitSeed b t⟩
  have hd : 2 < Module.finrank (ZMod 2) I := by
    rw [finrank_map_action]
    exact D.orbitSeed_finrank_gt_two h
  let e := (conjugateImageActionEquiv ρ D.orbitSeed t).trans D.orbitSeedActionEquiv
  exact cubic_stabilizes_of_small_best_offenders_equiv ρ I A hA hcu hi hd hb
    (D.orbitSeed_translate_kernel_eq_bot h A (IsElementaryAbelian.isPGroup 2 A) t)
    D.seedRepresentation e hex.1 (D.seed_best_rank_small_of_exceptional hex)

/-- The original represented seed is in particular stabilized. -/
theorem cubic_stabilizes_seed_of_exceptional (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hex : D.SeedSieveExceptions)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hcu : IsCubic D.orbitRepresentation A)
    (hb : fixedCodim D.orbitRepresentation A ≤ 2 * rank A) :
    A ≤ subspaceStabilizer D.orbitRepresentation D.orbitSeed := by
  simpa only [map_one,Module.End.one_eq_id,Submodule.map_id] using
    D.cubic_stabilizes_seed_translates_of_exceptional h hc hex A hA hcu hb 1

/-- In an exceptional row, the common cubic actor is best on every member
of the actual moved orbit, with the same rank on each constituent. -/
theorem cubic_best_on_seed_orbit_of_exceptional (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hcu : IsCubic D.orbitRepresentation A)
    (hb : fixedCodim D.orbitRepresentation A ≤ 2 * rank A)
    (J : Submodule (ZMod 2) D.orbitSpace)
    (hJ : J ∈ subspaceOrbit D.orbitRepresentation ⊤ D.orbitSeed) :
    IsBestOffender (subspaceImageRepresentation D.orbitRepresentation J)
      (restrictedSubgroup D.orbitRepresentation J A) ∧
    fixedCodim (subspaceImageRepresentation D.orbitRepresentation J)
      (restrictedSubgroup D.orbitRepresentation J A) = rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  apply common_actor_best_on_orbit D.orbitRepresentation D.orbitSeed hA
    (D.orbitSeed_independent hc ⊤) _ _ _ hb
    (D.orbitSeed_exists_moved_of_moved hm) J hJ
  · rintro _ ⟨t,rfl⟩
    exact D.cubic_stabilizes_seed_translates_of_exceptional h hc hex A hA hcu hb t
  · rintro _ ⟨t,rfl⟩
    exact D.orbitSeed_translate_kernel_eq_bot h A (IsElementaryAbelian.isPGroup 2 A) t
  · rintro _ ⟨t,rfl⟩
    exact ((conjugateImageActionEquiv D.orbitRepresentation D.orbitSeed t).trans
      D.orbitSeedActionEquiv).quadraticRatio_eq.trans hex.1

/-- On the original seed, the same image subgroup is best and lies in the
literal chosen component image. -/
theorem cubic_seed_best_le_component_of_exceptional (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions)
    (A : Subgroup D.orbitActor) (hA : IsElementaryTwo A)
    (hcu : IsCubic D.orbitRepresentation A)
    (hb : fixedCodim D.orbitRepresentation A ≤ 2 * rank A) :
    let B := (restrictedSubgroup D.orbitRepresentation D.orbitSeed A).map
      D.orbitSeedActionEquiv.groupEquiv.toMonoidHom
    IsBestOffender D.seedRepresentation B ∧ B ≤ D.componentImage ∧
      rank B = rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hmem : D.orbitSeed ∈ subspaceOrbit D.orbitRepresentation ⊤ D.orbitSeed := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hp := D.cubic_best_on_seed_orbit_of_exceptional h hc hm hex A hA hcu hb D.orbitSeed hmem
  have hk := D.orbitSeed_translate_kernel_eq_bot h A (IsElementaryAbelian.isPGroup 2 A) 1
  simp only [map_one,Module.End.one_eq_id,Submodule.map_id] at hk
  exact restricted_best_on_marked_image D.orbitRepresentation D.orbitSeed hA
    (D.cubic_stabilizes_seed_of_exceptional h hc hex A hA hcu hb) hk hp.1
    D.seedRepresentation D.orbitSeedActionEquiv D.componentImage hex.2.1


omit [Finite G] in
/-- A two-member faithful-image orbit gives two literal Sylow conjugates of
V. Both subgroup images use the original reduced-module inclusion. -/
theorem sylowTwoModuleTypes_of_orbit_two_conjugates (D : ChosenModule T L V)
    (hm : V < componentOrbit V (T : Subgroup G))
    (htwo : ∀ t : D.orbitActor, D.orbitSeed.map (D.orbitRepresentation t) ≠ D.orbitSeed →
      ∀ s : D.orbitActor, D.orbitSeed.map (D.orbitRepresentation s) = D.orbitSeed ∨
        D.orbitSeed.map (D.orbitRepresentation s) = D.orbitSeed.map (D.orbitRepresentation t)) :
    D.SylowTwoModuleTypes := by
  let H := L ⊔ (T : Subgroup G)
  have himage : ReducedNormal.subspaceImage H D.space = V := D.image_eq
  let ρ := reducedRepresentation H
  let f := invariantActionHom ρ D.orbitSpace (orbitSpan_invariant _ ⊤ D.space)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (V : Set G) := by
    intro hn
    exact hm.not_ge (iSup_conjugates_le_of_le_normalizer V T V le_rfl hn)
  obtain ⟨t,ht,hnt⟩ := Set.not_subset.mp hn
  let t' : H := ⟨t,(le_sup_right : (T : Subgroup G) ≤ H) ht⟩
  have htm : D.orbitSeed.map (D.orbitRepresentation (f t')) ≠ D.orbitSeed := by
    intro he
    have he' := congrArg (fun J : Submodule (ZMod 2) D.orbitSpace =>
      J.map D.orbitSpace.subtype) he
    rw [D.orbitSeed_map_action,D.orbitSeed_map] at he'
    have heG := congrArg (ReducedNormal.subspaceImage H) he'
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H t')) =
      ReducedNormal.subspaceImage H D.space at heG
    rw [ReducedNormal.subspaceImage_map,himage] at heG
    exact hnt (mem_normalizer_iff_map_conj_eq.mpr heG)
  have hrefl (U : Subgroup G) : SameConjugationModule L U U :=
    ⟨MulEquiv.refl U,fun _ _ _ he => he⟩
  refine ⟨t,ht,hnt,fun s hs => ?_⟩
  let s' : H := ⟨s,(le_sup_right : (T : Subgroup G) ≤ H) hs⟩
  rcases htwo (f t') htm (f s') with he | he
  · have he' := congrArg (fun J : Submodule (ZMod 2) D.orbitSpace =>
      J.map D.orbitSpace.subtype) he
    rw [D.orbitSeed_map_action,D.orbitSeed_map] at he'
    have heG := congrArg (ReducedNormal.subspaceImage H) he'
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H s')) =
      ReducedNormal.subspaceImage H D.space at heG
    rw [ReducedNormal.subspaceImage_map,himage] at heG
    change V.map (MulAut.conj s).toMonoidHom = V at heG
    rw [heG]
    exact Or.inl (hrefl V)
  · have he' := congrArg (fun J : Submodule (ZMod 2) D.orbitSpace =>
      J.map D.orbitSpace.subtype) he
    rw [D.orbitSeed_map_action,D.orbitSeed_map_action] at he'
    have heG := congrArg (ReducedNormal.subspaceImage H) he'
    change ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H s')) =
      ReducedNormal.subspaceImage H (D.space.map (ReducedNormal.representation H t')) at heG
    rw [ReducedNormal.subspaceImage_map,ReducedNormal.subspaceImage_map,himage] at heG
    change V.map (MulAut.conj s).toMonoidHom = V.map (MulAut.conj t).toMonoidHom at heG
    rw [heG]
    exact Or.inr (hrefl _)

/-- Even before their exclusion, both exceptional rows have exactly two
literal Sylow conjugates. The common actor budget proves this without any
assumption about automorphism types or constituent multiplicities. -/
theorem sylowTwoModuleTypes_of_exceptional (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : cubicRatio D.orbitRepresentation ≤ 2)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions) : D.SylowTwoModuleTypes := by
  obtain ⟨A,hA,hcu,hb⟩ := (cubicRatio_le_nat_iff D.orbitRepresentation 2).mp hq
  apply D.sylowTwoModuleTypes_of_orbit_two_conjugates hm
  intro t ht
  apply two_conjugates_of_common_budget D.orbitRepresentation D.orbitSeed hA
    (D.orbitSeed_independent hc ⊤) _ hb _ ht
  · rintro _ ⟨s,rfl⟩
    exact D.cubic_stabilizes_seed_translates_of_exceptional h hc hex A hA hcu hb s
  · intro J hJ
    exact (D.cubic_best_on_seed_orbit_of_exceptional h hc hm hex A hA hcu hb J hJ).2.ge

/-- The two-summand source geometry in either exceptional row, with the
original moving element and unchanged L-action retained. -/
theorem exceptional_sylow_pair (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : cubicRatio D.orbitRepresentation ≤ 2)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hex : D.SeedSieveExceptions) :
    ∃ t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
      componentOrbit V (T : Subgroup G) = V ⊔ V.map (MulAut.conj t).toMonoidHom ∧
      V ⊓ V.map (MulAut.conj t).toMonoidHom = ⊥ ∧
      ¬ SameConjugationModule L V (V.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨t,ht,hnt,htypes⟩ := D.sylowTwoModuleTypes_of_exceptional h hq hc hm hex
  exact ⟨t,ht,hnt,D.sylowOrbit_eq_sup_of_two_module_types t ht htypes,
    D.moved_conjugate_inf_eq_bot h hc ht hnt,D.moved_conjugate_not_sameModule ht hnt⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
