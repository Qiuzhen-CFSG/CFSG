module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.ChapterD.Section02.QuadraticOrbit
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderFaithful

/-!
# The chosen seed in its faithful local orbit

The actual chosen constituent embeds into its orbit representation. Homogeneous
independence and the nontrivial quasisimple component action survive this
embedding and passage to the faithful image. The generalized Fitting subgroup
and trivial 2-core make each elementary 2-actor faithful on every constituent.

These are the literal action inputs to the FF argument in [AS, D.3.5(2)], used
in the moved branch of [AS, 3.2.5]; see `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original seed inside its actual local orbit representation. -/
@[expose] def orbitSeed : Submodule (ZMod 2) D.orbitSpace :=
  D.space.comap D.orbitSpace.subtype

omit [Finite G] in
theorem orbitSeed_map : D.orbitSeed.map D.orbitSpace.subtype = D.space := by
  rw [orbitSeed, Submodule.map_comap_subtype,
    inf_eq_right.mpr D.seed_le_orbitSpace]

omit [Finite G] in
theorem orbitSeed_map_action (g : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    (D.orbitSeed.map (D.orbitRepresentation ((invariantActionHom (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
      (orbitSpan_invariant _ ⊤ D.space) g)))).map D.orbitSpace.subtype =
      D.space.map (reducedRepresentation (L ⊔ (T : Subgroup G)) g) := by
  rw [← Submodule.map_comp]
  have he : D.orbitSpace.subtype.comp (D.orbitRepresentation ((invariantActionHom (reducedRepresentation (L ⊔ (T : Subgroup G))) D.orbitSpace
      (orbitSpan_invariant _ ⊤ D.space) g))) =
      (reducedRepresentation (L ⊔ (T : Subgroup G)) g).comp D.orbitSpace.subtype := by
    apply LinearMap.ext
    intro v
    exact invariantActionHom_apply (reducedRepresentation (L ⊔ (T : Subgroup G)))
      D.orbitSpace (orbitSpan_invariant _ ⊤ D.space) g v
  rw [he, Submodule.map_comp, D.orbitSeed_map]

omit [Finite G] in
theorem seed_subspaceOrbit_eq_sylow :
    subspaceOrbit (reducedRepresentation (L ⊔ (T : Subgroup G))) ⊤ D.space =
      subspaceOrbit (reducedRepresentation (L ⊔ (T : Subgroup G)))
        ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) D.space := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let R := (T : Subgroup G).subgroupOf H
  let ρ := reducedRepresentation H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : R ⊔ X = ⊤ := by
    rw [sup_comm, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  apply Set.Subset.antisymm
  · rintro _ ⟨g,rfl⟩
    have hg : g.val ∈ R ⊔ X := hgen.symm ▸ mem_top _
    obtain ⟨t,ht,x,hx,he⟩ := mem_sup_of_normal_right.mp hg
    refine ⟨⟨t,ht⟩,?_⟩
    change D.space.map (ρ t) = D.space.map (ρ g.val)
    rw [← he, subspace_map_mul,
      (subspace_map_eq_iff ρ D.space x).mpr (D.irrPlus.invariant hx)]
  · rintro _ ⟨g,rfl⟩
    exact ⟨⟨g,mem_top _⟩,rfl⟩

omit [Finite G] in
/-- Homogeneous independence survives both restriction to the orbit space
and passage to its faithful image, for every subgroup of the actual actor. -/
theorem orbitSeed_independent (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (A : Subgroup D.orbitActor) :
    sSupIndep (subspaceOrbit D.orbitRepresentation A D.orbitSeed) := by
  classical
  let H := L ⊔ (T : Subgroup G)
  let ρ := reducedRepresentation H
  let Ω := subspaceOrbit D.orbitRepresentation A D.orbitSeed
  have hind : sSupIndep (subspaceOrbit ρ ⊤ D.space) := by
    rw [D.seed_subspaceOrbit_eq_sylow]
    exact D.irrPlus.independent_orbit_of_inf_fixedSpace_eq_bot ρ
      (D.seed_inf_fixedSpace_eq_bot hc)
  have hmem (J : Ω) : J.val.map D.orbitSpace.subtype ∈ subspaceOrbit ρ ⊤ D.space := by
    obtain ⟨a,ha⟩ := J.property
    obtain ⟨g,hg⟩ := invariantActionHom_surjective (reducedRepresentation H) D.orbitSpace
      (orbitSpan_invariant _ ⊤ D.space) a.val
    refine ⟨⟨g,mem_top _⟩,?_⟩
    rw [← ha]
    change D.space.map (ρ g) = (D.orbitSeed.map (D.orbitRepresentation a.val)).map D.orbitSpace.subtype
    rw [← hg, D.orbitSeed_map_action]
  let f : Ω → subspaceOrbit ρ ⊤ D.space :=
    fun J => ⟨J.val.map D.orbitSpace.subtype,hmem J⟩
  have hf : Function.Injective f := by
    intro J K he
    exact Subtype.ext (Submodule.map_injective_of_injective D.orbitSpace.subtype_injective
      (congrArg Subtype.val he))
  have hi := ((sSupIndep_iff _).mp hind).comp hf
  change iSupIndep (fun J : Ω => J.val.map D.orbitSpace.subtype) at hi
  apply (sSupIndep_iff _).mpr
  intro J
  apply Submodule.disjoint_def.mpr
  intro v hv hs
  have hz : (v : Additive (ReducedModule H)) = 0 := by
    apply Submodule.disjoint_def.mp (hi J) v.val ⟨v,hv,rfl⟩
    have hm : v.val ∈ (⨆ K : Ω, ⨆ (_ : K ≠ J), K.val).map D.orbitSpace.subtype :=
      ⟨v,hs,rfl⟩
    simpa only [Submodule.map_iSup] using hm
  exact Subtype.ext hz

open Chapter3.Section02.ChosenSource325

omit [Finite G] in
/-- The constituent retains its actual noncentral component action after
restriction to the orbit and passage to its faithful image. -/
theorem orbitSeed_isIrrPlus :
    IsIrrPlus D.orbitRepresentation D.orbitComponent D.orbitSeed :=
  isIrrPlus_faithfulOrbit _ D.irrPlus.isIrrPlus

omit [Finite G] in
theorem orbitSeed_disjoint_translate (hc : V ⊓ centralizer (L : Set G) = ⊥)
    {a : D.orbitActor} (ha : D.orbitSeed.map (D.orbitRepresentation a) ≠ D.orbitSeed) :
    Disjoint D.orbitSeed (D.orbitSeed.map (D.orbitRepresentation a)) := by
  have hi : D.orbitSeed ∈ subspaceOrbit D.orbitRepresentation ⊤ D.orbitSeed := by
    refine ⟨1,?_⟩
    simp only [Subgroup.coe_one,map_one,Module.End.one_eq_id,Submodule.map_id]
  exact (D.orbitSeed_independent hc ⊤).pairwiseDisjoint hi ⟨⟨a,mem_top _⟩,rfl⟩ ha.symm

omit [Finite G] in
/-- Equality of the represented seed and its orbit would identify the actual
ambient subgroups, so a moved chosen seed has a proper represented orbit. -/
theorem orbitSeed_ne_top_of_moved
    (hm : V < componentOrbit V (T : Subgroup G)) : D.orbitSeed ≠ ⊤ := by
  intro ht
  have he := D.orbitSeed_map
  rw [ht,Submodule.map_top,Submodule.range_subtype] at he
  have hg := congrArg (subspaceImage (L ⊔ (T : Subgroup G))) he
  rw [D.orbitSpace_image,D.image_eq] at hg
  exact hm.ne hg.symm

omit [Finite G] in
/-- The faithful orbit actor really moves some translate of the chosen seed. -/
theorem orbitSeed_exists_moved_of_moved
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ∃ a : D.orbitActor, D.orbitSeed.map (D.orbitRepresentation a) ≠ D.orbitSeed := by
  by_contra! hn
  have hspan : orbitSpan D.orbitRepresentation ⊤ D.orbitSeed = D.orbitSeed := by
    simp only [orbitSpan,hn,iSup_const]
  have ht : orbitSpan D.orbitRepresentation ⊤ D.orbitSeed = ⊤ :=
    orbitSpan_faithfulOrbit_eq_top (reducedRepresentation (L ⊔ (T : Subgroup G))) D.space
  rw [ht] at hspan
  exact D.orbitSeed_ne_top_of_moved hm hspan.symm

/-- The constituent dimension is greater than two because the actual
component image is quasisimple and acts nontrivially. -/
theorem orbitSeed_finrank_gt_two (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    2 < Module.finrank (ZMod 2) D.orbitSeed := by
  let := D.orbitComponent_quasisimple h
  exact D.orbitSeed_isIrrPlus.finrank_gt_two D.orbitRepresentation D.orbitComponent

/-- The elementary actor is faithful on every translated chosen constituent.
The proof uses F* and O₂ of the literal local orbit actor. -/
theorem orbitSeed_translate_kernel_eq_bot
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (A : Subgroup D.orbitActor) (hA : IsPGroup 2 A) (a : D.orbitActor) :
    subspaceKernel D.orbitRepresentation
      (D.orbitSeed.map (D.orbitRepresentation a)) A = ⊥ := by
  let := D.orbitComponent_quasisimple h
  have hi := D.orbitSeed_isIrrPlus.map_normalizer D.orbitRepresentation
    (show a ∈ normalizer (D.orbitComponent : Set D.orbitActor) from le_normalizer_of_normal (mem_top _))
  exact subspaceKernel_eq_bot_of_quasisimple_fitting D.orbitRepresentation D.orbitComponent
    (D.orbit_fitting h) (D.orbit_twoCore_eq_bot h) _ hi.choose
    (hi.not_le_fixedSpace D.orbitRepresentation) A hA

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
