module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalDual
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved

/-!
# Remaining binary actions on the local fixed involution's orbit

The smaller reduced orbit's component lies in its actual offender group.
B.5.1 for its marked binary actor, the local natural--dual exclusion and
the proved multiplicity-one result leave a single natural module, an
orthogonal six-space or its seven-dimensional cover, or an irreducible
of dimension ten. The fixed attachment in the orthogonal case is retained.

The natural and ten-dimensional actions fill the full action quotient.
Thus an SL₅(2) actor makes the smaller orbit irreducible of dimension five
or ten. Equality of its centralizer with that of VI transfers the whole
actor conclusion back to VI, without asserting irreducibility of VI or
containment of the full four-copy moved subgroup in the smaller orbit.

The remaining action exclusions and original row exhaustion stay with
qt-d-10-nona5-point-constrained. Source applies this reduction to the literal
point-control contract. Source: Aschbacher--Smith B.5.1 and10.2.9,
printed pp.99--103,751--753.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The smaller orbit's literal component is contained in its own offender group. -/
theorem Context.local_seed_actor_le_offender_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    (I.subgroupOf H).map (actionMk R) ≤ offenderSubgroup (action R) := by
  let H := pointJoin T v I
  let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
  have hr := c.local_seed_orbit_reduced hu
  let := hr.normal
  let := hr.elementary
  have hc := c.local_seed_centralizer_eq_of_four_natural_cover h hu hne
  have p := c.prepared_of_four_natural_cover h
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hjmap : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      Stellmacher.elementaryAbelianMaxJ (pointSylow T v) := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
  have hm : ¬ Stellmacher.elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (R : Set H) := by
    intro hz
    apply p.thompson_moves
    rw [←hjmap]
    rintro _ ⟨j,hj,rfl⟩ z hz'
    have hh : j ∈ centralizer (internalModule D v I : Set H) := hc ▸ hz hj
    exact congrArg H.subtype (hh ⟨z,c.orbit_le_join hz'⟩ hz')
  let : (I.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hK : (I.subgroupOf H).IsCComponent := c.escaping.component.subgroupOf_of_le
    le_sup_left (sup_le c.escaping.le_centralizer inf_le_right)
  have hKP : I.subgroupOf H ⊔ (P : Subgroup H) = ⊤ := by
    rw [hP',←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  let := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple c.join_sqtk
    P (I.subgroupOf H) R hK hKP hr.quotient_pCore_eq_bot hm
  exact component_le_offenderSubgroup P (I.subgroupOf H) R hKP hr.quotient_pCore_eq_bot hm

/-- Remaining actions on the whole smaller orbit. The orthogonal case retains
both the natural six-space and its nonsplit seven-dimensional cover. -/
inductive BinarySingleOrbitAction
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) : Prop
  | natural (d : ℕ) (degree : d = 4 ∨ d = 5) (whole : A = ⊤)
      (action : ActionEquiv (ρ.comp A.subtype) (linearNatural BinaryField.two d))
  | orthogonal (actor : A ≃* SL(4,ZMod 2))
      (model : IsAlternatingNatural (ρ.comp A.subtype) 8 ∨
        Nonempty (ActionEquiv (ρ.comp A.subtype)
          (BinaryPermutation.alternatingCoreRepresentation (Fin 8))))
      (dimension : Module.finrank (ZMod 2) V = 6 ∨ Module.finrank (ZMod 2) V = 7)
  | exterior (actor : A ≃* SL(5,ZMod 2)) (whole : A = ⊤)
      (irreducible : IsIrreducible (ρ.comp A.subtype))
      (dimension : Module.finrank (ZMod 2) V = 10)

/-- The local fixed involution's orbit has only the single natural,
orthogonal-cover, or ten-dimensional irreducible containing action.
The natural--dual and higher repeated rows are discharged on this actual orbit. -/
theorem Context.local_seed_single_action_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    BinarySingleOrbitAction (action U) A := by
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  let : (I.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  let : A.Normal := Normal.map inferInstance (actionMk U) (QuotientGroup.mk'_surjective _)
  have hAN : A ≤ N := c.local_seed_actor_le_offender_of_four_natural_cover h hu hne
  obtain ⟨d,hd,⟨eb⟩⟩ := c.local_seed_binary_actor_of_four_natural_cover h hu hne
  obtain ⟨_,⟨r⟩⟩ := c.local_seed_ff_of_four_natural_cover h hu hne
  have hm := ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor.movedCase hd
    (ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor.actionCase _ hd
      ((subgroupOfEquivOfLe hAN).trans eb) r.clause_one)
  have hs : r.sectionData.space.toSubmodule = ⊤ := by
    rw [r.sectionData.space_eq,moved_comp_map,map_subgroupOf_eq_of_le hAN]
    exact c.local_seed_orbit_fully_moved_of_four_natural_cover h hu hne
  let j : Additive U ≃ₗ[ZMod 2] r.sectionData.space.toSubmodule := LinearEquiv.ofBijective
    ((LinearMap.id : Additive U →ₗ[ZMod 2] Additive U).codRestrict r.sectionData.space.toSubmodule
      (fun _ => hs.symm ▸ Submodule.mem_top))
    ⟨fun _ _ he => congrArg Subtype.val he,fun w => ⟨w.val,Subtype.ext rfl⟩⟩
  cases hm with
  | natural E =>
    let f : ActionEquiv ((action U).comp A.subtype) (linearNatural BinaryField.two d) := {
      groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
      linearEquiv := j.trans E.linearEquiv
      intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }
    exact .natural d hd (BinaryLinearNormalActors.normal_natural_eq_top
      (action U) (action_faithful U) A d f.groupEquiv f.linearEquiv f.intertwines) f
  | orthogonal hd4 _ model dim =>
    subst d
    refine .orthogonal eb ?_ (dim.imp (j.finrank_eq.trans) (j.finrank_eq.trans))
    rcases model with E | E
    · obtain ⟨E⟩ := E
      exact Or.inl ⟨{
        groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
        linearEquiv := j.trans E.linearEquiv
        intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }⟩
    · obtain ⟨E⟩ := E
      exact Or.inr ⟨{
        groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
        linearEquiv := j.trans E.linearEquiv
        intertwines := fun a w => E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w) }⟩
  | exterior _ E hi dim =>
    let e : ActionEquiv ((action U).comp A.subtype)
        (r.sectionData.space.toRepresentation.comp (A.subgroupOf N).subtype) := {
      groupEquiv := (subgroupOfEquivOfLe hAN).symm
      linearEquiv := j
      intertwines := fun _ _ => rfl }
    have hi' := ExtensionConsequences.irreducible_of_equiv e hi
    let := hi'
    have hdim := j.finrank_eq.trans dim
    let eb5 := (subgroupOfEquivOfLe hAN).symm.trans E
    exact .exterior eb5 (BinaryLinearNormalActors.normal_ten_dimensional_eq_top
      (action U) (action_faithful U) A eb5 hdim) hi' hdim
  | naturalDual E =>
    exact (c.no_natural_dual_section_of_local_seed h hu hne hd N hAN r.sectionData E.some).elim
  | repeatedNatural n hn _ E =>
    obtain ⟨E⟩ := E
    have hn1 := c.repeated_section_multiplicity_one_of_local_seed h hu hne hd hn N hAN r.sectionData E
    subst n
    let one : (Fin 1 → Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) := {
      toFun w := w 0
      invFun w _ := w
      left_inv w := funext fun i => congrArg w (Subsingleton.elim _ _)
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    let f : ActionEquiv ((action U).comp A.subtype) (linearNatural BinaryField.two d) := {
      groupEquiv := (subgroupOfEquivOfLe hAN).symm.trans E.groupEquiv
      linearEquiv := (j.trans E.linearEquiv).trans one
      intertwines := fun a w => congrFun (E.intertwines ((subgroupOfEquivOfLe hAN).symm a) (j w)) 0 }

    exact .natural d hd (BinaryLinearNormalActors.normal_natural_eq_top
      (action U) (action_faithful U) A d f.groupEquiv f.linearEquiv f.intertwines) f

/-- In particular, the smaller orbit has at most ten binary dimensions,
including its complete central attachment. -/
theorem Context.local_seed_dimension_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
    letI := (c.local_seed_orbit_reduced hu).elementary
    Module.finrank (ZMod 2) (Additive U) = 4 ∨
      Module.finrank (ZMod 2) (Additive U) = 5 ∨
      Module.finrank (ZMod 2) (Additive U) = 6 ∨
      Module.finrank (ZMod 2) (Additive U) = 7 ∨
      Module.finrank (ZMod 2) (Additive U) = 10 := by
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  have ha := c.local_seed_single_action_of_four_natural_cover h hu hne
  cases ha with
  | natural d hd _ E =>
    have he := E.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
    rcases hd with rfl | rfl
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
  | orthogonal _ _ dim => exact Or.inr (Or.inr (dim.imp_right Or.inl))
  | exterior _ _ _ dim => exact Or.inr (Or.inr (Or.inr (Or.inr dim)))



/-- In the binary-five branch the smaller orbit is genuinely irreducible,
of dimension five or ten, and its component fills the full action quotient. -/
theorem Context.local_seed_irreducible_of_binary_five
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk U)
    ∀ (_E : A ≃* SL(5,ZMod 2)),
      A = ⊤ ∧ IsIrreducible ((action U).comp A.subtype) ∧
        (Module.finrank (ZMod 2) (Additive U) = 5 ∨
          Module.finrank (ZMod 2) (Additive U) = 10) := by
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let A := (I.subgroupOf H).map (actionMk U)
  dsimp only
  intro E
  have ha := c.local_seed_single_action_of_four_natural_cover h hu hne
  cases ha with
  | natural d hd ht f =>
    have hd5 := ChapterB.QuasisimpleSource.SourceCompletion.binary_degree_eq hd (Or.inr rfl)
      (f.groupEquiv.symm.trans E)
    subst d
    exact ⟨ht,ExtensionConsequences.irreducible_of_equiv f
      (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide)),
      Or.inl (f.linearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2)))⟩
  | orthogonal eb _ _ =>
    have he := ChapterB.QuasisimpleSource.SourceCompletion.binary_degree_eq
      (Or.inl rfl : 4 = 4 ∨ 4 = 5) (Or.inr rfl : 5 = 4 ∨ 5 = 5) (eb.symm.trans E)
    omega
  | exterior _ ht hi hd => exact ⟨ht,hi,Or.inr hd⟩

/-- Fullness of the component action on the smaller orbit transfers back
to the original VI quotient through the proved equality of centralizers. -/
theorem Context.original_actor_eq_top_of_local_seed_five
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    ∀ (_E : ((I.subgroupOf H).map (actionMk U)) ≃* SL(5,ZMod 2)),
      letI := c.reduced.normal
      (I.subgroupOf H).map (actionMk (internalModule D v I)) = ⊤ := by
  let H := pointJoin T v I
  let U := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let := (c.local_seed_orbit_reduced hu).elementary
  let := c.reduced.normal
  dsimp only
  intro E
  have ht := (c.local_seed_irreducible_of_binary_five h hu hne E).1
  have hc := c.local_seed_centralizer_eq_of_four_natural_cover h hu hne
  change (I.subgroupOf H).map (QuotientGroup.mk' (centralizer (U : Set H))) = ⊤ at ht
  change (I.subgroupOf H).map
    (QuotientGroup.mk' (centralizer (internalModule D v I : Set H))) = ⊤
  change centralizer (U : Set H) = centralizer (internalModule D v I : Set H) at hc
  apply comap_injective (QuotientGroup.mk'_surjective _)
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top]
  have he := congrArg (comap (QuotientGroup.mk' (centralizer (U : Set H)))) ht
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top,hc] at he
  exact he

end CFSG.Quasithin.Chapter10.PointControl.Constrained
