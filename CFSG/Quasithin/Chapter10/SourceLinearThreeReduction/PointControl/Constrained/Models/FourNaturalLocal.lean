module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.FourNaturalLocal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalSeven
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage
public import Theory.GroupTheory.ReducedNormal.NormalRestriction

/-!
# The faithful action on a local fixed involution's orbit

The smaller orbit detects the original component's two-core kernel:
otherwise the component centralizes that orbit and lies in the original
maximal local subgroup. Comparing kernels across the normal component
and its two-group supplement identifies the smaller orbit's centralizer
with that of VI. Thus the original Thompson movement survives restriction,
and the complete B.5.1 classification applies to the smaller orbit.

Original row exhaustion and exclusion of the binary containing actions
remain with qt-d-10-nona5-point-constrained. These are reductions of the
retained four-natural case, not an assertion of its impossibility.
Source: Aschbacher--Smith 10.2.9, printed pp.751--752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The local seed orbit detects the exact two-core kernel of the original containing component. -/
theorem Context.local_seed_component_kernel_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let R := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
    letI := (c.local_seed_orbit_reduced hu).normal
    ((actionMk R).subgroupMap (I.subgroupOf (pointJoin T v I))).ker =
      pCore 2 (I.subgroupOf (pointJoin T v I)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let V := conjugateSpanBy (zpowers u) I
  let R := V.subgroupOf H
  have hR := c.local_seed_orbit_reduced hu
  let := hR.normal
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hVI : V ≤ I := conjugateSpanBy_le_self
    (zpowers_le.mpr (c.escaping.strict.le
      ((source_full_moved_le_component D)
        ((commutator_mono (le_componentOrbit _ _) le_rfl) hu.1))))
  have hVH : V ≤ H := hVI.trans le_sup_left
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨_,_,d,hd,⟨E⟩⟩ := c.binary_source_action_of_four_natural_cover h
  let := c.component_head_quasisimple_of_binary_actor hd E
  let eK : K ≃* I := subgroupOfEquivOfLe le_sup_left
  let eQ := QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv eQ.symm
  let f := (eQ.trans (c.binaryActorQuotient hd E)).trans
    (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < d)).symm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) :=
    Atlas.psl_simple_high_rank d (by omega)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := f.isSimpleGroup
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    rcases (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative (K ⧸ pCore 2 K)
        (center_eq_top_iff.mp hz)).elim
  have hm : ⁅R,K⁆ ≠ ⊥ := by
    intro he
    have hc : K ≤ centralizer (R : Set H) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    apply c.escaping.escapes
    intro i hi
    apply c.local_orbit_centralizer_le_of_four_natural_cover h hu hne
    intro z hz
    exact congrArg H.subtype
      (hc (show (⟨i,(le_sup_left : I ≤ H) hi⟩ : H) ∈ K from hi) ⟨z,hVH hz⟩ hz)
  exact reduced_quasisimple_subgroupMap_ker R K hR hz hm

/-- Every original marked row supplies a concrete local involution and its
reduced orbit, with the literal original component kernel. -/
theorem Context.local_seed_orbit_of_original_moved_cover
    (c : Context D t v I) (h : OriginalMovedCover D) :
    ∃ u : G, ∃ hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G),
      u ≠ 1 ∧ conjugateSpanBy (zpowers u) L = ⁅D.moduleSubgroup,L⁆ ∧
      conjugateSpanBy (zpowers u) I ≤ orbitModule D v I ∧
      centralizer (conjugateSpanBy (zpowers u) I : Set G) ≤ D.maximalLocal ∧
      let R := (conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)
      letI := (c.local_seed_orbit_reduced hu).normal
      ((actionMk R).subgroupMap (I.subgroupOf (pointJoin T v I))).ker =
        pCore 2 (I.subgroupOf (pointJoin T v I)) := by
  have hf := c.four_natural_of_original_moved_cover h
  have hcard := c.local_point_fixed_card_of_four_natural_cover hf
  have hn : ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G) ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hcard
    omega
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hn
  have hne : (u:G) ≠ 1 := fun he => hu (Subtype.ext he)
  refine ⟨u,u.property,hne,c.local_moved_eq_span_of_four_natural_seed hf u.property hne,
    ?_,c.local_orbit_centralizer_le_of_four_natural_cover hf u.property hne,
    c.local_seed_component_kernel_of_four_natural_cover hf u.property hne⟩
  exact conjugateSpanBy_mono (zpowers_le.mpr
    ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) u.property.1,u.property.2⟩) le_rfl

/-- Restricting to the single local seed orbit preserves the full point-join action kernel. -/
theorem Context.local_seed_centralizer_eq_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    centralizer (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)) :
      Set (pointJoin T v I)) =
      centralizer (internalModule D v I : Set (pointJoin T v I)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
  have hr := c.local_seed_orbit_reduced hu
  let := hr.normal
  let := c.reduced.normal
  let := c.reduced.elementary
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hRU : R ≤ internalModule D v I := comap_mono
    (conjugateSpanBy_mono (zpowers_le.mpr
      ⟨(commutator_mono (le_componentOrbit _ _) le_rfl) hu.1,hu.2⟩) le_rfl)
  obtain ⟨_,_,d,hd,⟨E⟩⟩ := c.binary_source_action_of_four_natural_cover h
  have hk : K ⊓ centralizer (R : Set H) ≤ centralizer (internalModule D v I : Set H) := by
    intro z hz
    have hzK : (⟨z,hz.1⟩ : K) ∈ ((actionMk R).subgroupMap K).ker :=
      Subtype.ext ((QuotientGroup.eq_one_iff z).mpr hz.2)
    rw [c.local_seed_component_kernel_of_four_natural_cover h hu hne,
      ←c.action_kernel_eq_twoCore_of_binary_actor hd E] at hzK
    exact (QuotientGroup.eq_one_iff z).mp (congrArg Subtype.val
      (show ((actionMk (internalModule D v I)).subgroupMap K) ⟨z,hz.1⟩ = 1 from hzK))
  apply c.reduced.centralizer_eq_of_normal_intersection hRU K
    ((pointSylow T v).subgroupOf H) (T.isPGroup'.to_le inf_le_left).comap_subtype ?_ hk
  rw [←subgroupOf_sup (show I ≤ H from le_sup_left) (show pointSylow T v ≤ H from le_sup_right)]
  exact subgroupOf_self H

/-- The actual orbit of one local fixed involution is a faithful reduced FF
module with the complete B.5.1 conclusion and the original point action kernel. -/
theorem Context.local_seed_ff_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    let A := (I.subgroupOf H).map (actionMk R)
    let N := offenderSubgroup (action R)
    IsFFModule (V := Additive R) (action R) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action R).comp N.subtype) (A.subgroupOf N)) := by
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
  exact ⟨isFFModule_of_thompson_movement P R hm,
    quasisimple_source_conclusion_of_thompson_movement c.join_sqtk P
      (I.subgroupOf H) R hK hKP hr.quotient_pCore_eq_bot hm⟩

/-- The smaller local orbit is fully moved by its original component. -/
theorem Context.local_seed_orbit_fully_moved_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    letI := (c.local_seed_orbit_reduced hu).elementary
    ChapterB.QuasisimpleSource.moved (action R) ((I.subgroupOf H).map (actionMk R)) = ⊤ := by
  let H := pointJoin T v I
  let V := conjugateSpanBy (zpowers u) I
  let R := V.subgroupOf H
  have hr := c.local_seed_orbit_reduced hu
  let := hr.normal
  let := hr.elementary
  have hWI : ⁅D.moduleSubgroup,L⁆ ≤ I :=
    (commutator_mono (le_componentOrbit _ _) le_rfl).trans
      ((source_full_moved_le_component D).trans c.escaping.strict.le)
  have hVI : V ≤ I := conjugateSpanBy_le_self (zpowers_le.mpr (hWI hu.1))
  have hVH : V ≤ H := hVI.trans le_sup_left
  have hWW : ⁅⁅D.moduleSubgroup,L⁆,L⁆ = ⁅D.moduleSubgroup,L⁆ := by
    apply commutator_isPPerfect_idempotent L D.moduleSubgroup D.faithful.1.2.1
      ((D.fullModule_elementary (source_module_nonsolvable_uniqueness D)).isPGroup.to_le (le_componentOrbit _ _))
    exact (le_componentOrbit L T).trans D.orbit_normalizes_module
  have hcomm : ⁅V,I⁆ = V := by
    apply le_antisymm
      (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _))
    rw [←c.local_orbit_eq_seed_orbit_of_four_natural_cover h hu hne]
    apply conjugateSpanBy_le ?_ (normalizer_commutator_ge_right _ _)
    exact hWW.ge.trans (commutator_mono (le_conjugateSpanBy _ _) c.escaping.strict.le)
  have hcomm' : ⁅R,I.subgroupOf H⁆ = R := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le le_sup_left]
    exact hcomm
  change ChapterB.QuasisimpleSource.moved (action R) ((I.subgroupOf H).map (actionMk R)) = ⊤
  rw [←ChapterB.QuasisimpleSource.SourceCompletion.coinvariants_eq_moved]
  exact Representation.NormalElementaryQuotient.coinvariants_image_eq_top R (actionMk R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (I.subgroupOf H)
    (comap_mono hVI) hcomm'

/-- The smaller orbit has the same literal binary containing quotient as VI. -/
theorem Context.local_seed_binary_actor_of_four_natural_cover
    (c : Context D t v I) (h : FourNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    let H := pointJoin T v I
    let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
    letI := (c.local_seed_orbit_reduced hu).normal
    let A := (I.subgroupOf H).map (actionMk R)
    ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  let H := pointJoin T v I
  let R := (conjugateSpanBy (zpowers u) I).subgroupOf H
  let K := I.subgroupOf H
  let := (c.local_seed_orbit_reduced hu).normal
  let f := (actionMk R).subgroupMap K
  let k : K ≃* I := subgroupOfEquivOfLe le_sup_left
  let q : (K ⧸ pCore 2 K) ≃* (I ⧸ pCore 2 I) :=
    QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let r := (QuotientGroup.quotientKerEquivOfSurjective f
    ((actionMk R).subgroupMap_surjective K)).symm
  obtain ⟨d,hd,⟨e⟩⟩ := c.binary_quotient_of_four_natural_cover h
  exact ⟨d,hd,⟨((r.trans (QuotientGroup.quotientMulEquivOfEq
    (c.local_seed_component_kernel_of_four_natural_cover h hu hne))).trans q).trans e⟩⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
