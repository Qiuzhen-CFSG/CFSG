module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalLocalPair
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.FourNaturalActions
public import Theory.Representation.BinaryConjugationSection.Restriction

/-!
# The orbit of the original local natural three-space

The actual natural marking of [D.moduleSubgroup,L] gives a unique point-Sylow
fixed line. Its nonidentity vector generates that local three-space. Its orbit
under the containing component retains the exact action kernel of the full VI,
so Thompson movement and the B.5.1 action classification pass to this smaller
orbit. No marking or dimension is imposed on the whole original moved module.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752. The resulting smaller
orbit is used by OriginalNaturalActions in the original point-control reduction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Coordinates on the literal local moved subgroup, with trivial kernel. -/
def LocalNaturalCover (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ e : (L ⧸ pCore 2 L) ≃* BinaryLinearThree.Group,
    Nonempty (BinaryConjugationSection L ⁅D.moduleSubgroup,L⁆ ⊥
      (BinaryLinearThree.W.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))

/-- The original natural marking forces a cubic divisor of the component quotient. -/
theorem LocalNaturalCover.three_dvd (h : LocalNaturalCover D) :
    3 ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨e,_⟩ := h
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL]
  decide

/-- The actual local moved subgroup has order eight. -/
theorem Context.local_moved_card_of_local_natural (_c : Context D t v I)
    (h : LocalNaturalCover D) : Nat.card (⁅D.moduleSubgroup,L⁆ : Subgroup G) = 8 := by
  obtain ⟨e,⟨r⟩⟩ := h
  have hc := r.card_section
  simpa using hc

/-- The point Sylow fixes precisely one line in the literal local natural copy. -/
theorem Context.local_point_fixed_card_of_local_natural (c : Context D t v I)
    (h : LocalNaturalCover D) :
    Nat.card (⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G) : Subgroup G) = 2 := by
  obtain ⟨e,⟨r⟩⟩ := h
  let W := ⁅D.moduleSubgroup,L⁆
  let P := pointSylow T v
  let F := W ⊓ centralizer (P : Set G)
  have hWF : W ≤ ⁅D.fullModule,L⁆ := commutator_mono (le_componentOrbit _ _) le_rfl
  have hWP : P ≤ normalizer (W : Set G) :=
    ((le_inf inf_le_left c.escaping.sylow_normalizes).trans le_sup_right).trans
      c.halfJoin_normalizes_local_moved
  have hfix : F ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups P W
    (T.isPGroup'.to_le inf_le_left)
    ((source_original_full_moved_elementary D).isPGroup.to_le hWF) hWP
    (Selection.ModuleChoice.local_moved_ne_bot D)
  have hlo : 1 < Nat.card F := (one_lt_card_iff_ne_bot F).mpr hfix
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  obtain ⟨R,hR⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (H := localJoin T L)
    ⟨T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
      map_subgroupOf_eq_of_le le_sup_right⟩ hLH hc.subnormal
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := R.mapSurjective hq
  have hRP : (R : Subgroup L).map L.subtype ≤ P := by
    rw [hR]
    exact le_inf inf_le_left (inf_le_right.trans
      (c.escaping.strict.le.trans c.escaping.le_centralizer))
  let f : F → fixedSpace BinaryLinearThree.W (Q : Subgroup BinaryLinearThree.Group) :=
    fun z => ⟨(r.coordinates ⟨z,z.property.1⟩).toAdd,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      have hh := r.equivariant l ⟨z,z.property.1⟩
      have hz : (⟨(l:G)*z*(l:G)⁻¹,
          (mem_normalizer_iff.mp (r.normalized l.property) (z:G)).mp z.property.1⟩ : W) = ⟨z,z.property.1⟩ := by
        apply Subtype.ext
        change (l:G)*(z:G)*(l:G)⁻¹ = (z:G)
        rw [z.property.2 l (hRP (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
      rw [hz] at hh
      change (r.coordinates ⟨z,z.property.1⟩).toAdd =
        BinaryLinearThree.W (q l) (r.coordinates ⟨z,z.property.1⟩).toAdd at hh
      rw [he] at hh
      exact hh.symm⟩
  have hrinj : Function.Injective r.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r.kernel_eq,bot_subgroupOf])
  have hi : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    exact congrArg (fun a : W => (a:G)) (hrinj (congrArg Subtype.val he))
  have hup := (Nat.card_le_card_of_injective f hi).trans
    (BinaryLinearThree.card_sylow_natural_fixed_le_two Q)
  change Nat.card F ≤ 2 at hup
  change Nat.card F = 2
  omega

/-- A nonzero vector generates the literal local natural three-space. -/
theorem Context.local_moved_eq_span_of_local_natural_seed (_c : Context D t v I)
    (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) : conjugateSpanBy (zpowers u) L = ⁅D.moduleSubgroup,L⁆ := by
  obtain ⟨e,⟨r⟩⟩ := h
  let W := ⁅D.moduleSubgroup,L⁆
  let A := conjugateSpanBy (zpowers u) L
  have hAW : A ≤ W :=
    conjugateSpanBy_le (zpowers_le.mpr hu.1) (normalizer_commutator_ge_right _ _)
  have hAb : ¬ A ≤ ⊥ := by
    intro hb
    exact hne (mem_bot.mp (hb (le_conjugateSpanBy _ _ (mem_zpowers u))))
  have hs := r.restricted_coordinates_surjective_of_transitive A hAW
    (le_normalizer_conjugateSpanBy _ _) hAb (by
      intro x y hx hy
      obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three x y hx hy
      obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
      exact ⟨l,(congrArg (fun g => specialLinearNatural 3 g x) hl).trans hg⟩)
  have hi : Function.Injective r.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [r.kernel_eq,bot_subgroupOf])
  apply le_antisymm hAW
  intro w hw
  obtain ⟨a,ha⟩ := hs (r.coordinates ⟨w,hw⟩)
  have he : (a:G) = w := congrArg Subtype.val (hi ha)
  exact he ▸ a.property

/-- The local I-orbit can be generated by its single point-fixed involution. -/
theorem Context.local_orbit_eq_seed_orbit_of_local_natural (c : Context D t v I)
    (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    conjugateSpanBy ⁅D.moduleSubgroup,L⁆ I = conjugateSpanBy (zpowers u) I := by
  apply le_antisymm
  · apply conjugateSpanBy_le ?_ (le_normalizer_conjugateSpanBy _ _)
    rw [←c.local_moved_eq_span_of_local_natural_seed h hu hne]
    exact conjugateSpanBy_mono le_rfl c.escaping.strict.le
  · exact conjugateSpanBy_mono (zpowers_le.mpr hu.1) le_rfl

/-- The smaller orbit retains ambient centralizer control on the original point configuration. -/
theorem Context.local_orbit_centralizer_le_of_local_natural (c : Context D t v I)
    (h : LocalNaturalCover D) {u : G}
    (hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G))
    (hne : u ≠ 1) :
    centralizer (conjugateSpanBy (zpowers u) I : Set G) ≤ D.maximalLocal := by
  rw [←c.local_orbit_eq_seed_orbit_of_local_natural h hu hne]
  exact (centralizer_le (le_conjugateSpanBy _ _)).trans
    ((Subgroup.centralizer_le_normalizer _).trans c.local_moved_normalizer_le)

/-- The local seed orbit detects the exact two-core kernel of the original containing component. -/
theorem Context.local_seed_component_kernel_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
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
  obtain ⟨_,_,d,hd,⟨E⟩⟩ := c.original_binary_source_action (c.actionFacts_of_three h.three_dvd)
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
    apply c.local_orbit_centralizer_le_of_local_natural h hu hne
    intro z hz
    exact congrArg H.subtype
      (hc (show (⟨i,(le_sup_left : I ≤ H) hi⟩ : H) ∈ K from hi) ⟨z,hVH hz⟩ hz)
  exact reduced_quasisimple_subgroupMap_ker R K hR hz hm

/-- Restricting to the single local seed orbit preserves the full point-join action kernel. -/
theorem Context.local_seed_centralizer_eq_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
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
  obtain ⟨_,_,d,hd,⟨E⟩⟩ := c.original_binary_source_action (c.actionFacts_of_three h.three_dvd)
  have hk : K ⊓ centralizer (R : Set H) ≤ centralizer (internalModule D v I : Set H) := by
    intro z hz
    have hzK : (⟨z,hz.1⟩ : K) ∈ ((actionMk R).subgroupMap K).ker :=
      Subtype.ext ((QuotientGroup.eq_one_iff z).mpr hz.2)
    rw [c.local_seed_component_kernel_of_local_natural h hu hne,
      ←c.action_kernel_eq_twoCore_of_binary_actor hd E] at hzK
    exact (QuotientGroup.eq_one_iff z).mp (congrArg Subtype.val
      (show ((actionMk (internalModule D v I)).subgroupMap K) ⟨z,hz.1⟩ = 1 from hzK))
  apply c.reduced.centralizer_eq_of_normal_intersection hRU K
    ((pointSylow T v).subgroupOf H) (T.isPGroup'.to_le inf_le_left).comap_subtype ?_ hk
  rw [←subgroupOf_sup (show I ≤ H from le_sup_left) (show pointSylow T v ≤ H from le_sup_right)]
  exact subgroupOf_self H

/-- The actual orbit of one local fixed involution is a faithful reduced FF
module with the complete B.5.1 conclusion and the original point action kernel. -/
theorem Context.local_seed_ff_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
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
  have hc := c.local_seed_centralizer_eq_of_local_natural h hu hne
  have p := c.prepared_of_three h.three_dvd
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
theorem Context.local_seed_orbit_fully_moved_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
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
    rw [←c.local_orbit_eq_seed_orbit_of_local_natural h hu hne]
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
theorem Context.local_seed_binary_actor_of_local_natural
    (c : Context D t v I) (h : LocalNaturalCover D) {u : G}
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
  obtain ⟨d,hd,⟨e⟩⟩ := c.original_containing_binary_quotient (c.actionFacts_of_three h.three_dvd)
  exact ⟨d,hd,⟨((r.trans (QuotientGroup.quotientMulEquivOfEq
    (c.local_seed_component_kernel_of_local_natural h hu hne))).trans q).trans e⟩⟩

/-- The original natural branch supplies a nonidentity local seed whose
smaller orbit retains the full VI action kernel. -/
theorem Context.local_seed_of_local_natural (c : Context D t v I)
    (h : LocalNaturalCover D) :
    ∃ u : G, ∃ _hu : u ∈ ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G),
      u ≠ 1 ∧ conjugateSpanBy (zpowers u) L = ⁅D.moduleSubgroup,L⁆ ∧
      centralizer (((conjugateSpanBy (zpowers u) I).subgroupOf (pointJoin T v I)) :
        Set (pointJoin T v I)) =
        centralizer (internalModule D v I : Set (pointJoin T v I)) := by
  have hc := c.local_point_fixed_card_of_local_natural h
  have hn : ⁅D.moduleSubgroup,L⁆ ⊓ centralizer (pointSylow T v : Set G) ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hc
    omega
  obtain ⟨u,hu⟩ := ne_bot_iff_exists_ne_one.mp hn
  have hne : (u:G) ≠ 1 := fun he => hu (Subtype.ext he)
  exact ⟨u,u.property,hne,c.local_moved_eq_span_of_local_natural_seed h u.property hne,
    c.local_seed_centralizer_eq_of_local_natural h u.property hne⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
