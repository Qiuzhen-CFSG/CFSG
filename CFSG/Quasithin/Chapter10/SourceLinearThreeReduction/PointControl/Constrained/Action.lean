module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Setup
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# The constrained component in its actual centralizer quotient

Centralizer control makes the smaller component image proper. Normal generation
by L makes that image nonzero even when [V,L] is not contained in VI. The
containing component consequently has a solvable action kernel, so the literal
local-component condition descends at the image of its original Sylow subgroup.
Thompson movement then supplies the faithful FF action and the complete B.5.1
conclusion. Neither step assumes an A5 marking or full fixed-span promotion.

Source: Aschbacher--Smith, 10.2.9, printed p.751.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Normal generation, rather than an unproved full-span inclusion, keeps
the original smaller component nonzero and proper in the literal action. -/
theorem Context.small_image_strict (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal) :
    let H := pointJoin T v I
    let U := internalModule D v I
    letI := c.reduced.normal
    (L.subgroupOf H).map (actionMk U) ≠ ⊥ ∧
      (L.subgroupOf H).map (actionMk U) < (I.subgroupOf H).map (actionMk U) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let q := actionMk U
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  have hLM : L ≤ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hkerM : q.ker ≤ D.maximalLocal.subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    apply hc
    intro w hw
    exact congrArg H.subtype (ha ⟨w,c.orbit_le_join hw⟩ hw)
  constructor
  · intro hz
    have hLker := (Subgroup.map_eq_bot_iff _).mp hz
    have hLC : L ≤ centralizer (orbitModule D v I : Set G) := by
      intro l hl w hw
      have hh : (⟨l,hLH hl⟩ : H) ∈ centralizer (U : Set H) := by
        simpa only [actionMk,QuotientGroup.ker_mk'] using
          hLker (show (⟨l,hLH hl⟩ : H) ∈ L.subgroupOf H from hl)
      exact congrArg H.subtype (hh ⟨w,c.orbit_le_join hw⟩ hw)
    have hIC : I ≤ normalizer (centralizer (orbitModule D v I : Set G) : Set G) :=
      (le_normalizer_conjugateSpanBy _ I).trans
        (normalizer_le_normalizer_centralizer _)
    have hIG : I ≤ centralizer (orbitModule D v I : Set G) := by
      calc
        I = componentOrbit L I := c.escaping.generation.symm
        _ ≤ centralizer (orbitModule D v I : Set G) :=
          iSup_conjugates_le_of_le_normalizer _ _ _ hLC hIC
    exact c.escaping.escapes (hIG.trans hc)
  · apply lt_of_le_of_ne (map_mono (comap_mono c.escaping.strict.le))
    intro he
    have hle : I.subgroupOf H ≤ L.subgroupOf H ⊔ q.ker := by
      rw [←comap_map_eq]
      exact map_le_iff_le_comap.mp he.ge
    have hIM : I.subgroupOf H ≤ D.maximalLocal.subgroupOf H :=
      hle.trans (sup_le (comap_mono hLM) hkerM)
    exact c.escaping.escapes (fun i hi =>
      hIM (show (⟨i,(show I ≤ H from le_sup_left) hi⟩ : H) ∈ I.subgroupOf H from hi))

/-- The action kernel on I is a proper normal subgroup of this C-component,
and is therefore solvable. -/
theorem Context.action_kernel_solvable (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal) :
    letI := c.reduced.normal
    Group.IsSolvable ((actionMk (internalModule D v I)).subgroupMap
      (I.subgroupOf (pointJoin T v I))).ker := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let K := I.subgroupOf H
  let f := (actionMk U).subgroupMap K
  have hK : K.IsCComponent := c.escaping.component.subgroupOf_of_le
    le_sup_left (sup_le c.escaping.le_centralizer inf_le_right)
  have hn : K.map (actionMk U) ≠ ⊥ := by
    intro hz
    exact (c.small_image_strict hc).1 (eq_bot_iff.mpr
      (hz ▸ (map_mono (comap_mono c.escaping.strict.le))))
  have hp : f.ker ≠ ⊤ := by
    intro he
    apply hn
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro _ ⟨a,ha,rfl⟩
    have hm : (⟨a,ha⟩ : K) ∈ f.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show f ⟨a,ha⟩ = 1 from hm)
  exact hK.isSolvable_of_subnormal_lt_top (inferInstance : f.ker.Normal).isSubnormal hp

/-- The original local component descends at the image of the full Sylow
intersection, without assuming that its two-core centralizes VI. -/
theorem Context.small_image_local (c : Context D t v I)
    (hc : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal) :
    let H := pointJoin T v I
    letI := c.reduced.normal
    let K := I.subgroupOf H
    let q := actionMk (internalModule D v I)
    let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
    B < ⊤ ∧ ∃ R : Sylow 2 K,
      (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K ∧
      B ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  let H := pointJoin T v I
  let := c.reduced.normal
  let K := I.subgroupOf H
  let A := L.subgroupOf H
  let q := actionMk (internalModule D v I)
  let B := (A.map q).subgroupOf (K.map q)
  let f := q.subgroupMap K
  have hAK : A ≤ K := comap_mono c.escaping.strict.le
  have hab : A.map q ≤ K.map q := map_mono hAK
  have hp : B < ⊤ := lt_top_iff_ne_top.mpr (fun he => by
    have hh := congrArg (Subgroup.map (K.map q).subtype) he
    rw [map_subgroupOf_eq_of_le hab,←MonoidHom.range_eq_map,range_subtype] at hh
    exact (c.small_image_strict hc).2.ne hh)
  refine ⟨hp,?_⟩
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hAlocal : A ∈ localCComponents P := by
    rw [hP']
    exact SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1)
      (c.escaping.strict.le.trans le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  obtain ⟨R,hR,hAR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hAlocal hAK
    (inferInstance : K.Normal).isSubnormal
  have hR' : (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K := by
    rw [hR,hP']
    ext x
    exact and_iff_left (c.escaping.le_centralizer x.property)
  let : Group.IsSolvable f.ker := c.action_kernel_solvable hc
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hAR f
  have himage : (A.subgroupOf K).map f = B := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map.mpr ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,hax⟩
      exact ⟨⟨a,hAK ha⟩,ha,Subtype.ext hax⟩
  refine ⟨R,hR',?_⟩
  simpa only [himage,Sylow.coe_mapSurjective] using hlocal

/-- Thompson movement supplies the actual quasisimple FF actor and every
clause of B.5.1 on its literal moved section. -/
theorem Context.ff_action (c : Context D t v I) (p : Prepared D v I) :
    let H := pointJoin T v I
    let U := internalModule D v I
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf H).map (actionMk U)
    let N := offenderSubgroup (action U)
    IsQuasisimple A ∧ A ≤ N ∧
      ⁅A,(elementaryAbelianMaxJ ((pointSylow T v).subgroupOf H)).map (actionMk U)⁆ = A ∧
      IsFFModule (V := Additive U) (action U) ∧ Function.Injective (action U) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action U).comp N.subtype) (A.subgroupOf N)) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hjmap : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (pointSylow T v) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP]
  have hm : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (U : Set H) := by
    intro hc
    apply p.thompson_moves
    rw [←hjmap]
    rintro _ ⟨a,ha,rfl⟩ z hz
    exact congrArg H.subtype (hc ha ⟨z,c.orbit_le_join hz⟩ hz)
  let : (I.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le I.le_normalizer (inf_le_right.trans c.escaping.normalizes))
  have hK : (I.subgroupOf H).IsCComponent := c.escaping.component.subgroupOf_of_le
    le_sup_left (sup_le c.escaping.le_centralizer inf_le_right)
  have hKP : I.subgroupOf H ⊔ (P : Subgroup H) = ⊤ := by
    rw [hP',←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hq := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple c.join_sqtk
    P (I.subgroupOf H) U hK hKP c.reduced.quotient_pCore_eq_bot hm
  let := hq
  refine ⟨hq,component_le_offenderSubgroup P (I.subgroupOf H) U hKP
    c.reduced.quotient_pCore_eq_bot hm,?_,isFFModule_of_thompson_movement P U hm,
    action_faithful U,?_⟩
  · rw [←hP']
    exact commutator_thompson_eq P (I.subgroupOf H) U hKP c.reduced.quotient_pCore_eq_bot hm
  · exact quasisimple_source_conclusion_of_thompson_movement c.join_sqtk P
      (I.subgroupOf H) U hK hKP c.reduced.quotient_pCore_eq_bot hm

/-- Proved action facts passed to the independent model analysis. In
particular the B.5.1 conclusion belongs to this exact centralizer quotient. -/
structure ActionFacts (c : Context D t v I) : Prop where
  prepared : Prepared D v I
  small_nontrivial : letI := c.reduced.normal
    (L.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I)) ≠ ⊥
  small_local : let H := pointJoin T v I
    letI := c.reduced.normal
    let K := I.subgroupOf H
    let q := actionMk (internalModule D v I)
    let B := ((L.subgroupOf H).map q).subgroupOf (K.map q)
    B < ⊤ ∧ ∃ R : Sylow 2 K,
      (R : Subgroup K) = ((T : Subgroup G).subgroupOf H).subgroupOf K ∧
      B ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K))
  solvable_kernel : letI := c.reduced.normal
    Group.IsSolvable ((actionMk (internalModule D v I)).subgroupMap
      (I.subgroupOf (pointJoin T v I))).ker
  classification : let H := pointJoin T v I
    let U := internalModule D v I
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf H).map (actionMk U)
    let N := offenderSubgroup (action U)
    IsQuasisimple A ∧ A ≤ N ∧
      ⁅A,(elementaryAbelianMaxJ ((pointSylow T v).subgroupOf H)).map (actionMk U)⁆ = A ∧
      IsFFModule (V := Additive U) (action U) ∧ Function.Injective (action U) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action U).comp N.subtype) (A.subgroupOf N))

/-- The supplied geometric preparation discharges all the action and
local-component inputs to the next source inspection. -/
theorem Context.actionFacts (c : Context D t v I) (p : Prepared D v I) : ActionFacts c :=
  ⟨p,(c.small_image_strict p.centralizer_le).1,c.small_image_local p.centralizer_le,
    c.action_kernel_solvable p.centralizer_le,c.ff_action p⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
