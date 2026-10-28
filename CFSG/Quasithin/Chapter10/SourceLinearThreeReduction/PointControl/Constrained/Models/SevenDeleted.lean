module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankTwoReduction
public import Theory.SpecificGroups.Alternating.SevenPerfectSylow
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Excluding the deleted-permutation A₇ containing action

The source marking identifies the offender subgroup of the central section
with S₇ and its component with A₇. Intersecting the original point Sylow
with the two normal offender subgroups retains normalization of the actual
smaller image. A proper perfect subgroup normalized by a full Sylow of S₇
is A₅ or a point-stabilizer A₆. The original quotient's three-rank bound
excludes A₆, and the original non-A₅ hypothesis excludes the other case.
No full moved-span premise is needed for this exclusion.

The full-span action sieve consequently leaves the exceptional A₇ central
section of dimension four or a binary-linear actor. It retains all six
B.5.1 clauses, every action marking, and the original fixed kernel; the
four-dimensional conclusion is not an assertion about the whole VI.
General preparation, the exceptional A₇ extension and binary-linear
reductions, including the four-natural row, remain with the final assembly
owner qt-d-10-nona5-point-constrained.

Source: Aschbacher–Smith 10.2.9, case (b2), printed pp.751–752,
using the full B.5.1 action marking and the original odd-prime rank bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative MatrixGroups

private def alternatingCoreQuotient {n : ℕ} (hn : 5 ≤ n) :
    (alternatingGroup (Fin n) ⧸ pCore 2 (alternatingGroup (Fin n))) ≃*
      alternatingGroup (Fin n) := by
  let A := alternatingGroup (Fin n)
  have hz : center A = ⊥ := alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simpa using hn)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩
  let : IsQuasisimple A := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : pCore 2 A = ⊥ := bot_unique ((IsQuasisimple.pCore_le_center 2).trans_eq hz)
  exact (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot

private theorem five_quotient_of_seven_sylow
    (B : Subgroup (alternatingGroup (Fin 7))) [Group.IsPerfect B]
    (hne : B ≠ ⊥) (hp : B ≠ ⊤)
    (S : Sylow 2 (Equiv.Perm (Fin 7)))
    (hn : (S : Subgroup (Equiv.Perm (Fin 7))) ≤ normalizer
      (B.map (alternatingGroup (Fin 7)).subtype : Set (Equiv.Perm (Fin 7))))
    (hr : primeRank 3 (B ⧸ pCore 2 B) ≤ 1) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  rcases Theory.SpecificGroups.Alternating.SevenPerfectSylow.five_or_point_six B hne hp S hn
    with he | ⟨i,rfl⟩
  · obtain ⟨e⟩ := he
    exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (alternatingCoreQuotient (by decide))⟩
  · let e := AlternatingSix.SmallIndex.pointEquiv i
    let eQ := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans (alternatingCoreQuotient (by decide))
    rw [primeRank_equiv 3 eQ] at hr
    have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
    omega

/-- Restrict the original Sylow through the normal offender subgroup,
retaining the marked alternating component and smaller normalized subgroup. -/
private theorem five_quotient_of_marked_seven
    {X : Type*} [Group X] [Finite X] (A R : Subgroup X) [R.Normal]
    (hAR : A ≤ R) (E : R ≃* Equiv.Perm (Fin 7))
    (eA : A ≃* alternatingGroup (Fin 7))
    (hE : ∀ a : A, E ⟨a,hAR a.property⟩ = (eA a : Equiv.Perm (Fin 7)))
    (B : Subgroup A) [Group.IsPerfect B] (hne : B ≠ ⊥) (hp : B ≠ ⊤)
    (P : Sylow 2 X)
    (hn : (P : Subgroup X) ≤ normalizer (B.map A.subtype : Set X))
    (hr : primeRank 3 (B ⧸ pCore 2 B) ≤ 1) :
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal R
  let C := B.map eA.toMonoidHom
  let eB : B ≃* C := eA.subgroupMap B
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := eB.toMonoidHom) eB.surjective
  have hCn : C ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective _ eA.injective).mp h)
  have hCp : C ≠ ⊤ := by
    intro h
    apply hp
    apply map_injective (f := eA.toMonoidHom) eA.injective
    exact h.trans (map_top_of_surjective _ eA.surjective).symm
  have he : ((B.map A.subtype).subgroupOf R).map E.toMonoidHom =
      C.map (alternatingGroup (Fin 7)).subtype := by
    ext x
    constructor
    · rintro ⟨r,⟨b,hb,hbr⟩,rfl⟩
      refine ⟨eA b,mem_map_of_mem _ hb,?_⟩
      exact (hE b).symm.trans (congrArg E (Subtype.ext hbr))
    · rintro ⟨a,⟨b,hb,hba⟩,rfl⟩
      subst a
      exact ⟨⟨b,hAR b.property⟩,⟨b,hb,rfl⟩,hE b⟩
  have hnorm : (S : Subgroup R) ≤ normalizer ((B.map A.subtype).subgroupOf R : Set R) := by
    intro s hs b
    have hs' : (s : X) ∈ (P : Subgroup X) := by
      change s ∈ (P : Subgroup X).subgroupOf R
      rwa [←hS]
    exact (mem_normalizer_iff.mp (hn hs')) (b : X)
  have hnorm' : ((S.mapSurjective (f := E.toMonoidHom)
      E.surjective : Sylow 2 (Equiv.Perm (Fin 7))) : Subgroup _) ≤
      normalizer (C.map (alternatingGroup (Fin 7)).subtype : Set (Equiv.Perm (Fin 7))) := by
    change (S : Subgroup R).map E.toMonoidHom ≤ _
    rw [←he]
    exact (map_mono hnorm).trans (((B.map A.subtype).subgroupOf R).le_normalizer_map _)
  let eQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  have hrC : primeRank 3 (C ⧸ pCore 2 C) ≤ 1 := by rwa [←primeRank_equiv 3 eQ]
  obtain ⟨e⟩ := five_quotient_of_seven_sylow C hCn hCp
    (S.mapSurjective E.surjective) hnorm' hrC
  exact ⟨eQ.trans e⟩

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
private theorem small_image_offender_geometry (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ (B : Subgroup (A.subgroupOf N)) (P : Sylow 2 N),
      Group.IsPerfect B ∧ B ≠ ⊥ ∧ B ≠ ⊤ ∧
      (P : Subgroup N) ≤ normalizer (B.map (A.subgroupOf N).subtype : Set N) ∧
      primeRank 3 (B ⧸ pCore 2 B) ≤ 1 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L)) := by
  let H := pointJoin T v I
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  let q := actionMk U
  let A := (I.subgroupOf H).map q
  let N := offenderSubgroup (action U)
  let C := A.subgroupOf N
  let B₀ := (L.subgroupOf H).map q
  let B := B₀.subgroupOf A
  have hAN : A ≤ N := a.classification.2.1
  have hBA : B₀ ≤ A := map_mono (comap_mono c.escaping.strict.le)
  let j : A ≃* C := (subgroupOfEquivOfLe hAN).symm
  let B' := B.map j.toMonoidHom
  let b : B ≃* B' := j.subgroupMap B
  obtain ⟨eB⟩ := c.small_local_quotient a
  obtain ⟨hp,R,_,hl⟩ := a.small_local
  let : Group.IsPerfect B := by
    let := hl.perfect
    let S := R.mapSurjective (q.subgroupMap_surjective (I.subgroupOf H))
    let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup A) from le_sup_left)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  have hnB : B ≠ ⊥ := by
    intro hz
    apply a.small_nontrivial
    have h := congrArg (map A.subtype) hz
    change B₀ = ⊥
    change (B₀.subgroupOf A).map A.subtype = (⊥ : Subgroup A).map A.subtype at h
    simpa only [map_subgroupOf_eq_of_le hBA,Subgroup.map_bot] using h
  have hnB' : B' ≠ ⊥ := fun h => hnB ((map_eq_bot_iff_of_injective _ j.injective).mp h)
  have hpB' : B' ≠ ⊤ := by
    intro h
    apply hp.ne
    apply map_injective (f := j.toMonoidHom) j.injective
    exact h.trans (map_top_of_surjective _ j.surjective).symm
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hPL : (P : Subgroup H) ≤ normalizer (L.subgroupOf H : Set H) := by
    rw [hP']
    intro p hp l
    exact (mem_normalizer_iff.mp (c.escaping.sylow_normalizes hp)) (l : G)
  let PQ := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hQB : (PQ : Subgroup (ActionQuotient U)) ≤ normalizer (B₀ : Set _) :=
    (map_mono hPL).trans ((L.subgroupOf H).le_normalizer_map q)
  let : N.Normal := offenderSubgroup_normal (action U)
  obtain ⟨PN,hPN⟩ := PQ.exists_subgroupOf_eq_of_normal N
  have hB' : B'.map C.subtype = B₀.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact hz
    · intro hx
      exact ⟨j ⟨x,hBA hx⟩,mem_map_of_mem j.toMonoidHom hx,rfl⟩
  have hn : (PN : Subgroup N) ≤ normalizer (B'.map C.subtype : Set N) := by
    rw [hB']
    intro p hp x
    have hp' : (p : ActionQuotient U) ∈ (PQ : Subgroup _) := by
      change p ∈ (PQ : Subgroup (ActionQuotient U)).subgroupOf N
      rwa [←hPN]
    exact (mem_normalizer_iff.mp (hQB hp')) (x : ActionQuotient U)
  let eQ := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans eB
  have hr : primeRank 3 (B' ⧸ pCore 2 B') ≤ 1 := by
    rw [primeRank_equiv 3 eQ]
    exact Selection.ModuleChoice.component_quotient_odd_rank_le_one D
      (fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)) 3 Nat.prime_three (by decide)
  exact ⟨B',PN,inferInstance,hnB',hpB',hn,hr,⟨eQ⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual point action cannot have the deleted-permutation A₇ section.
Both full-Sylow restrictions and the original two-core quotient are supplied
by the context; no span, model-normalizer, or central-kernel premise is added. -/
theorem Context.no_deletedSeven_source_section (c : Context D t v I) (a : ActionFacts c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∀ (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N)),
      ¬ Nonempty (MarkedActionEquiv s.action (offenderSubgroup s.action) (A.subgroupOf N)
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  let C := A.subgroupOf N
  obtain ⟨B,P,hperfect,hne,hproper,hn,hr,⟨eQ⟩⟩ := small_image_offender_geometry c a
  let := hperfect
  dsimp only
  intro s ⟨E⟩
  let R := offenderSubgroup s.action
  let : R.Normal := offenderSubgroup_normal s.action
  obtain ⟨e⟩ := five_quotient_of_marked_seven C R E.contained E.action.groupEquiv
    E.subgroupEquiv E.compatible B hne hproper P hn hr
  exact c.nonA5 ⟨eQ.symm.trans e⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The surviving marked A₇ action is exceptional of degree four; every
other action has a genuine binary linear actor. The full source conclusion
and all its original action markings remain available. -/
theorem Context.binary_or_exceptionalSeven_action_of_moved_le
    (c : Context D t v I) (a : ActionFacts c)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
      BinaryOrSevenAction h.sectionData ∧
      ((Nonempty ((A.subgroupOf N) ≃* alternatingGroup (Fin 7)) ∧
          Module.finrank (ZMod 2)
            (h.sectionData.space.toSubmodule ⧸ h.sectionData.central.toSubmodule) = 4) ∨
        ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty ((A.subgroupOf N) ≃* SL(d,ZMod 2))) := by
  let := c.reduced.normal
  let := c.reduced.elementary
  obtain ⟨h,hs⟩ := c.binary_or_seven_action_of_moved_le a hspan
  refine ⟨h,hs,?_⟩
  cases hs with
  | sevenFour _ _ e hd => exact Or.inl ⟨⟨e⟩,hd⟩
  | sevenDeleted _ _ E => exact (c.no_deletedSeven_source_section a h.sectionData ⟨E⟩).elim
  | linear d hd _ _ E => exact Or.inr ⟨d,hd,⟨E.groupEquiv⟩⟩
  | orthogonalSix _ _ E => exact Or.inr ⟨4,Or.inl rfl,⟨(E.groupEquiv.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
      (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩⟩
  | symmetricEight _ _ E => exact Or.inr ⟨4,Or.inl rfl,⟨(E.subgroupEquiv.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
      (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩⟩
  | exteriorFive _ _ E _ => exact Or.inr ⟨5,Or.inr rfl,⟨E⟩⟩
  | naturalDual d hd E => exact Or.inr ⟨d,hd,⟨E.some.groupEquiv⟩⟩
  | repeatedNatural d r hd _ _ E => exact Or.inr ⟨d,hd,⟨E.some.groupEquiv⟩⟩

/-- Outside the exceptional degree-four section, the literal full-span
FF action forces the original SL₃(2) quotient. -/
theorem Context.binaryThree_or_exceptionalSeven_of_moved_le
    (c : Context D t v I) (a : ActionFacts c)
    (hspan : ⁅D.fullModule,L⁆ ≤ orbitModule D v I) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    let N := offenderSubgroup (action (internalModule D v I))
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) ∨
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
          ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N),
        BinaryOrSevenAction h.sectionData ∧
        Nonempty (A ≃* alternatingGroup (Fin 7)) ∧
        Module.finrank (ZMod 2)
          (h.sectionData.space.toSubmodule ⧸ h.sectionData.central.toSubmodule) = 4 := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
  let N := offenderSubgroup (action (internalModule D v I))
  let e : A ≃* A.subgroupOf N := (subgroupOfEquivOfLe a.classification.2.1).symm
  obtain ⟨h,hs,hseven | ⟨d,hd,hlinear⟩⟩ := c.binary_or_exceptionalSeven_action_of_moved_le a hspan
  · exact Or.inr ⟨h,hs,⟨e.trans hseven.1.some⟩,hseven.2⟩
  · exact Or.inl (c.binary_three_quotient_of_binary_containing a hd (e.trans hlinear.some))

end CFSG.Quasithin.Chapter10.PointControl.Constrained
