module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.PositiveCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SevenCover
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The exceptional A₇ action on the actual moved subgroup

Perfectness makes [VI,I] commutator-generated. Vanishing of the dual first
cohomology of the exceptional four-space kills its central covering kernel,
so the literal subgroup [VI,I] has dimension four. Reducedness shows that
it has exactly the same action centralizer as VI, even when VI retains
additional fixed vectors. Its faithful four-space action makes the whole
actor A₇.

Apply C.1.24 to this actual normal elementary moved subgroup. The original
Baumann characteristic-subgroup obstruction forces a block and identifies
I/O₂(I) with A₇. The opposite cubic then excludes this row for every original
natural cover, including a positive original fixed kernel. Neither the
original moved factor nor the entire orbit is identified with [VI,I].

The containing-action sieve and binary branches are assembled in
Models.BinaryPositive; general quiet preparation and the retained four-natural
row remain with qt-d-10-nona5-point-constrained.
Source: Aschbacher–Smith 10.2.9, printed pp.751–752, C.1.24, pp.130–131,
and the cohomology calculation I.1.5–6, p.408.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative

private theorem four_section_moved
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) [Group.IsPerfect A]
    (s : MovedSection ρ A) (e : A ≃* alternatingGroup (Fin 7))
    (hi : IsIrreducible (s.action.comp A.subtype))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    s.central.toSubmodule = ⊥ ∧ Module.finrank (ZMod 2) s.space.toSubmodule = 4 := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) s.space.toSubmodule :=
    (s.space.toRepresentation.comp A.subtype).comp e.symm.toMonoidHom
  let τ : Representation (ZMod 2) (alternatingGroup (Fin 7))
      (s.space.toSubmodule ⧸ s.central.toSubmodule) :=
    (s.action.comp A.subtype).comp e.symm.toMonoidHom
  let := hi
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr hi
  let p : σ.IntertwiningMap τ := {
    toLinearMap := s.central.toSubmodule.mkQ
    isIntertwining' := by intros; rfl }
  have hp : OneCohomology.IsCover p := by
    refine ⟨Submodule.mkQ_surjective _,?_,?_⟩
    · intro w hw g
      have hw' : w ∈ s.central.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hw
      rw [s.central_eq] at hw'
      exact hw' (e.symm g)
    · let C := (Coinvariants.ker σ).map s.space.toSubmodule.subtype
      have hC : s.space.toSubmodule ≤ C := by
        rw [s.space_eq]
        change subspaceCommutator ρ ⊤ A ≤ C
        rw [← subspaceCommutator_idempotent_of_perfect ρ A]
        apply Submodule.span_le.mpr
        rintro _ ⟨a,ha,v,hv,rfl⟩
        let w : s.space.toSubmodule := ⟨v,s.space_eq.symm ▸ hv⟩
        refine ⟨σ (e ⟨a,ha⟩) w - w,Coinvariants.sub_mem_ker _ _,?_⟩
        change ρ (e.symm (e ⟨a,ha⟩)).val v - v = ρ a v - v
        rw [e.symm_apply_apply]
      apply top_unique
      intro w _
      obtain ⟨z,hz,he⟩ := hC w.property
      exact (Subtype.ext he : z = w) ▸ hz
  have hinj := BinaryAlternatingSevenControl.four_cover_injective hd p hp
  have hz : s.central.toSubmodule = ⊥ := by
    have hh := LinearMap.ker_eq_bot.mpr hinj
    change LinearMap.ker s.central.toSubmodule.mkQ = ⊥ at hh
    rwa [Submodule.ker_mkQ] at hh
  exact ⟨hz, (LinearEquiv.ofBijective p.toLinearMap ⟨hinj,hp.1⟩).finrank_eq.trans hd⟩

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The literal moved subgroup has dimension four in the exceptional A₇ row,
without asserting that the whole orbit is moved. -/
theorem Context.moved_four_dimensional_of_seven_section (c : Context D t v I)
    (af : ActionFacts c) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let U := internalModule D v I
    let K := I.subgroupOf (pointJoin T v I)
    letI : IsElementaryAbelian 2 (⁅U,K⁆ : Subgroup (pointJoin T v I)) :=
      IsElementaryAbelian.of_le (commutator_le_left U K)
    let A := K.map (actionMk U)
    ∀ (N : Subgroup (ActionQuotient U)) (_hAN : A ≤ N)
      (s : MovedSection ((action U).comp N.subtype) (A.subgroupOf N))
      (_e : (A.subgroupOf N) ≃* alternatingGroup (Fin 7)),
      IsIrreducible (s.action.comp (A.subgroupOf N).subtype) →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 →
      s.central.toSubmodule = ⊥ ∧
        Module.finrank (ZMod 2) (Additive (⁅U,K⁆ : Subgroup (pointJoin T v I))) = 4 := by
  let := c.reduced.normal
  let := c.reduced.elementary
  let U := internalModule D v I
  let K := I.subgroupOf (pointJoin T v I)
  let A := K.map (actionMk U)
  let : IsElementaryAbelian 2 (⁅U,K⁆ : Subgroup (pointJoin T v I)) :=
    IsElementaryAbelian.of_le (commutator_le_left U K)
  dsimp only
  intro N hAN s e hi hd
  let : IsQuasisimple A := af.classification.1
  let : Group.IsPerfect (A.subgroupOf N) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hAN).symm.toMonoidHom)
      (subgroupOfEquivOfLe hAN).symm.surjective
  obtain ⟨hz,hs⟩ := four_section_moved _ _ s e hi hd
  have he : s.space.toSubmodule = subspaceCommutator (action U) ⊤ A := by
    rw [s.space_eq]
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · rintro _ ⟨a,ha,v,hv,rfl⟩
      exact Submodule.subset_span ⟨a.val,ha,v,hv,rfl⟩
    · rintro _ ⟨a,ha,v,hv,rfl⟩
      exact Submodule.subset_span ⟨⟨a,hAN ha⟩,ha,v,hv,rfl⟩
  let f := (NormalElementaryQuotient.movedEquiv U (actionMk U)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K).trans
      (LinearEquiv.ofEq _ _ he.symm)
  exact ⟨hz,f.finrank_eq.trans hs⟩
end CFSG.Quasithin.Chapter10.PointControl.Constrained

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem point_baumann_eq {v : G} (hvT : v ∈ (T : Subgroup G))
    (hv2 : v ^ 2 = 1)
    (hJP : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      elementaryAbelianMaxJ (T : Subgroup G)) :
    ChapterB.baumann ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) =
      ChapterB.baumann (T : Subgroup G) := by
  let : IsElementaryAbelian 2 (zpowers v) := IsElementaryAbelian.zpowers_of_pow_eq_one hv2
  have hvC : v ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro j hj
    have hJle : elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ≤
        (T : Subgroup G) ⊓ centralizer ({v} : Set G) := sSup_le fun _ hA => hA.1
    have hjP := hJle (hJP.symm ▸ hj)
    exact (mem_centralizer_singleton_iff.mp hjP.2)
  have hvZ := elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G) (zpowers v)
    (zpowers_le.mpr hvT) (zpowers_le.mpr hvC) (mem_zpowers v)
  have hBC : ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr ((show b ∈ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G) from hb.2) v hvZ).symm
  exact baumann_eq_of_intermediate _ _ (le_inf inf_le_left hBC) inf_le_left

private theorem no_point_characteristic
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (I H : Subgroup G) (hLI : L ≤ I) (hIH : I ≤ H) (hout : ¬ I ≤ D.maximalLocal)
    (P : Sylow 2 H)
    (hb : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G))
    (R : Subgroup (ChapterB.baumann (P : Subgroup H)))
    (hchar : R.Characteristic) (hne : R ≠ ⊥)
    (hn : (R.map (ChapterB.baumann (P : Subgroup H)).subtype).Normal) : False := by
  let B := ChapterB.baumann (P : Subgroup H)
  let B0 := ChapterB.baumann (T : Subgroup G)
  let e : B ≃* B0 := (B.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hb)
  let R0 := R.map e.toMonoidHom
  let : R0.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp hchar (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  have he : R0.map B0.subtype = (R.map B.subtype).map H.subtype := by
    rw [map_map,map_map]
    rfl
  have hN : I ≤ normalizer (R0.map B0.subtype : Set G) := by
    rw [he]
    have hN := (R.map B.subtype).le_normalizer_map H.subtype
    have hn' : normalizer (R.map B.subtype : Set H) = ⊤ := @normalizer_eq_top _ _ _ hn
    rw [hn',←MonoidHom.range_eq_map,range_subtype] at hN
    exact hIH.trans hN
  have hz := source_overgroup_characteristic_baumann_eq_bot D I hLI hout R0 hN
  exact hne ((map_eq_bot_iff_of_injective R e.injective).mp hz)


/-- A four-dimensional moved A₇ action reconstructs the actual component head.
The original orbit may retain additional fixed vectors. -/
theorem Context.block_and_quotient_of_four_moved_action (c : Context D t v I)
    (af : ActionFacts c)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        alternatingGroup (Fin 7))
    (hd : letI := c.reduced.normal
      letI := c.reduced.elementary
      let U := internalModule D v I
      let K := I.subgroupOf (pointJoin T v I)
      letI : IsElementaryAbelian 2 (⁅U,K⁆ : Subgroup (pointJoin T v I)) :=
        IsElementaryAbelian.of_le (commutator_le_left U K)
      Module.finrank (ZMod 2) (Additive (⁅U,K⁆ : Subgroup (pointJoin T v I))) = 4) :
    ChapterC.IsBlock (I.subgroupOf (pointJoin T v I)) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) := by
  let H := pointJoin T v I
  let K := I.subgroupOf H
  let U := internalModule D v I
  let := c.reduced.normal
  let := c.reduced.elementary
  have hHX : H ≤ centralizer ({v} : Set G) := sup_le c.escaping.le_centralizer inf_le_right
  have hK : K.IsCComponent := c.escaping.component.subgroupOf_of_le le_sup_left hHX
  let : K.Normal := normal_subgroupOf_of_le_normalizer (hHX.trans c.escaping.normalizes)
  let d : K ≃* I := subgroupOfEquivOfLe le_sup_left
  obtain ⟨P,hP⟩ := c.join_sylow
  have hP' : (P : Subgroup H) = (pointSylow T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show pointSylow T v ≤ H from le_sup_right)]
  have hKP : K ⊔ (P : Subgroup H) = ⊤ := by
    rw [hP',←subgroupOf_sup (show I ≤ H from le_sup_left)
      (show pointSylow T v ≤ H from le_sup_right)]
    exact subgroupOf_self H
  have hprod : ∀ g : H, ∃ k ∈ K, ∃ s ∈ (P : Subgroup H), k*s=g := by
    intro g
    exact mem_sup_of_normal_left.mp (hKP.symm ▸ mem_top g)
  let := hK.perfect
  have hpK : IsPPerfect 2 K := by
    intro R hn hp
    let := hn
    let : Group.IsNilpotent (K ⧸ R) := hp.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := K)]
    exact solvableResidual_le_of_solvable_quotient R
  have hres : pResidual 2 H = K :=
    pResidual_eq_of_isPPerfect_sup K (P : Subgroup H) hpK P.isPGroup' hKP
  let W := ⁅U,K⁆
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U K)
  have hCW : centralizer (W : Set H) = centralizer (U : Set H) := by
    change centralizer ((⁅U,K⁆ : Subgroup H) : Set H) = _
    rw [←hres]
    exact c.reduced.centralizer_moved_eq U
  let ρ := NormalElementaryQuotient.representation W (actionMk U)
    (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans hCW.symm)
  have hfaith : Function.Injective ρ := NormalElementaryQuotient.representation_injective W
    (actionMk U) (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans hCW.symm)
  let A := K.map (actionMk U)
  let : A.Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hAtop : A = ⊤ := BinaryAlternatingSevenControl.normal_alternatingSeven_eq_top
    ρ hfaith hd A e
  let dQ : ActionQuotient U ≃* alternatingGroup (Fin 7) :=
    (topEquiv.symm.trans (MulEquiv.subgroupCongr hAtop.symm)).trans e
  let q := dQ.toMonoidHom.comp (actionMk U)
  have hq : Function.Surjective q := dQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = centralizer (W : Set H) := by
    rw [hCW]
    ext x
    change dQ (actionMk U x) = 1 ↔ _
    rw [dQ.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hKq : K.map q = ⊤ := by
    change K.map (dQ.toMonoidHom.comp (actionMk U)) = ⊤
    rw [←map_map,show K.map (actionMk U) = ⊤ from hAtop]
    exact map_top_of_surjective _ dQ.surjective
  let : IsQuasisimple (I ⧸ pCore 2 I) := source_a5_point_a7_head_quasisimple D
    c.point_involution I c.escaping.le_centralizer c.escaping.component c.reduced e
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm
  have hCOrig : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal :=
    (Subgroup.centralizer_le_normalizer _).trans c.escaping.moved_normalizer
  have hv : v ∈ D.fullModule := partner_le_fullModule D c.escaping.t_mem c.escaping.v_mem
  have ho := source_a5_point_centralizer_oddCore_eq_bot D hv c.escaping.v_ne
    (c.escaping.crossed c.escaping.v_mem) hCOrig
  have hfI : generalizedFitting I = pCore 2 I := by
    let dX := subgroupOfEquivOfLe c.escaping.le_centralizer
    rcases c.escaping.component.component_or_generalizedFitting_eq_pCore ho with h | h
    · let := h.2
      exact (c.not_quasisimple (IsQuasisimple.of_mulEquiv dX)).elim
    · have hh := congrArg (Subgroup.map dX.toMonoidHom) h
      rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hfK : generalizedFitting K = pCore 2 K := by
    have hh := congrArg (Subgroup.map d.symm.toMonoidHom) hfI
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hh
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hvT := D.fullModule_le_sylow hu hv
  have hv2 : v ^ 2 = 1 := by simpa only [c.point_involution] using pow_orderOf_eq_one v
  have hb : (ChapterB.baumann (P : Subgroup H)).map H.subtype = ChapterB.baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (P : Subgroup H)
    change (ChapterB.baumann (P : Subgroup H)).map H.subtype =
      ChapterB.baumann ((P : Subgroup H).map H.subtype) at hh
    rw [hP] at hh
    exact hh.trans (point_baumann_eq hvT hv2 af.prepared.thompson_eq)
  have hm : ⁅W,K⁆ = W := commutator_isPPerfect_idempotent K U hpK
    (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  have hne : W ≠ ⊥ := by
    intro hz
    have hc : Nat.card W = 16 := by
      change Nat.card (Additive W) = 16
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
      norm_num
    rw [hz,card_bot] at hc
    omega
  have hblock : ChapterC.IsBlock K :=
    (ChapterC.RankOne.SevenSource.normal_characteristic_or_block_of_exceptional_seven
      K W hK c.characteristic_two hfK P hprod q hq hk hKq hd (hm.symm ▸ hne)).resolve_left (by
        rintro ⟨R,hchar,hneR,hn⟩
        exact no_point_characteristic D I H c.escaping.strict.le le_sup_left c.escaping.escapes
          P hb R hchar hneR hn)
  let eqK := (ChapterC.RankOne.SevenSource.coreQuotientEquiv_of_full_moved K W hblock hne hm q hk).trans
    ((MulEquiv.subgroupCongr hKq).trans topEquiv)
  exact ⟨hblock,⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans eqK⟩⟩

/-- The original component quotient marking, retained from the reconstructed block. -/
theorem Context.alternatingSeven_quotient_of_four_moved_action (c : Context D t v I)
    (af : ActionFacts c)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        alternatingGroup (Fin 7))
    (hd : letI := c.reduced.normal
      letI := c.reduced.elementary
      let U := internalModule D v I
      let K := I.subgroupOf (pointJoin T v I)
      letI : IsElementaryAbelian 2 (⁅U,K⁆ : Subgroup (pointJoin T v I)) :=
        IsElementaryAbelian.of_le (commutator_le_left U K)
      Module.finrank (ZMod 2) (Additive (⁅U,K⁆ : Subgroup (pointJoin T v I))) = 4) :
    Nonempty ((I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :=
  (c.block_and_quotient_of_four_moved_action af e hd).2
end CFSG.Quasithin.Chapter10.PointControl.Constrained

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- Every original natural cover excludes the exceptional four-dimensional
A₇ source section, with both original and containing fixed kernels retained. -/
theorem Context.no_seven_four_section_of_binaryThreeNatural (c : Context D t v I)
    (hmodel : Selection.BinaryThreeNatural D) :
    letI := c.reduced.normal
    letI := c.reduced.elementary
    let A := (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))
    ∀ (N : Subgroup (ActionQuotient (internalModule D v I))) (_hAN : A ≤ N)
      (s : MovedSection ((action (internalModule D v I)).comp N.subtype) (A.subgroupOf N))
      (_E : (A.subgroupOf N) ≃* alternatingGroup (Fin 7)),
      IsIrreducible (s.action.comp (A.subgroupOf N).subtype) →
      Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 → False := by
  let := c.reduced.normal
  let := c.reduced.elementary
  dsimp only
  intro N hAN s E hi hd
  have af := c.actionFacts_of_binaryThreeNatural hmodel
  have hm := (c.moved_four_dimensional_of_seven_section af N hAN s E hi hd).2
  obtain ⟨e⟩ := c.alternatingSeven_quotient_of_four_moved_action af
    ((subgroupOfEquivOfLe hAN).symm.trans E) hm
  exact c.no_alternatingSeven_of_binaryThreeNatural hmodel e
end CFSG.Quasithin.Chapter10.PointControl.Constrained
