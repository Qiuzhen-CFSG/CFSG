module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFiveSource
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.EarlierModules
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingConstituent
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.AlternatingConstituentRows
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerCatalogue

/-!
# The original A₅ constituent contradiction at the same ambient group

The reduced primitive-kernel witness contains an actual chosen module of a
faithful local component K. Apply only the original 13.3.2(3) premise at G,T,L
and this K, using Hypothesis 13.3.1 inherited from the standing counterexample.
The compatible constituent injection and the commuting cubic then exclude
the same reduced quotient action by the proved B.5 row calculation.

The earlier module premise remains with qt-d-1332-source; final source
assembly is retained by qt-d-1378-source and qt-d-1381-source.
Source: Aschbacher–Smith 13.3.2(3), 13.7.4(1), printed pp.885,937–938.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
universe u
variable {G : Type u} [Group G] [Finite G]

open Stellmacher ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The genuine earlier constituent classification excludes the centralized
primitive A5 kernel on its actual reduced module and quotient action. -/
theorem source_primitive_alternatingFive_false_of_modules_at
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hp : IsPPerfect 2 (J.map H.subtype))
    (hcomm : ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (ha : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)))
    (modules : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  have hJn := (source_primitive_kernel_normal_of_small_model d h hne J hJ hs hJC
    (Or.inl ha)).2
  have hd : 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
    obtain ⟨e⟩ := ha
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hout := source_primitive_kernel_not_le_local_of_three_dvd d h1221 h eL hne
    J hJ hs hJC hd
  obtain ⟨U,hUD,hUU₂,hr,hUne,hUK,hUL,hmin⟩ :=
    source_primitive_component_minimal_tilde_module d h1221 h hU eL hm J hJC hJn hp hout
      hJ hs hcomm
  have hU0 : U ≤ (fixedLayer F).subgroupOf X :=
    hUU₂.trans (comap_mono (source_kernel_mixed_geometry d h hJC hJn hp hcomm).2.2.1)
  have hDR := (source_kernel_tilde_geometry d h hJC hJn hp hcomm).2.2.2.2.2.2.1
  have hKH : K ≤ H := hJC.trans (kernel_le_H (D := F))
  have hXH : X ≤ H := sup_le hKH h.local_le
  have hXn : X ≤ normalizer (K : Set G) := hXH.trans hJn
  let eJ : J ≃* K := J.equivMapOfInjective H.subtype H.subtype_injective
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  let eQ := QuotientGroup.congr (pCore 2 J) (pCore 2 K) eJ (pCore_map_iso 2 eJ)
  obtain ⟨a⟩ := ha
  let aK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) := eQ.symm.trans a
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv aK.symm
  obtain ⟨A,⟨chosen⟩,hAU⟩ := chosen_inside_reduced_overgroup
    (T := T) (show K ≤ X from le_sup_left)
    (show (T : Subgroup G) ≤ X from le_sup_right.trans le_sup_right) hXn hp U hr hUne hUK
  have hmov : ⁅fixedLayer F,K⁆ ≠ ⊥ := by
    intro hz
    have hUB : U.map X.subtype ≠ ⊥ := fun he =>
      hUne ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp he)
    have he : ⁅U.map X.subtype,K⁆ = U.map X.subtype := by
      have hh := congrArg (map X.subtype) hUK
      rw [map_commutator] at hh
      change ⁅U.map X.subtype,(K.subgroupOf X).map X.subtype⁆ = U.map X.subtype at hh
      rwa [map_subgroupOf_eq_of_le (show K ≤ X from le_sup_left)] at hh
    apply hUB
    apply le_bot_iff.mp
    rw [←he]
    exact (commutator_mono ((map_le_iff_le_comap).mpr hU0) le_rfl).trans_eq hz
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  have hf := component_faithful_of_fixedLayer_movement h
    (conjugateSpanBy_elementary_of_commutative V₃ H) J hJ hmov
  have model := modules (Chapter14.Section03.FaithfulSource.hypothesis1331 d.counterexample) K hf ⟨aK⟩ A chosen
  let := hr.normal
  let := hr.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  obtain ⟨f,hf,i,hi,hact⟩ := alternating_constituent_quotient_injection
    (show K ≤ X from le_sup_left) hXn U hr hUne hUK hAU model
  obtain ⟨hEn,hCn,hRp,hcore,hfaith,hn,hquot⟩ :=
    source_kernel_reduced_actor_image h hKH hJn U hr
  let := hCn
  let := hn
  obtain ⟨cover⟩ := source_kernel_reduced_actor_cover d h hKH U hr
  have hCN := source_component_kernel_le_restricted_offender h J hJ hs hJC hJn
    hcomm hout hB U hr hU0 hUne hUK
  obtain ⟨e⟩ := source_primitive_reduced_actor_equiv h J hJC hJn U hr hUne hUK hs
  let aC : C ≃* alternatingGroup (Fin 5) := e.symm.trans a
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv aC.symm
  have hc : Nat.card C = 60 := by
    rw [Nat.card_congr aC.toEquiv,nat_card_alternatingGroup]
    norm_num
  obtain ⟨_,_,hAE,z,hzA,hz3,hfix⟩ := source_kernel_reduced_cubic_image d h eL hJC hJn hp
    hcomm U hr hUne hUL (hUD.trans (subgroupOf_mono X hDR))
  have hwhole : moved ρ C = ⊤ := by
    change subspaceCommutator ρ ⊤ C = ⊤
    rw [← NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (K.subgroupOf X)]
    change AddSubgroup.toZModSubmodule 2 ((⁅U,K.subgroupOf X⁆).subgroupOf U).toAddSubgroup = ⊤
    rw [hUK,subgroupOf_self]
    rfl
  exact OddFFRows.not_ambient_alternatingFive_constituent_of_commuting_cubic ρ
    (show C ≤ E from le_sup_left) hfaith hcore cover hCN hquot hwhole hc f hf i hi hact z
    (by rw [←hz3]; exact pow_orderOf_eq_one z)
    (fun c => (mem_centralizer_iff.mp (hAE hzA)) c ((show C ≤ E from le_sup_left) c.property) |>.symm) hfix

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
