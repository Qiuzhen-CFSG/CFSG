module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryTransvection
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The normal-closure image of the odd transvection action

For P = <E^I>, the established kernel-commutator bound makes the action
kernel central modulo O₂(P). Passing through that central cover proves
O₂(P*) = O₂(P)* on the literal action on W/<z>. Images of conjugate spans
identify P* with the closure of the moving elementary actor.

The endpoint lines meet in <z>. An element of the moving actor in
O₂(P*) therefore has displacement in both endpoint lines and is trivial.
Consequently the nontrivial elementary actor of order at most four embeds
in P*/O₂(P*), with the quotient map unchanged.

This proves the core-image comparison and surviving actor used in 6.1.19.
It does not assert O₂(P*) = 1: that requires a further argument on W/<z>,
whereas the earlier core theorem controls U/Z_S. That argument, the
component and amalgam analysis, initial naturalness and unconditional
6.1.27 remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

open Subgroup Theory.GroupTheory
open scoped commutatorElement
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem core_image_of_central_mod_core
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (hk : ⁅(⊤ : Subgroup A), f.ker⁆ ≤ pCore 2 A) :
    (pCore 2 A).map f = pCore 2 B := by
  let Q := pCore 2 A
  let N := Q.map f
  let : N.Normal := Normal.map inferInstance f hf
  let q := QuotientGroup.mk' Q
  let b := QuotientGroup.mk' N
  let a := QuotientGroup.map Q N f (le_comap_map f Q)
  have ha : Function.Surjective a :=
    QuotientGroup.map_surjective_of_surjective Q N f
      ((QuotientGroup.mk'_surjective N).comp hf) (le_comap_map f Q)
  have hcentral : f.ker.map q ≤ center (A ⧸ Q) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [← map_top_of_surjective q (QuotientGroup.mk'_surjective Q),
      ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [commutator_comm]
  have hak : a.ker ≤ center (A ⧸ Q) := by
    rw [QuotientGroup.ker_map]
    change ((Q.map f).comap f).map q ≤ _
    rw [comap_map_eq, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact hcentral
  have hc : pCore 2 (B ⧸ N) = ⊥ := by
    have he := a.map_pCore_of_central_kernel (p := 2) ha hak
    rw [pCore_quotient_pCore_eq_bot, Subgroup.map_bot] at he
    exact he.symm
  apply le_antisymm
  · exact le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩
  have hm : (pCore 2 B).map b ≤ pCore 2 (B ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance b (QuotientGroup.mk'_surjective N),pCore_isPGroup.map b⟩
  have he : (pCore 2 B).map b = ⊥ := bot_unique (hc ▸ hm)
  simpa only [b,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he

private theorem relative_core_image
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (I P : Subgroup G) (hPI : P ≤ I) (ρ : I →* A)
    (hc : ⁅P,ρ.ker.map I.subtype⁆ ≤ P.pCoreIn 2) :
    ((P.pCoreIn 2).subgroupOf I).map ρ = ((P.subgroupOf I).map ρ).pCoreIn 2 := by
  let f := ρ.comp (inclusion hPI)
  have hk : ⁅(⊤ : Subgroup P),f.ker⁆ ≤ pCore 2 P := by
    apply (map_le_map_iff_of_injective P.subtype_injective).mp
    rw [map_commutator, ← MonoidHom.range_eq_map,range_subtype]
    apply le_trans (commutator_mono le_rfl ?_) hc
    rintro _ ⟨x,hx,rfl⟩
    exact mem_map_of_mem I.subtype (show inclusion hPI x ∈ ρ.ker from hx)
  have hfr : ⁅(⊤ : Subgroup P),f.rangeRestrict.ker⁆ ≤ pCore 2 P := by
    simpa only [MonoidHom.ker_rangeRestrict] using hk
  have hm := core_image_of_central_mod_core f.rangeRestrict f.rangeRestrict_surjective hfr
  have hmap := congrArg (map f.range.subtype) hm
  have he : f.range = (P.subgroupOf I).map ρ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext i
    constructor
    · rintro ⟨p,rfl⟩; exact p.property
    · intro hi; exact ⟨⟨i,hi⟩,rfl⟩
  have hleft : ((pCore 2 P).map f.rangeRestrict).map f.range.subtype =
      ((P.pCoreIn 2).subgroupOf I).map ρ := by
    rw [map_map]
    change (pCore 2 P).map (ρ.comp (inclusion hPI)) = _
    rw [← map_map]
    congr 1
    apply map_injective I.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le ((pCoreIn_le 2 P).trans hPI)]
    rfl
  rw [hleft] at hmap
  exact hmap.trans (congrArg (fun D : Subgroup A => D.pCoreIn 2) he)


private theorem span_image
    {G A : Type*} [Group G] [Group A]
    (I E : Subgroup G) (hEI : E ≤ I) (ρ : I →* A) :
    ((conjugateSpanBy E I).subgroupOf I).map ρ =
      conjugateSpanBy ((E.subgroupOf I).map ρ) ρ.range := by
  have he : (conjugateSpanBy E I).subgroupOf I =
      conjugateSpanBy (E.subgroupOf I) ⊤ := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hEI),
      map_conjugateSpanBy,map_subgroupOf_eq_of_le hEI,
      ← MonoidHom.range_eq_map,range_subtype]
  rw [he,map_conjugateSpanBy,←MonoidHom.range_eq_map]

private theorem moving_image_disjoint_core
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    (I E W Z Z' D : Subgroup G) (hEI : E ≤ I)
    (hIZ : I ≤ normalizer (Z : Set G))
    (hID : I ≤ normalizer (D : Set G)) (hDZ : D ≤ Z)
    (hinter : Z ⊓ Z' = D)
    (ρ : I →* A)
    (hker : ρ.ker = (commutatorPreimage I W D).subgroupOf I)
    (hcore : (((conjugateSpanBy E I).pCoreIn 2).subgroupOf I).map ρ =
      (((conjugateSpanBy E I).subgroupOf I).map ρ).pCoreIn 2)
    (hcentral : ⁅I.pCoreIn 2,W⁆ ≤ Z)
    (hdisp : ⁅E,W⁆ ≤ Z') :
    ((E.subgroupOf I).map ρ) ⊓
      (((conjugateSpanBy E I).subgroupOf I).map ρ).pCoreIn 2 = ⊥ := by
  apply bot_unique
  rintro y ⟨⟨e,he,rfl⟩,hy⟩
  rw [←hcore] at hy
  obtain ⟨q,hq,heq⟩ := hy
  have hqcore : (q : G) ∈ I.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (conjugateSpanBy_le_self hEI)
      (le_normalizer_conjugateSpanBy E I) hq
  have hdiff : e / q ∈ ρ.ker := by
    change ρ (e / q) = 1
    rw [map_div,heq,div_self']
  rw [hker] at hdiff
  have hdiffZ : (e : G) / (q : G) ∈ commutatorPreimage I W Z := by
    apply (le_commutatorPreimage (commutatorPreimage_le I W D) ?_) hdiff
    exact (commutator_commutatorPreimage_le I W D hID).trans hDZ
  have hqZ : (q : G) ∈ commutatorPreimage I W Z :=
    le_commutatorPreimage (pCoreIn_le 2 I) hcentral hqcore
  have heZ : (e : G) ∈ commutatorPreimage I W Z := by
    simpa only [div_mul_cancel] using (commutatorPreimage I W Z).mul_mem hdiffZ hqZ
  have heK : e ∈ ρ.ker := by
    rw [hker]
    apply (mem_commutatorPreimage_iff I W D hID (e : G)).mpr
    · refine ⟨e.property,fun w hw => ?_⟩
      rw [←hinter]
      exact ⟨(mem_commutatorPreimage_iff I W Z hIZ _).mp heZ |>.2 w hw,
        hdisp (commutator_mem_commutator he hw)⟩
  exact MonoidHom.mem_ker.mp heK

private theorem reduced_actor_injective
    {A : Type*} [Group A] [Finite A] (J B : Subgroup A) (hBJ : B ≤ J)
    (hd : B ⊓ J.pCoreIn 2 = ⊥) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion hBJ)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxQ : inclusion hBJ x ∈ pCore 2 J := (QuotientGroup.eq_one_iff _).mp hx
  have hxB : (x : A) ∈ B ⊓ J.pCoreIn 2 :=
    ⟨x.property,mem_map_of_mem J.subtype hxQ⟩
  rw [hd,mem_bot] at hxB
  exact Subtype.ext hxB

open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)

/-- The normal closure on the involution quotient has exactly the image of
its original two-core, and the moving elementary actor is disjoint from it. -/
theorem exists_involution_closure_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy (ZS (T : Subgroup G) L R) (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let Z' := (ZS (T : Subgroup G) L R).map (MulAut.conj d.representative).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : ((zpowers z).subgroupOf W).Normal),
      letI := hN
      ∃ ρ : I →* MulAut (W ⧸ (zpowers z).subgroupOf W),
        (∀ i : I, ∀ w : W,
          ρ i (QuotientGroup.mk' ((zpowers z).subgroupOf W) w) =
            QuotientGroup.mk' ((zpowers z).subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
        IsElementaryAbelian 2 (W ⧸ (zpowers z).subgroupOf W) ∧
        let A := (E.subgroupOf I).map ρ
        let J := (P.subgroupOf I).map ρ
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A ∧ Nat.card A ≤ 4 ∧
        commutatorAction A (W ⧸ (zpowers z).subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' ((zpowers z).subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' ((zpowers z).subgroupOf W))) = 2 ∧
        commutatorAction₂ A (W ⧸ (zpowers z).subgroupOf W) = ⊥ ∧
        ρ.ker = (commutatorPreimage I W (zpowers z)).subgroupOf I ∧
        J = conjugateSpanBy A ρ.range ∧
        ((P.pCoreIn 2).subgroupOf I).map ρ = J.pCoreIn 2 ∧
        A ⊓ J.pCoreIn 2 = ⊥ ∧
        ∃ hAJ : A ≤ J,
          Function.Injective ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion hAJ)) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hEW,hIW,hN,ρ,hρ,hquot,hAelem,hApos,hAupper,
      hdisp,hline,hquad,hker,_,hPK⟩ :=
    d.exists_involution_transvection_action h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let U := Escape.U (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let W := U ⊓ conjugateSpanBy Z (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
  let P := conjugateSpanBy E I
  let := hN
  let q := QuotientGroup.mk' ((zpowers z).subgroupOf W)
  have hZcard : Nat.card Z' = 4 := by
    rw [card_map_of_injective (MulAut.conj d.representative).injective]
    have hh := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [hn] at hh
    exact hh
  have hz' : zpowers z ≤ Z' := by
    have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers z ⊓ Z') Z' bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,inf_comm (zpowers z) Z',inf_relIndex_left] at hi
    have hc : (zpowers z).relIndex Z' = 2 := by
      have hh := hline
      rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hZW] at hh
      exact hh
    rw [hc] at hi
    have hmeet : Nat.card (zpowers z ⊓ Z' : Subgroup G) = 2 := by
      rw [inf_comm] at hi
      omega
    have he : zpowers z ⊓ Z' = zpowers z := eq_of_le_of_card_ge inf_le_left (by
      rw [hmeet,Nat.card_zpowers,ho])
    exact he.symm.le.trans inf_le_right
  have hinter : Z ⊓ Z' = zpowers z := by
    have hc := (d.parameter_and_intersection h hnat hE hs hNS).2
    exact (eq_of_le_of_card_ge (le_inf (zpowers_le.mpr hz) hz') (by
      rw [hc,Nat.card_zpowers,ho])).symm
  have hcore := relative_core_image I P (conjugateSpanBy_le_self hEI) ρ hPK
  have hIZ : I ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  have hID : I ≤ Subgroup.normalizer (zpowers z : Set G) :=
    (centralizer_le (zpowers_le.mpr hz)).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm : ⁅E,W⁆ ≤ Z' := by
    have hh : (⁅W,E⁆.subgroupOf W).map q ≤ (Z'.subgroupOf W).map q := by
      rw [←quotient_conjugation_commutatorAction_eq_image I W (zpowers z) E hIW hEI hN ρ hρ]
      exact hdisp.le
    have hk : q.ker ≤ Z'.subgroupOf W := by
      rw [QuotientGroup.ker_mk']; exact subgroupOf_mono W hz'
    have hc : ⁅W,E⁆.subgroupOf W ≤ Z'.subgroupOf W := by
      have hh' := map_le_iff_le_comap.mp hh
      rwa [comap_map_eq_self hk] at hh'
    have hm := map_mono (f := W.subtype) hc
    rw [map_subgroupOf_eq_of_le (le_normalizer_iff_commutator_le_left.mp (hEI.trans hIW)),
      map_subgroupOf_eq_of_le hZW,commutator_comm] at hm
    exact hm
  have hcentral : ⁅I.pCoreIn 2,W⁆ ≤ Z := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans (natural_escape_core h hnat).2
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hEW,hIW,hN,ρ,hρ,hquot,hAelem,hApos,hAupper,
    hdisp,hline,hquad,hker,span_image I E hEI ρ,hcore,?_⟩
  have hd := moving_image_disjoint_core I E W Z Z' (zpowers z) hEI hIZ hID
    (zpowers_le.mpr hz) hinter ρ hker hcore hcentral hcomm
  have hAJ := map_mono (f := ρ) (subgroupOf_mono I (le_conjugateSpanBy E I))
  exact ⟨hd,hAJ,reduced_actor_injective _ _ hAJ hd⟩

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
