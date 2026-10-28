module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import Theory.GroupTheory.CComponent.QuasisimpleImage
public import Theory.GroupTheory.CentralProductRadicalAction
public import Theory.GroupTheory.PerfectNormalizerInner
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# The original normal seed lies in the selected constrained component

Modulo the ambient two-core, the selected C-component is ordinary.
Project the original perfect normal seed into that component. Radical
saturation puts the projection's two-core in the original radical, and the
projection commutator calculation places the projection in its normalizer.
It therefore lies in the original local subgroup and normalizes the seed.
Perfect projection and C-component minimality identify it with the seed.
Containment then lifts through the solvable two-core.

Source: Aschbacher--Smith, C.4.5, printed p.152. The proof retains the
selected component and uses no module model or assumed projection lift.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28

private theorem normal_seed_projection_le
    {X : Type*} [Group X] [Finite X] (A B R J : Subgroup X)
    [Group.IsPerfect A] [Group.IsSolvable (MulAut.Outer J)]
    (hAB : A ≤ B) (hBA : B ≤ normalizer (A : Set X))
    (hA : (A.subgroupOf B).IsCComponent) (hJ : IsComponent X J)
    (hR : IsPGroup 2 R) (hRB : R ≤ B)
    (hNR : normalizer (R : Set X) ≤ B)
    (hAR : A ≤ normalizer (R : Set X))
    (hAJ : A ≤ normalizer (J : Set X))
    (hRJ : R ≤ normalizer (J : Set X))
    (hsat : ∀ P : Subgroup X, IsPGroup 2 P → B ≤ normalizer (P : Set X) → P ≤ R)
    (hnc : ¬ A ≤ centralizer (J : Set X)) : A ≤ J := by
  let C := centralizer (J : Set X)
  have hinner := perfect_le_sup_centralizer_of_solvable_outer J A hAJ
  obtain ⟨P,Q,hPJ,hQC,hP,hQ,hAP,hPA,hN⟩ :=
    exists_perfect_projections_of_central_product J C A
      (le_centralizer_iff.mp le_rfl) hinner
  let := hP
  have hBP : B ⊓ normalizer (J : Set X) ≤ normalizer (P : Set X) :=
    hN _ inf_le_right (inf_le_right.trans (normalizer_le_normalizer_centralizer J))
      (inf_le_left.trans hBA)
  have hcore : P.pCoreIn 2 ≤ R := hJ.stabilizer_saturation hsat _
    ((pCoreIn_le 2 P).trans hPJ) (isPGroup_pCoreIn 2 P)
    (hBP.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hRP : R ≤ normalizer (P : Set X) := (le_inf hRB hRJ).trans hBP
  have hcomm : ⁅P,R⁆ ≤ P.pCoreIn 2 :=
    perfect_projection_radical_commutator A P C R
      (hPJ.trans (le_centralizer_iff.mp le_rfl))
      (hAP.trans (sup_le le_sup_left (hQC.trans le_sup_right)))
      (hPA.trans (sup_le le_sup_left (hQC.trans le_sup_right)))
      (hRB.trans hBA) hAR hRP (hRJ.trans (normalizer_le_normalizer_centralizer J)) hR
  have hPB : P ≤ B := (le_normalizer_iff_commutator_le_right.mpr
    (hcomm.trans hcore)).trans hNR
  have hPL : P ≤ A := perfect_projection_le_of_normalizes P Q A
    (hPJ.trans (le_centralizer_iff.mp hQC)) hAP hPA (hPB.trans hBA)
  have hne : P ≠ ⊥ := by
    intro he
    exact hnc ((show A ≤ Q by simpa only [he,bot_sup_eq] using hAP).trans hQC)
  have hAPn : A ≤ normalizer (P : Set X) :=
    hN A hAJ (hAJ.trans (normalizer_le_normalizer_centralizer J)) A.le_normalizer
  have hsub : (P.subgroupOf B).IsSubnormal := by
    have hp : ((P.subgroupOf B).subgroupOf (A.subgroupOf B)).Normal := by
      apply normal_subgroupOf_of_le_normalizer
      intro a ha p
      exact hAPn ha (p : X)
    exact IsSubnormal.trans (subgroupOf_mono B hPL) hp.isSubnormal hA.subnormal
  have hperfect : Group.IsPerfect (P.subgroupOf B) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hPB).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPB).symm.surjective
  have hbot : P.subgroupOf B ≠ ⊥ := by
    intro he
    have hh := congrArg (map B.subtype) he
    exact hne (by simpa only [map_subgroupOf_eq_of_le hPB,Subgroup.map_bot] using hh)
  have hmin := hA.minimal (P.subgroupOf B) (subgroupOf_mono B hPL) hbot hperfect hsub
  intro a ha
  exact hPJ (hmin (show (⟨a,hAB ha⟩ : B) ∈ A.subgroupOf B from ha))

variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- C.4.5 placement for a normal original seed, on the same selected
constrained component. -/
theorem constrained_normal_seed_le
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J) : L.subgroupOf H ≤ J := by
  let A := L.subgroupOf H
  let B := M.subgroupOf H
  let S := R.subgroupOf H
  let O := pCore 2 H
  let q := QuotientGroup.mk' O
  let Ab := A.map q
  let Bb := B.map q
  let Sb := S.map q
  let Jb := J.map q
  have hRH := h.radical_le.trans h.local_le
  have hML : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn
  have hs : conjugateSpanBy L M = L := le_antisymm
    (conjugateSpanBy_le le_rfl hML) (le_conjugateSpanBy _ _)
  have hAB : A ≤ B := subgroupOf_mono H h.component_le
  have hBA : B ≤ normalizer (A : Set H) := by
    intro b hb a
    exact hML hb (a : G)
  have hA : (A.subgroupOf B).IsCComponent := by
    let e := subgroupOfEquivOfLe h.local_le
    have hh := h.component.map_equiv e.symm
    have he : (L.subgroupOf M).map e.symm.toMonoidHom = A.subgroupOf B := by
      ext b
      constructor
      · rintro ⟨l,hl,rfl⟩; exact hl
      · intro hl; exact ⟨e b,hl,e.symm_apply_apply b⟩
    exact he ▸ hh
  let : Group.IsPerfect (A.subgroupOf B) := hA.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAB).toMonoidHom)
    (subgroupOfEquivOfLe hAB).surjective
  let : Group.IsPerfect Ab := Group.IsPerfect.map q
  have hOS : O ≤ S := by
    intro x hx
    exact h.ambient_core_le_radical (mem_map_of_mem H.subtype hx)
  have hker : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let : Group.IsNilpotent O := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable O := inferInstance
  have hNR : normalizer (S : Set H) ≤ B := by
    rw [←subgroupOf_normalizer_eq hRH]
    intro x hx
    exact h.normalizer_le ⟨x.property,hx⟩
  have hAR : A ≤ normalizer (S : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical (hs.symm ▸ ha) (r : G)
  have hAJ : A ≤ normalizer (J : Set H) := by
    simpa only [hs] using h.constrained_span_normalizes_intrinsic J hJ hq
  have hRJ : S ≤ normalizer (J : Set H) := by
    have hh := h.constrained_radical_normalizes J hJ hq hout hf
    have he : (J.map H.subtype).subgroupOf H = J :=
      J.comap_map_eq_self_of_injective H.subtype_injective
    rw [←he,←subgroupOf_normalizer_eq (map_subtype_le J)]
    intro r hr
    exact hh hr
  have hAbB : Ab ≤ Bb := map_mono hAB
  have hBAb : Bb ≤ normalizer (Ab : Set (H ⧸ O)) :=
    (map_mono hBA).trans (A.le_normalizer_map q)
  have hSbB : Sb ≤ Bb := map_mono (subgroupOf_mono H h.radical_le)
  have hAbS : Ab ≤ normalizer (Sb : Set (H ⧸ O)) :=
    (map_mono hAR).trans (S.le_normalizer_map q)
  have hAbJ : Ab ≤ normalizer (Jb : Set (H ⧸ O)) :=
    (map_mono hAJ).trans (J.le_normalizer_map q)
  have hSbJ : Sb ≤ normalizer (Jb : Set (H ⧸ O)) :=
    (map_mono hRJ).trans (J.le_normalizer_map q)
  have hcomapS : Sb.comap q = S := comap_map_eq_self (by
    simpa only [q,QuotientGroup.ker_mk'] using hOS)
  have hNbS : normalizer (Sb : Set (H ⧸ O)) ≤ Bb := by
    have hh : (normalizer (Sb : Set (H ⧸ O))).comap q ≤ B := by
      rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective O),hcomapS]
      exact hNR
    have hm := map_mono (f := q) hh
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)] at hm
  have hsat : ∀ P : Subgroup (H ⧸ O), IsPGroup 2 P →
      Bb ≤ normalizer (P : Set (H ⧸ O)) → P ≤ Sb := by
    intro P hp hBP
    have hnP : B ≤ normalizer (P.comap q : Set H) :=
      (map_le_iff_le_comap.mp hBP).trans (P.le_normalizer_comap q)
    have hPR := le_of_normalizer_le_normalizer_of_pCore_normalizer_le S (P.comap q)
      h.isRadical.isPGroup (hp.comap_of_ker_isPGroup q hker)
      h.isRadical.2.le (hNR.trans hnP)
    have hm := map_mono (f := q) hPR
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)] at hm
  have hJb : IsComponent (H ⧸ O) Jb := hJ.isComponent_map_of_twoCore_killed hq q
    (QuotientGroup.mk'_surjective O)
    (by simpa only [q,QuotientGroup.ker_mk'] using pCoreIn_le_of_subnormal 2 hJ.subnormal)
    (hJ.map_quotient_ne_bot O)
  let : IsQuasisimple Jb := hJb.2
  let : Group.IsSolvable (MulAut.Outer Jb) :=
    ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable h.sqtk
      ((ChapterA.Section02.IsSectionOf.of_surjective (q.subgroupMap J)
        (q.subgroupMap_surjective J)).trans (.subgroup J))
  have hAb : (Ab.subgroupOf Bb).IsCComponent := by
    let f := q.subgroupMap B
    have hk : IsPGroup 2 f.ker := by
      rw [ker_subgroupMap]
      exact hker.comap_subtype
    let : Group.IsNilpotent f.ker := hk.isNilpotent
    let : Group.IsSolvable f.ker := inferInstance
    have hh := cComponent_map_of_solvable_ker hA f (q.subgroupMap_surjective B)
    have he : (A.subgroupOf B).map f = Ab.subgroupOf Bb := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact mem_map_of_mem q hy
      · rintro ⟨y,hy,he⟩
        exact ⟨⟨y,hAB hy⟩,hy,Subtype.ext he⟩
    exact he ▸ hh
  have hnc : ¬ Ab ≤ centralizer (Jb : Set (H ⧸ O)) := by
    intro hc
    have he : ⁅A,J⁆.map q = ⊥ := by
      rw [map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr hc
    have hh : ⁅A,J⁆ ≤ O := by
      simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using he
    apply h.span_commutator_not_le_ambient_core J hout
    simpa only [hs] using hh
  have hle := normal_seed_projection_le Ab Bb Sb Jb hAbB hBAb hAb hJb
    (h.radical_isTwoGroup.comap_subtype.map q) hSbB hNbS hAbS hAbJ hSbJ hsat hnc
  exact perfect_le_cComponent_of_map_le hJ O hle

end CFSG.Quasithin.ChapterC.HypothesisC28
