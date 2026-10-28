module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightBender
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
-- Internal source-kernel convention; the public theorem exposes no private definition.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
-- Reuse the internal H-star overlap identification within this extension family.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalCartan

/-!
# The exchanged-component exclusion in generic amalgam recognition

In the exchanged E.2.2 row, quotient by the original source kernel,
which is O₂(H). The two components commute there. The Sylow part of
the second component lies in the original overlap core and centralizes
the first component, so it lies in O₂(L₂S). Its order is at least four
in both the linear and Suzuki rows. Pulling this through the literal
quotient gives [O₂(L₂S) : O₂(L₂)] ≥ 4.

Consequently the core-extension bound at most two from 5.2.6 excludes
this row. The actual Bender factor is then the whole residual O²(H).
The Chapter 12 application uses the bound only for perfect prepared pairs
and retains original uniqueness over L. The bound itself, the marked
diagram chief-factor exclusion, and ambient completion recognition remain
source obligations of qt-d-1222-rankone-generic-global. No classification
or global isomorphism is asserted by this conditional elimination.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651, using
E.2.2(1a) and 5.1.10–11 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem centralizing_two_part_le_core (C S : Subgroup X)
    (hp : IsPGroup 2 S) (hn : S ≤ normalizer (C : Set X)) :
    S ⊓ centralizer (C : Set X) ≤ (C ⊔ S).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (hp.to_le inf_le_left) (inf_le_left.trans le_sup_right)
  apply sup_le
  · exact (le_centralizer_iff.mp (show S ⊓ centralizer (C : Set X) ≤
      centralizer (C : Set X) from inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  · exact (le_inf S.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer C))).trans
      inf_normalizer_le_normalizer_inf

private theorem exchanged_model_sylow_card {M C : Subgroup X} {f : ℕ}
    (hm : ExchangedModel M C f) (P : Sylow 2 (sourceImage M C)) : 4 ≤ Nat.card P := by
  rcases hm with ⟨F,_,_,_,hf,hF,e,_⟩ | ⟨m,hm,_,e,_⟩
  · let d := e.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F).symm
    let Q := P.mapSurjective (f := d.toMonoidHom) d.surjective
    have hc : Nat.card P = Nat.card F := by
      calc
        _ = Nat.card Q := Nat.card_congr (P.equivMapOfInjective d.toMonoidHom d.injective).toEquiv
        _ = Nat.card (Multiplicative F) :=
          (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 Q).toEquiv).symm
        _ = Nat.card F := rfl
    rw [hc,hF]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
  · rw [BenderSuzuki.MatrixGroups.suzukiSylow_card (by omega) e P]
    have hh : 2 ≤ 2 ^ (2*m+1) := Nat.le_pow (by omega)
    nlinarith

private theorem paired_core_card (T : Sylow 2 X) {C S : Subgroup X}
    (hqt : IsStronglyQuasithin X) (hC : IsComponent X C)
    (hgen : C ⊔ (T : Subgroup X) = ⊤) (hnot : ¬ C.Normal)
    (hp : IsPGroup 2 S) (hS : S ≤ normalizer (C : Set X))
    (hroot : (T : Subgroup X) ⊓ pResidual 2 X ≤ S)
    (hlarge : ∀ P : Sylow 2 C, 4 ≤ Nat.card P) :
    4 ≤ Nat.card ((C ⊔ S).pCoreIn 2) := by
  rcases ChapterE.Structure.component_normal_or_pair hqt T hC hgen with hn |
    ⟨t,_,hD,hcomm,_,hres,_,_⟩
  · exact (hnot hn.1).elim
  let D := C.map (MulAut.conj (t:X)).toMonoidHom
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal D hD.1
  have hmap : (P : Subgroup D).map D.subtype = (T : Subgroup X) ⊓ D := by
    rw [hP,subgroupOf_map_subtype]
  let e := (MulAut.conj (t:X)).subgroupMap C
  let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hfour : 4 ≤ Nat.card P := by
    have hc := Nat.card_congr (P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv
    exact hc ▸ hlarge Q
  have hu : (T : Subgroup X) ⊓ D ≤ (C ⊔ S).pCoreIn 2 := by
    apply le_trans _ (centralizing_two_part_le_core C S hp hS)
    refine le_inf (le_trans ?_ hroot) ?_
    · exact inf_le_inf_left _ (hres ▸ le_sup_right)
    · exact inf_le_right.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hcomm))
  have hc : Nat.card ((T : Subgroup X) ⊓ D : Subgroup X) = Nat.card P := by
    rw [←hmap,card_map_of_injective D.subtype_injective]
  exact (hc ▸ hfour).trans (Nat.card_le_card_of_injective
    (inclusion hu) (inclusion_injective hu))

/-- The exchanged source row forces a core extension of order at least four. -/
theorem exchanged_source_core_index
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hc : ExchangedClauses (ChapterB.minimalParabolicMax T hP) C T)
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) C f) :
    4 ≤ (C.pCoreIn 2).relIndex
      ((C ⊔ (ChapterB.minimalParabolicMax T hP).pCoreIn 2).pCoreIn 2) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let U := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hJ : J = pCore 2 X := hc.kernel_eq
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk',hJ];exact pCore_isPGroup
  have hs : ¬ Group.IsSolvable X := fun hh => hC.not_isSolvable
    (by let := hh;infer_instance)
  have hi := ChapterE.Structure.source_component_simple_image T hP hs C hC hgen
  change IsSimpleGroup (C.map q) ∧ IsComponent (X ⧸ J) (C.map q) ∧
    ¬ IsMulCommutative (C.map q) ∧ C.map q ⊔ (U : Subgroup (X ⧸ J)) = ⊤ at hi
  have hnot : ¬ C.Normal := by
    intro hn
    let := hn
    obtain ⟨t,_,ht,_⟩ := hc.exchanged_product
    exact ht (mem_normalizer_iff_map_conj_eq.mp
      (show t⁻¹ ∈ normalizer (C : Set X) by rw [normalizer_eq_top];exact mem_top _)).symm
  let : Group.IsSolvable J := by
    rw [hJ]
    let := pCore_isPGroup (p := 2) (G := X) |>.isNilpotent
    infer_instance
  have hnot' : ¬ (C.map q).Normal := fun hn => hnot (cComponent_normal_of_quotient_normal hC J hn)
  have hqt : IsStronglyQuasithin (X ⧸ J) :=
    (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
      hX T hP hs).stronglyQuasithin
  have hS : (M.pCoreIn 2).map q ≤ normalizer (C.map q : Set (X ⧸ J)) :=
    (map_mono (Prime.exchanged_core_normalizes hX T hP hC hgen hc hm)).trans
      (C.le_normalizer_map q)
  obtain ⟨P,hP'⟩ := T.exists_subgroupOf_eq_of_subnormal (pResidual 2 X)
    (Subgroup.Normal.isSubnormal inferInstance)
  have hmapP : (P : Subgroup (pResidual 2 X)).map (pResidual 2 X).subtype =
      (T : Subgroup X) ⊓ pResidual 2 X := by rw [hP',subgroupOf_map_subtype]
  have him := T.map_image_eq_inf _ _ P hmapP inf_le_left q
  rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective J)] at him
  have hroot : (U : Subgroup (X ⧸ J)) ⊓ pResidual 2 (X ⧸ J) ≤ (M.pCoreIn 2).map q := by
    change (T : Subgroup X).map q ⊓ pResidual 2 (X ⧸ J) ≤ _
    rw [←him]
    exact map_mono (Prime.exchanged_residual_sylow_le_core hX T hP hC hgen hc hm)
  have hfour := paired_core_card U hqt hi.2.1 hi.2.2.2 hnot'
    ((isPGroup_pCoreIn 2 M).map q) hS hroot (exchanged_model_sylow_card hm)
  have hQ : q.ker ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes hk
    (by rw [QuotientGroup.ker_mk'];exact M.normalCore_le) le_normalizer_of_normal
  have hQ' : q.ker ≤ (C ⊔ M.pCoreIn 2).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hk (hQ.trans le_sup_right) le_normalizer_of_normal
  have hCq : C.pCoreIn 2 ≤ q.ker := by
    rw [QuotientGroup.ker_mk',hJ]
    exact pCoreIn_le_of_subnormal 2 hC.subnormal
  have hcore : ((C ⊔ M.pCoreIn 2).pCoreIn 2).map q =
      (C.map q ⊔ (M.pCoreIn 2).map q).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup q hk,Subgroup.map_sup]
  have hb : (C.pCoreIn 2).map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hCq
  have hidx : Nat.card ((C.map q ⊔ (M.pCoreIn 2).map q).pCoreIn 2) =
      q.ker.relIndex ((C ⊔ M.pCoreIn 2).pCoreIn 2) := by
    rw [←hcore,←relIndex_bot_left,←hb,
      relIndex_map_map,sup_eq_right.mpr hCq,sup_eq_left.mpr hQ']
  exact (hidx ▸ hfour).trans (relIndex_le_of_le_left (L := (C ⊔ M.pCoreIn 2).pCoreIn 2) hCq Subgroup.index_ne_zero_of_finite)

/-- The lower bound on the literal H-star factor and S = O₂(N_G(L) ∩ H). -/
theorem exchanged_rightFactor_core_index
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H : Subgroup G} {n f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf H = ⊤)
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    4 ≤ ((C.map H.subtype).pCoreIn 2).relIndex
      (((C.map H.subtype) ⊔ sourceS L H).pCoreIn 2) := by
  let U := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  have hP := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hpar
  have hmax := hstar_maximal_eq_overlap hH hP
  have hc' : ExchangedClauses (ChapterB.minimalParabolicMax U hP) C U := hmax ▸ hc
  have hm' : ExchangedModel (ChapterB.minimalParabolicMax U hP) C f := hmax ▸ hm
  have hh := exchanged_source_core_index (Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1)
    U hP hC hgen hc' hm'
  rw [hmax] at hh
  have hS : (M.pCoreIn 2).map H.subtype = sourceS L H := by
    rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
    rfl
  have he := relIndex_map_map_of_injective (f := H.subtype)
    (C.pCoreIn 2) ((C ⊔ M.pCoreIn 2).pCoreIn 2) H.subtype_injective
  rw [map_pCoreIn_of_injective 2 C H.subtype H.subtype_injective,
    map_pCoreIn_of_injective 2 (C ⊔ M.pCoreIn 2) H.subtype H.subtype_injective,
    Subgroup.map_sup,hS] at he
  exact he ▸ hh

/-- In the Bender branch, the Green Book core bound rules out the exchanged
component. The surviving original factor is exactly O²(H). The bound is an
explicit recognition premise, to be discharged by this task's source assembly. -/
theorem rankOne_residual_rightFactor_of_core_bound
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : RightRankOneSource T L H)
    (hcore : ∀ R : Subgroup G, RightFactor T L H A B R → Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2) ≤ 2) :
    RightFactor T L H A B (residual H) ∧ Group.IsPerfect (residual H) := by
  obtain ⟨C,f,hC,hqs,hgen,_,hc | hc⟩ := hs
  · have hr := exchanged_source_rightFactor h hH hpar c hN hC hgen hc.1 hc.2
    have hlo := exchanged_rightFactor_core_index h hH hpar hC hgen hc.1 hc.2
    let := hC.perfect
    have hhi := hcore _ hr (Group.IsPerfect.map H.subtype)
    omega
  · have he : C = pResidual 2 H :=
      BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hC
    refine ⟨(single_bender_source_geometry h.sylow_normalizes hH hC hqs hc.1 hc.2).rightFactor
      c h.sylow_normalizes hH hN (Set.mem_singleton _),?_⟩
    let : Group.IsPerfect (pResidual 2 H) := he ▸ hC.perfect
    exact Group.IsPerfect.map H.subtype

/-- The original right-factor dispatcher after the exchanged-component
exclusion. The marked diagram row still needs the source chief-factor argument. -/
theorem residual_rightFactor_or_diagram_of_core_bound
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hcore : ∀ R : Subgroup G, RightFactor T L H A B R → Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2) ≤ 2) :
    (RightFactor T L H A B (residual H) ∧ Group.IsPerfect (residual H)) ∨
      RightDiagramSource T L H := by
  rcases right_source_cases h.qtke h.sylow_normalizes hH hpar with hs | hs
  · exact Or.inl (rankOne_residual_rightFactor_of_core_bound h hH hpar c hN hs hcore)
  · exact Or.inr hs

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
