module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Quotients
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity

/-!
# Normal containing components in the original flag normalizers

The original seed witnesses a nontrivial two-core in LᵢT. Together with
its two-perfectness and quasisimple quotient, this puts every source Lᵢ
in L(G,T). Source 1.2.4 inside the actual two-local Gᵢ then constructs
a unique containing C-component, normal relative to Gᵢ.

For i≥3 the smaller subgroup induces the full linear group on Vᵢ.
If the containing component has quasisimple two-core quotient, equal
nontrivial action images and two-core normalization through T force equality.
Models applies this to discharge the n=5 hyperplane component.

Source: Aschbacher--Smith, opening and i=3,4 argument of12.9.3,
printed p.858 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- Both literal residual conventions give two-perfect subgroups. -/
theorem Li_twoPerfect (F : InvariantFlag T V n) (i : ℕ) : IsPPerfect 2 (F.Li L i) := by
  by_cases hm : n = 5 ∧ (i = 2 ∨ i = 3)
  · rw [Li, if_pos hm]
    let N := L ⊓ F.Gi i
    let e := (solvableResidual N).equivMapOfInjective N.subtype N.subtype_injective
    let : Group.IsPerfect ((solvableResidual N).map N.subtype) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    intro R hn hp
    let := hn
    by_contra hne
    let : Nontrivial (((solvableResidual N).map N.subtype) ⧸ R) :=
      QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  · rw [Li, if_neg hm]
    exact isPPerfect_embedded_pResidual 2 _

/-- T normalizes the original Lᵢ, including the exceptional solvable residuals. -/
theorem sylow_normalizes_Li {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (i : ℕ) :
    (T : Subgroup G) ≤ normalizer (F.Li L i : Set G) := by
  have ht : (T : Subgroup G) ≤ normalizer ((L ⊓ F.Gi i : Subgroup G) : Set G) :=
    (le_inf (h.sylow_normalizes earlier.structural)
      ((F.invariant i).trans (F.Gi i).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  dsimp only [Li]
  split <;> exact ht.trans (normalizer_le_normalizer_characteristic_image _ _)

/-- V witnesses the nontrivial core in the local-family definition. -/
theorem seed_le_local_core {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n) (i : ℕ) :
    V ≤ F.Ri L i := by
  let := h.chosen.elementary
  have ht : (T : Subgroup G) ≤ normalizer (V : Set G) := F.last ▸ F.invariant n
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (h.chosen.le_sylow.trans le_sup_right)
    (sup_le (((F.Li_le L i).trans inf_le_left).trans h.chosen.normalizes) ht)

/-- All six source residuals really belong to L(G,T). -/
theorem Li_mem_local {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (i : ℕ) (hi : ComponentIndex n i) :
    F.Li L i ∈ Chapter1.L G (T : Subgroup G) := by
  let := h.chosen.elementary
  let B := F.Li L i
  let J := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf J
  let : IsQuasisimple (B ⧸ pCore 2 B) := Li_core_quasisimple F h.naturalMarking i hi
  have ht : (⊤ : Subgroup B).IsCComponent :=
    isCComponent_top_of_isPPerfect_of_quasisimple_quotient
      (pCore 2 B) pCore_isPGroup (Li_twoPerfect F i)
  let e : B ≃* A := (subgroupOfEquivOfLe (show B ≤ J from le_sup_left)).symm
  have htA : (⊤ : Subgroup A).IsCComponent := by
    have he : (⊤ : Subgroup B).map e.toMonoidHom = ⊤ :=
      (MonoidHom.range_eq_map e.toMonoidHom).symm.trans
        (MonoidHom.range_eq_top.mpr e.surjective)
    exact he ▸ ht.map_equiv e
  have hn : A.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer (sylow_normalizes_Li h earlier F i))
  have hA : A.IsCComponent := by
    simpa only [← MonoidHom.range_eq_map, range_subtype] using htA.map_subtype hn.isSubnormal
  refine ⟨hA,⟨T.subtype le_sup_right,?_⟩,?_⟩
  · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
  · intro he
    exact h.chosen.ne_bot (bot_unique (he ▸ seed_le_local_core h F i))

/-- Every nonzero flag member defines an actual two-local normalizer. -/
theorem Gi_twoLocal {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (i : ℕ) (hi : 1 ≤ i) : IsTwoLocal (F.Gi i) := by
  let := h.chosen.elementary
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by have := h.rank; omega)
    rw [he,Subgroup.card_bot] at hc
    norm_num at hc
  exact ⟨F.Vi i,fun he => hp (bot_unique (he ▸ F.monotone hi)),
    (IsElementaryAbelian.isPGroup 2 V).to_le (F.le_seed i),rfl⟩

/-- Source 1.2.4 applied inside the literal N_G(Vᵢ), as at the start of 12.9.3. -/
theorem exists_unique_normal_local_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (i : ℕ) (hi : ComponentIndex n i) :
    ∃! D : Subgroup G, D ∈ Chapter1.cComponentsIn (F.Gi i) ∧
      F.Li L i ≤ D ∧ (D.subgroupOf (F.Gi i)).Normal := by
  let H := F.Gi i
  have hT : (T : Subgroup G) ≤ H := F.invariant i
  have hL : F.Li L i ≤ H := (F.Li_le L i).trans inf_le_right
  have hlocal : (F.Li L i).subgroupOf H ∈ Chapter1.L H (T.subtype hT) := by
    simpa only [Sylow.coe_subtype] using
      (Chapter1.mem_LIn_iff_subgroupOf hT hL).mp ⟨hL,Li_mem_local h earlier F i hi⟩
  have hnorm : (T.subtype hT : Subgroup H) ≤
      normalizer ((F.Li L i).subgroupOf H : Set H) := by
    intro t ht b
    exact sylow_normalizes_Li h earlier F i ht (b : G)
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (h.source.simpleQTKE.twoLocal_sqtk (Gi_twoLocal h F i (by
      rcases hi with ⟨_,hlo,_⟩ | ⟨_,he⟩ <;> omega))) (pCore 2 H) pCore_isPGroup
  obtain ⟨D,⟨hD,hLD,hn⟩,hu⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ (T.subtype hT) hlocal hnorm
  have he : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective _
  refine ⟨D.map H.subtype,⟨⟨map_subtype_le _,he.symm ▸ hD⟩,?_,he.symm ▸ hn⟩,?_⟩
  · simpa only [map_subgroupOf_eq_of_le hL] using map_mono (f := H.subtype) hLD
  · intro J hJ
    have hj := hu (J.subgroupOf H) ⟨hJ.1.2,comap_mono hJ.2.1,hJ.2.2⟩
    exact (map_subgroupOf_eq_of_le (show J ≤ H from hJ.1.1)).symm.trans
      (congrArg (map H.subtype) hj)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]
/-- A quasisimple containing component at a flag space of dimension at
least three is the original residual. Both subgroups induce the whole
linear group; the component two-core normalizes the residual through T. -/
theorem component_eq_of_quasisimple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (i : ℕ) (hi : 3 ≤ i) (hin : i ≤ n)
    (D : Subgroup G) (hD : D ∈ Chapter1.cComponentsIn (F.Gi i))
    (hLD : F.Li L i ≤ D) (hnD : (D.subgroupOf (F.Gi i)).Normal)
    (hq : IsQuasisimple (D ⧸ pCore 2 D)) : D = F.Li L i := by
  let H := F.Gi i
  let B := (F.Li L i).subgroupOf H
  let C := D.subgroupOf H
  let f := flagLinearAction F i
  have hLH : F.Li L i ≤ H := (F.Li_le L i).trans inf_le_right
  let eC := subgroupOfEquivOfLe hD.1
  let := hq
  let : IsQuasisimple (C ⧸ pCore 2 C) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).symm
  have hb : B.map f = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨l,hl⟩ := Li_flagLinearAction_surjective F h.naturalMarking i hi hin a
    exact mem_map.mpr ⟨⟨l,hLH l.property⟩,l.property,hl⟩
  have hc : C.map f = ⊤ := top_unique (hb.symm ▸ map_mono (comap_mono hLD))
  have hne : C.map f ≠ ⊥ := by
    rw [hc]
    let e := (Module.finBasisOfFinrankEq (ZMod 2) _ (flag_space_finrank F i hin)).equivFun
    let eG := BinaryLinear.SmallParabolicLevi.linearGroupCongr e
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin i) (ZMod 2)) :=
      Atlas.psl_simple_high_rank i hi
    let : IsSimpleGroup (LinearGroup i) := (projectiveEquivLinear (by omega)).symm.isSimpleGroup
    let : IsSimpleGroup (BinaryLinear.GL (space (V := V) (F.Vi i))) := eG.isSimpleGroup
    exact top_ne_bot
  have hn : pCore 2 C ≤ normalizer (B.subgroupOf C : Set C) := by
    intro c hc b
    have hct : (c.val : G) ∈ (T : Subgroup G) := by
      have hpc : c.val ∈ pCore 2 H :=
        pCoreIn_le_of_subnormal 2 hnD.isSubnormal (mem_map_of_mem C.subtype hc)
      exact pCore_isPGroup.le_sylow_of_normal (T.subtype (F.invariant i)) hpc
    exact sylow_normalizes_Li h earlier F i hct (b.val : G)
  have he : B = C := Theory.GroupTheory.IsCComponent.eq_of_image_eq_of_twoCore_normalizes f hD.2
    (comap_mono hLD) (hb.trans hc.symm) hne hn
  have he' := congrArg (map H.subtype) he
  exact (map_subgroupOf_eq_of_le hD.1).symm.trans
    (he'.symm.trans (map_subgroupOf_eq_of_le hLH))

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
