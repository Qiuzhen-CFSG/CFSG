module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Marking
public import Theory.GroupTheory.Recognition.QuasithinM23.SylowPlanes
public import Theory.GroupTheory.FrattiniConjugatorAdjustment
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# The two original root planes and their normalizers

The compatible linear amalgam transports its whole middle Sylow group to
UT₃(F). In the exceptional branch the original two-cores are its distinct
root planes. Their intrinsic classification identifies the original
normalizer intersections, and a Frattini adjustment yields M = L(M ∩ J).

Source: Aschbacher–Smith, 5.2.11(2),(3), printed pp.653–654
(`refs/quasithin.pdf`). Both orientations of the supplied amalgam comparison
are retained; no ambient recognition or generation premise is added.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
theorem Preparation.linear_sourceS_unitriangular
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
 :
    Nonempty (U F ≃* sourceS L H) := by
  let C := ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)
  let hf := d.hypothesisF11 h hH.1.1.2
  have hSC : sourceS L H ≤ C := le_sup_right
  obtain ⟨a⟩ : Nonempty (C ≃* Matrix.PSL3.LinearThree.borel F) := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact ⟨(MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle⟩
    · exact ⟨(MulEquiv.subgroupCongr (ChapterF.Source.lemma_F_1_3_6 hf)).symm.trans e.middle⟩
  obtain ⟨P,hP⟩ := hf.sylow_commonBorel
  have hPS : (P : Subgroup C) = (sourceS L H).subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSC]
  let R := (Matrix.PSL3.LinearThree.unipotentSylow F hm hF).subtype
    (Matrix.PSL3.LinearThree.unipotent_le_borel F)
  let : (R : Subgroup (Matrix.PSL3.LinearThree.borel F)).Normal := by
    change ((Matrix.PSL3.LinearThree.unipotent F).subgroupOf
      (Matrix.PSL3.LinearThree.borel F)).Normal
    rw [←Matrix.PSL3.CartanActions.BorelQuotient.twoCore_eq F hF]
    infer_instance
  let := Sylow.unique_of_normal R (inferInstance : R.Normal)
  have hSR : ((sourceS L H).subgroupOf C).map a.toMonoidHom =
      (Matrix.PSL3.LinearThree.unipotent F).subgroupOf (Matrix.PSL3.LinearThree.borel F) := by
    rw [←hPS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim (P.mapSurjective a.surjective) R)
  let b : sourceS L H ≃* Matrix.PSL3.LinearThree.unipotent F :=
    (subgroupOfEquivOfLe hSC).symm.trans
      ((((sourceS L H).subgroupOf C).equivMapOfInjective a.toMonoidHom a.injective).trans
        ((MulEquiv.subgroupCongr hSR).trans
          (subgroupOfEquivOfLe (Matrix.PSL3.LinearThree.unipotent_le_borel F))))
  exact ⟨((projectiveEquiv F).trans
    (MulEquiv.subgroupCongr (Matrix.PSL3.LinearThree.projective_range F))).trans b.symm⟩

omit [Finite G] in
private theorem core_le_sourceS
    {T : Sylow 2 G} {L H A B : Subgroup G}
    (d : Preparation T L H A B (residual H))
    (i : Fin 2) : (![L,residual H] i).pCoreIn 2 ≤ sourceS L H := by
  obtain ⟨P,hP⟩ := d.sylow i
  have hle : (pCore 2 (![L,residual H] i)).map (![L,residual H] i).subtype ≤
      (P : Subgroup (![L,residual H] i)).map (![L,residual H] i).subtype :=
    map_mono ((pCore_isPGroup (p := 2)).le_sylow_of_normal P)
  exact hle.trans (hP.le.trans inf_le_left)

theorem Preparation.linear_exceptional_sylow_planes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    L.pCoreIn 2 ⊔ J.pCoreIn 2 = sourceS L H ∧
      L.pCoreIn 2 ⊓ J.pCoreIn 2 = (center (sourceS L H)).map (sourceS L H).subtype ∧
      Nat.card (L.pCoreIn 2 ⊓ J.pCoreIn 2 : Subgroup G) = 4 ∧
      (∀ E : Subgroup G, IsElementaryAbelian 2 E → E ≤ sourceS L H →
        Nat.card E = 16 → E = L.pCoreIn 2 ∨ E = J.pCoreIn 2) ∧
      normalizer (sourceS L H : Set G) ⊓ J = normalizer (L : Set G) ⊓ J ∧
      normalizer (sourceS L H : Set G) ⊓ normalizer (L : Set G) =
        J ⊓ normalizer (L : Set G) := by
  have hTH := hH.1.1.2
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  obtain ⟨_,hn,hF4,hcores,hMcore,hNV,hCV,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp F hm hF he hnonmax
  obtain ⟨hTJ,hHJ,hmax,hNJ,hNU,hCU,_⟩ :=
    d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  have hc := (d.linear_overcomponent_core h hTH hp F hm hF he hJ.1 hKJ.le).1
  have haV : IsElementaryAbelian 2 (pCore 2 L) := (hcores 0).1
  have haK : IsElementaryAbelian 2 (pCore 2 (residual H)) := (hcores 1).1
  let := haV
  let := haK
  let : IsElementaryAbelian 2 (L.pCoreIn 2) := haV.map L.subtype
  let : IsElementaryAbelian 2 (J.pCoreIn 2) := by
    rw [hc]
    exact haK.map (residual H).subtype
  have hV : L.pCoreIn 2 ≤ sourceS L H := core_le_sourceS d 0
  have hU : J.pCoreIn 2 ≤ sourceS L H := hc ▸ core_le_sourceS d 1
  have hcV : Nat.card (L.pCoreIn 2) = Nat.card F ^ 2 := by
    change Nat.card ((pCore 2 L).map L.subtype) = _
    rw [card_map_of_injective L.subtype_injective,hF4]
    exact (hcores 0).2
  have hcU : Nat.card (J.pCoreIn 2) = Nat.card F ^ 2 := by
    rw [hc]
    change Nat.card ((pCore 2 (residual H)).map (residual H).subtype) = _
    rw [card_map_of_injective (residual H).subtype_injective,hF4]
    exact (hcores 1).2
  have hne : L.pCoreIn 2 ≠ J.pCoreIn 2 := by
    intro heq
    have hJM : J = normalizer (L : Set G) := by rw [←hNU,←heq,hNV]
    exact d.right_outside (hJM ▸ hKJ.le)
  obtain ⟨e⟩ := d.linear_sourceS_unitriangular h hH F hm hF he
  obtain ⟨hgen,hcenter,hcard,hall⟩ :=
    QuasithinM23.unitriangular_two_planes F (sourceS L H) e
      (L.pCoreIn 2) (J.pCoreIn 2) hV hU hcV hcU hne
  have hnormal := QuasithinM23.unitriangular_plane_normalizers F (sourceS L H) e
      (L.pCoreIn 2) (J.pCoreIn 2) hV hU hcV hcU hne
  rw [hNU,hNV] at hnormal
  rw [hF4] at hcard hall
  have hnormal' := QuasithinM23.unitriangular_plane_normalizers F (sourceS L H) e
      (J.pCoreIn 2) (L.pCoreIn 2) hU hV hcU hcV hne.symm
  rw [hNU,hNV] at hnormal'
  exact ⟨hgen,hcenter,hcard,hall,hnormal,hnormal'⟩

/-- The source Frattini factorization of the original left maximal local. -/
theorem Preparation.linear_exceptional_left_generation
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J) :
    L ⊔ (normalizer (L : Set G) ⊓ J) = normalizer (L : Set G) := by
  obtain ⟨_,_,_,_,_,hN⟩ := d.linear_exceptional_sylow_planes h hH hp F hm hF he hJ hKJ
  have hSL : sourceS L H ≤ L := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0
  have hs := d.sylow 0
  change ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = sourceS L H ⊓ L at hs
  obtain ⟨P,hP⟩ := hs
  rw [inf_eq_left.mpr hSL] at hP
  apply le_antisymm (sup_le L.le_normalizer inf_le_left)
  intro x hx
  obtain ⟨l,hl⟩ := exists_frattini_adjustment L P x hx
  rw [hP] at hl
  have hlM : (l : G)*x ∈ normalizer (L : Set G) :=
    (normalizer (L : Set G)).mul_mem (L.le_normalizer l.property) hx
  have hlJ : (l : G)*x ∈ J := (hN.le ⟨hl,hlM⟩).1
  have hm := (L ⊔ (normalizer (L : Set G) ⊓ J)).mul_mem
    (mem_sup_left (L.inv_mem l.property)) (mem_sup_right ⟨hlM,hlJ⟩)
  simpa only [inv_mul_cancel_left] using hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
