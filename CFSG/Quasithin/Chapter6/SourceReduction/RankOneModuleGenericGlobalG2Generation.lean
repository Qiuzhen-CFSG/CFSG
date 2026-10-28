module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2LocalSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2AmbientOrder
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2AmbientOrder

/-!
# Ambient generation by the original G₂ pair

The fixed-coset argument retains the same marked long and short involutions
as the source two-class catalogue. The all-degree equality S=T extends that
catalogue to every overgroup of L ∨ O²(H). Both full ambient centralizers lie
in the normalizer join, which controls fusion of the two classes. Thompson's
mixed-pair order formula therefore makes the normalizer join all of G.
The literal source normalizer products make L ∨ O²(H) normal there, and
simplicity makes this nontrivial factor join all of G as well.

The original compatible parabolic maps consequently give a faithful completion
in ambient G, with their whole overlap exactly the original common Borel.
This discharges the ambient-generation part of the G₂ recognition route for
every n>1, including field four. It does not construct the exhaustive comparison
or identify this completion with the concrete G₂ model. Those duties and the
original uniqueness input in Preparation remain with the generic-global owner.
The Chapter12 companion applies both results to the literal chosen-module pair.

Source: Aschbacher–Smith F.4.38, F.4.42–44, printed pp.294–296, and
5.3.3–4, p.659 (`refs/quasithin.pdf`). The internal import reuses the existing
Sylow-conjugacy and two-class fusion lemmas within this source family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The actual G₂ normalizer pair and perfect factor pair generate the whole
ambient group, at every original exponent n>1. -/
theorem Preparation.g2_ambient_generation
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      L ⊔ residual H = ⊤ := by
  have hST := d.g2_sourceS_eq_sylow h hH hp F he
  obtain ⟨e,z,v,hz,hv,hzK,hz2,hv2,hn,hclasses,_,hfixed⟩ :=
    d.g2_short_fixed_coset_classes h hH hp F he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let l : parabolic₂ (F := F) →* G := P.subtype.comp e.left.symm.toMonoidHom
  have hvm : v.val = l G2ShortAction.short := by
    rw [hv]
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) :=
      ⟨rootC 1,(G2CompletionFusion.short (1:F)).property,G2ShortAction.short.property⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  have hCv : centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) := by
    rw [hvm]
    exact (hfixed hST).2
  let J := L ⊔ residual H
  let M := normalizer (L : Set G) ⊔ normalizer (residual H : Set G)
  have hTJ : (T : Subgroup G) ≤ J := by
    rw [←hST]
    exact ((d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.2 1).trans le_sup_right
  have hcatalogue : ∀ x : J, x.val∈(T : Subgroup G) → orderOf x=2 →
      IsConj z x ∨ IsConj v x := by
    simpa only [hST] using hclasses
  have hMclasses := classes_in_overgroup hTJ z v hcatalogue
  have hGclasses (x : G) (hx : orderOf x=2) : IsConj z.val x ∨ IsConj v.val x := by
    let a : (⊤ : Subgroup G) := ⟨x,mem_top x⟩
    have ha : orderOf a=2 := (Subgroup.orderOf_coe a).symm.trans hx
    rcases hMclasses ⊤ le_top a ha with hh | hh
    · exact Or.inl ((⊤ : Subgroup G).subtype.map_isConj hh)
    · exact Or.inr ((⊤ : Subgroup G).subtype.map_isConj hh)
  have hJM : J ≤ M := sup_le (L.le_normalizer.trans le_sup_left)
    ((residual H).le_normalizer.trans le_sup_right)
  let zM : M := inclusion hJM z
  let vM : M := inclusion hJM v
  have hzM : orderOf zM=2 := (orderOf_injective (inclusion hJM) (inclusion_injective _) z).trans hz2
  have hvM : orderOf vM=2 := (orderOf_injective (inclusion hJM) (inclusion_injective _) v).trans hv2
  have hMz : ∀ a : M, IsConj zM a ↔ IsConj z.val a.val :=
    fusion_from_two_classes zM vM hzM hn (hMclasses M hJM)
  have hMv : ∀ a : M, IsConj vM a ↔ IsConj v.val a.val :=
    fusion_from_two_classes vM zM hvM (fun hh => hn hh.symm)
      (fun a ha => (hMclasses M hJM a ha).symm)
  have hCz : centralizer ({z.val} : Set G) ≤ M :=
    ((d.g2_central_involution_centralizers h hH hp F he) 1 z.val hzK
      ((Subgroup.orderOf_coe z).trans hz2)).trans le_sup_right
  have hMG : M=⊤ := TwoInvolutionClassOrder.eq_top_of_centralizers_le M z.val v.val
    ((Subgroup.orderOf_coe z).trans hz2) ((Subgroup.orderOf_coe v).trans hv2)
    hn hGclasses zM.property vM.property hCz (hCv.trans le_sup_left) hMz hMv
  have hcomp : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .g2 F he
  have hlocal := d.normalizer_local_conditions h hH (d.g2_right_maximal_all h hH hp F he) rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hcomp)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  have hN : J.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (by
    have hh := normalizer_pair_normalizes hlocal
    change M ≤ normalizer (J : Set G) at hh
    rwa [hMG] at hh))
  let : IsSimpleGroup G := h.qtke.simple
  have hJG : J=⊤ := hN.eq_bot_or_eq_top.resolve_left (by
    intro hbot
    have hz1 : z.val=1 := mem_bot.mp (hbot ▸ z.property)
    have hh : orderOf z.val=2 := (Subgroup.orderOf_coe z).trans hz2
    simp [hz1] at hh)
  exact ⟨hMG,hJG⟩

/-- The same compatible maps now form a faithful completion in the actual
ambient G. Its middle image is the whole source Borel, including both Cartans. -/
theorem Preparation.g2_ambient_completion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∃ c : RankTwoAmalgam.FaithfulCompletion
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse (G := G),
      c.left = (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom ∧
      c.right = (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).subtype.comp
        e.right.symm.toMonoidHom ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range := by
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let P₁ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hgen : P₀ ⊔ P₁ = ⊤ := by
    rw [ChapterF.Source.parabolics_generate]
    change L ⊔ residual H ⊔ sourceS L H = ⊤
    rw [(d.g2_ambient_generation h hH hp F (Or.inr ⟨e⟩)).2,top_sup_eq]
  let c₀ : RankTwoAmalgam.FaithfulCompletion
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (G := G) :=
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups P₀ (P₀ ⊓ P₁) P₁
      inf_le_left inf_le_right hgen
  let c := c₀.comapIso e.symm
  have hmid : c.middle.range = P₀ ⊓ P₁ := by
    rw [RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range]
    exact range_subtype _
  refine ⟨c,rfl,rfl,hmid.trans (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hH.1.1.2)),?_⟩
  rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,hmid]
  exact congrArg₂ (fun X Y : Subgroup G => X ⊓ Y) (range_subtype P₀) (range_subtype P₁)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
