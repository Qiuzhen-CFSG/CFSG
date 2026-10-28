module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CenterKernel

/-!
# Ambient involution fusion in the actual G₂ factor join

Set K = O²(H), S = O₂(N_G(L) ∩ H), and J = L ∨ K. The compatible
G₂ comparison places S in K, so both source parabolics lie in J. Their
inverse maps therefore give homomorphisms into this actual join, agreeing
on the whole overlap. The two-group image of S lies in the model Borel's
unique Sylow subgroup. The coordinate reduction with local conjugators
then covers the involutions of S by two classes inside J.

The pinned highest long root maps into Z(K), by transport of the actual
parabolic solvable residual and its center. The pinned short root is the
same witness as in the proved general-degree nonfusion theorem. The two
classes consequently stay distinct in ambient G. Thus any ambient fusion
between involutions of S is already realized by J.

This advances the fusion comparison used in the centralizer and order
recognition argument. It does not identify J with the G₂ model or prove
J = G; the compatible comparison and original Preparation.unique_left
remain genuine inputs. The companion applies the result to the literal
Chapter12 chosen-module setup. Source: Aschbacher–Smith F.4.30, F.4.35
and F.4.43, pp.290,292,296, and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem source_parabolics_le_join {L K S : Subgroup G} (hSK : S≤K) :
    (ChapterF.Source.parabolic ![L,K] S 0 ≤ L⊔K) ∧
    (ChapterF.Source.parabolic ![L,K] S 1 ≤ L⊔K) := by
  constructor
  · change L⊔S⊔ChapterF.Source.borel K S ≤ L⊔K
    exact sup_le (sup_le le_sup_left (hSK.trans le_sup_right)) (inf_le_left.trans le_sup_right)
  · change K⊔S⊔ChapterF.Source.borel L S ≤ L⊔K
    exact sup_le (sup_le le_sup_right (hSK.trans le_sup_right)) (inf_le_left.trans le_sup_left)

omit [Finite G] in
private theorem source_g2_sylow_image {L H : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (x : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1)
    (hx : x.val∈sourceS L H) : (e.right x).val∈unipotent := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let a : P →* Model F := (parabolic₁ (F := F)).subtype.comp e.right.toMonoidHom
  let V := ((sourceS L H).subgroupOf P).map a
  have hVP : IsPGroup 2 V := ((pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype).map a
  have hVB : V ≤ Atlas.G2.borel := by
    rintro _ ⟨y,hy,rfl⟩
    let b : (P₀ ⊓ P : Subgroup G) :=
      ⟨y.val,(show sourceS L H ≤ P₀ from le_sup_right.trans le_sup_left) hy,y.property⟩
    have heq := congrArg Subtype.val (e.right_commutes b)
    change a y = (e.middle b).val at heq
    rw [heq]
    exact (ChapterF.GreenBook.LieModels.G2.overlap_eq_borel (F := F)).le (e.middle b).property
  let U := (Atlas.G2.LieParabolicSetup.sylow (F := F)).subtype
    (show unipotent ≤ Atlas.G2.borel from le_sup_left)
  let : (U : Subgroup (Atlas.G2.borel (K := F))).Normal := EvenBorelTorus.radical_normal
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  obtain ⟨D,hD⟩ := (hVP.comap_subtype : IsPGroup 2 (V.subgroupOf Atlas.G2.borel)).exists_le_sylow
  have hDU : D=U := Subsingleton.elim _ _
  have hxV : a x ∈ V := mem_map_of_mem a hx
  have hh := hD (show (⟨a x,hVB hxV⟩ : Atlas.G2.borel (K := F)) ∈
      V.subgroupOf Atlas.G2.borel from hxV)
  rw [hDU] at hh
  exact hh

private theorem source_g2_long_center
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    (e.right.symm (G2CompletionFusion.long (1:F))).val ∈
      (center (residual H)).map (residual H).subtype := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hq : 2<Nat.card F := by
    rw [(d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.exponent
  have hJ : J = solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJf : J.map f = residual H := by
    rw [hJ,show f = P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hTH hp 1
  have hZ : ((center J).map J.subtype).map f =
      (center (residual H)).map (residual H).subtype := by
    rw [map_subgroup_center_eq f hf,hJf]
  change f (G2CompletionFusion.long (1:F)) ∈ _
  rw [←hZ]
  apply mem_map_of_mem
  have hr : rootA (1:F) ∈ (center (local₁ (F := F))).map local₁.subtype := by
    refine ⟨⟨rootA 1,radical₁_le_local₁ (rootA_mem_radical₁ _)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA (1:F) y.property)
  have hm : ((center J).map J.subtype).map (parabolic₁ (F := F)).subtype =
      (center (local₁ (F := F))).map local₁.subtype := by
    rw [map_subgroup_center_eq _ (parabolic₁ (F := F)).subtype_injective,
      map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel)]
  have hh : (G2CompletionFusion.long (1:F)).val ∈
      ((center J).map J.subtype).map (parabolic₁ (F := F)).subtype := hm.symm ▸ hr
  obtain ⟨u,hu,he⟩ := hh
  exact (show u = G2CompletionFusion.long (1:F) from Subtype.ext he) ▸ hu


/-- The actual factor join has two marked classes covering the involutions
of the original S. Their images remain distinct under ambient G-conjugacy. -/
theorem Preparation.g2_completion_involution_classes
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
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (G2CompletionFusion.long (1:F))).val ∧
        v.val = (e.right.symm (G2CompletionFusion.short (1:F))).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        ∀ x : (L ⊔ residual H : Subgroup G), x.val∈sourceS L H → orderOf x=2 →
          IsConj z x ∨ IsConj v x := by
  let : Group (Model F) := inferInstance
  let : Group (parabolic₁ (F := F)) := Subgroup.toGroup _
  let : Group (parabolic₂ (F := F)) := Subgroup.toGroup _
  let : Group (L ⊔ residual H : Subgroup G) := Subgroup.toGroup _
  obtain ⟨e,v₀,_,⟨w,hwv,hw⟩,_,hv2,hnot⟩ := d.g2_short_root_not_fused h hH hp F he
  have hs := d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)
  have hSK : sourceS L H ≤ residual H := hs.2.2.2.2 1
  obtain ⟨hP₀,hP⟩ := source_parabolics_le_join hSK
  let J := L ⊔ residual H
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let P₀ := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* J := (inclusion hP).comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* J := (inclusion hP₀).comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := (inclusion_injective hP).comp e.right.symm.injective
  have ha (x : Model F) (hx : x∈parabolic₁) (hy : x∈parabolic₂) :
      f ⟨x,hx⟩ = l ⟨x,hy⟩ := by
    apply Subtype.ext
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  let z : J := f (G2CompletionFusion.long (1:F))
  let v : J := f (G2CompletionFusion.short (1:F))
  have hv : v.val=v₀ := by
    have hh : e.right w = G2CompletionFusion.short (1:F) := Subtype.ext hw
    have hh' := congrArg e.right.symm hh
    rw [e.right.symm_apply_apply] at hh'
    exact (congrArg Subtype.val hh').symm.trans hwv
  have hz : z.val∈(center (residual H)).map (residual H).subtype :=
    source_g2_long_center d h hH.1.1.2 hp e
  have hz2 : orderOf z=2 := by
    rw [show z=f (G2CompletionFusion.long (1:F)) from rfl,orderOf_injective f hf,
      ←orderOf_injective (parabolic₁ (F := F)).subtype Subtype.val_injective]
    apply orderOf_eq_prime
    · change (rootA (1:F))^2=1
      rw [pow_two,rootA_add,CharTwo.add_self_eq_zero,rootA_zero]
    · change rootA (1:F)≠1
      intro hh
      exact one_ne_zero (rootA_injective (hh.trans rootA_zero.symm))
  have hv2' : orderOf v=2 := by
    rw [←orderOf_injective J.subtype Subtype.val_injective]
    change orderOf v.val=2
    rw [hv]
    exact hv2
  refine ⟨e,z,v,rfl,rfl,hz,hz2,hv2',?_,?_⟩
  · intro hc
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    apply hnot g
    rw [←hv]
    exact ⟨z.val,hz,by change g*z.val*g⁻¹=v.val; exact hg⟩
  · intro x hx hx2
    let y : P := ⟨x.val, (show sourceS L H≤P from le_sup_right.trans le_sup_left) hx⟩
    have hy : (e.right y).val ∈ unipotent := source_g2_sylow_image e y hx
    have hy2 : (e.right y)^2=1 := by
      rw [←map_pow]
      have hxpow : x^2=1 := by simpa only [hx2] using pow_orderOf_eq_one x
      have hyy : y^2=1 := by
        apply Subtype.ext
        change x.val^2=1
        exact congrArg (fun t : J => t.val) hxpow
      rw [hyy,map_one]
    have hy1 : e.right y≠1 := by
      intro hyy
      have hyy' : y=1 := e.right.injective (hyy.trans e.right.map_one.symm)
      have hxx : x=1 := Subtype.ext (congrArg (fun t : P => t.val) hyy')
      simp [hxx] at hx2
    have hh := G2CompletionFusion.compatible_involution_classes f l ha (e.right y) hy hy2 hy1
    have hfxy : f (e.right y)=x := by
      change inclusion hP (e.right.symm (e.right y))=x
      rw [e.right.symm_apply_apply]
      rfl
    rwa [hfxy] at hh

/-- Ambient conjugacy between involutions of the original S is already
realized by the literal join L ∨ O²(H), without identifying that join with a model. -/
theorem Preparation.g2_completion_controls_involution_fusion
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
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (x y : G) (hx : x∈sourceS L H) (hy : y∈sourceS L H)
    (hx2 : orderOf x=2) (hy2 : orderOf y=2) :
    IsConj x y ↔ ∃ g∈L⊔residual H, g*x*g⁻¹=y := by
  constructor
  · intro hxy
    obtain ⟨_,z,v,_,_,_,_,_,hn,hclasses⟩ := d.g2_completion_involution_classes h hH hp F he
    let J := L⊔residual H
    have hSJ : sourceS L H≤J :=
      ((d.g2_local_structure h hH.1.1.2 hp F he).2.2.2.2 1).trans le_sup_right
    let a : J := ⟨x,hSJ hx⟩
    let b : J := ⟨y,hSJ hy⟩
    have ha2 : orderOf a=2 := (orderOf_injective J.subtype Subtype.val_injective a).symm.trans hx2
    have hb2 : orderOf b=2 := (orderOf_injective J.subtype Subtype.val_injective b).symm.trans hy2
    have hab : IsConj a b := by
      rcases hclasses a hx ha2 with ha|ha <;> rcases hclasses b hy hb2 with hb|hb
      · exact ha.symm.trans hb
      · exact (hn (((J.subtype.map_isConj ha).trans hxy).trans (J.subtype.map_isConj hb).symm)).elim
      · exact (hn (((J.subtype.map_isConj hb).trans hxy.symm).trans (J.subtype.map_isConj ha).symm)).elim
      · exact ha.symm.trans hb
    obtain ⟨g,hg⟩ := isConj_iff.mp hab
    exact ⟨g.val,g.property,congrArg Subtype.val hg⟩
  · rintro ⟨g,_,hg⟩
    exact isConj_iff.mpr ⟨g,hg⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
