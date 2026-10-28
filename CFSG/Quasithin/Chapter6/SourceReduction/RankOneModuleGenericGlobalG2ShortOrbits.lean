module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow

/-!
# Commuting-pair exchange for the G₂ short-root centralizer

The A- and E-root involutions are conjugate in the ambient group, but lie in
distinct orbits of the full centralizer of the pinned C-root involution.
An explicit Weyl word exchanges the commuting pair (E,C) with (A,F).
A conjugator in the C-root centralizer would therefore produce an element
of the full A-root centralizer moving C out of the original right radical.
The original centralizer bound and characteristicity of that radical exclude
this. Both compatible local maps are retained throughout.

The right-factor centralizer of the pinned C-root is exactly C_S(v), for the
original S=O₂(N_G(L) ∩ H). In model coordinates, an element centralizing both
A and C is in the Borel; its two torus parameters are forced to be one.
The residual and Sylow comparison maps transport this to the source factors.
Neither conclusion requires S=T. The internal import reuses the existing
inverse Sylow-image proof without changing its public boundary.

These are steps in F.4.42's orbital comparison, not the full centralizer
containment. Exhaustive coverage, common-stabilizer containment and the
unique-fixed-coset premise remain to be proved by the source assembly.
Source: Aschbacher–Smith F.4.42, printed p.295, and 5.3.3, p.659
(`refs/quasithin.pdf`). Coordinates reuse the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortOrbits
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The pinned E-root in the original left model parabolic. -/
@[expose] def outside : parabolic₂ (F := F) :=
  ⟨rootE 1,unipotent_le_local₂.trans local₂_le_parabolic₂ (by
    rw [unipotent_eq_range]
    exact ⟨![0,0,0,0,1,0],by simp [unipotentProduct]⟩)⟩

omit [Finite F] in
private theorem outside_commutes : Commute (outside (F := F)).val (rootC (1:F)) := by
  apply mem_centralizer_singleton_iff.mp
  apply residualBlock_le_centralizer_rootC
  rw [show (outside (F := F)).val = rootE 1 from rfl,←block_upper]
  exact mem_sup_right ⟨_,rfl⟩

/-- The E-root image, viewed inside the full ambient short-root centralizer. -/
@[expose] def outsideMark {G : Type*} [Group G] (f : parabolic₂ (F := F) →* G) :
    centralizer ({f G2ShortAction.short} : Set G) :=
  ⟨f outside,mem_centralizer_singleton_iff.mpr (by
    rw [←map_mul,←map_mul]
    exact congrArg f (Subtype.ext outside_commutes.eq))⟩

variable {G : Type*} [Group G]

omit [Finite F] in
private theorem weylS_rootC : MulAut.conj (weylS : Model F) (rootC 1)=rootD 1 := by
  have hC : rootC (1:F)=unipotentProduct ![0,0,1,0,0,0] := by simp [unipotentProduct]
  change weylS * _ * weylS⁻¹ = _
  rw [hC,weylS_fiveRoot_conjugate _ rfl]
  simp [unipotentProduct]

omit [Finite F] [CharP F 2] in
private theorem rootE_to_B : MulAut.conj (weylS : Model F) (rootE 1)=rootB 1 := by
  calc
    _ = MulAut.conj weylS (MulAut.conj weylS (rootB (1:F))) :=
      congrArg (MulAut.conj weylS) (weylS_rootB (1:F)).symm
    _ = _ := by rw [←MulAut.mul_apply,←map_mul,←pow_two,weylS_sq,map_one,MulAut.one_apply]

omit [Finite F] [CharP F 2] in
private theorem rootB_to_A : MulAut.conj (weylR : Model F) (rootB 1)=rootA 1 := by
  calc
    _ = MulAut.conj weylR (MulAut.conj weylR (rootA (1:F))) :=
      congrArg (MulAut.conj weylR) (weylR_rootA (1:F)).symm
    _ = _ := by rw [←MulAut.mul_apply,←map_mul,←pow_two,weylR_sq,map_one,MulAut.one_apply]

private def u₁ (x : Model F) (hx : x ∈ unipotent) : parabolic₁ (F := F) :=
  ⟨x,unipotent_le_local₁.trans (le_sup_left.trans_eq local₁_sup_borel) hx⟩
private def u₂ (x : Model F) (hx : x ∈ unipotent) : parabolic₂ (F := F) :=
  ⟨x,unipotent_le_local₂.trans local₂_le_parabolic₂ hx⟩

omit [Finite F] [CharP F 2] in
private theorem rootU (t : Fin 6 → F) : unipotentProduct t ∈ unipotent :=
  unipotentProduct_mem t

omit [Finite F] in
/-- The two explicit Weyl steps exchange the commuting marked pairs. -/
private theorem exchange
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩) :
    ∃ w : G,
      MulAut.conj w (l outside)=f (G2CompletionFusion.long 1) ∧
      MulAut.conj w (l G2ShortAction.short)=f
        (u₁ (rootF 1) (by simpa [unipotentProduct] using rootU (F := F) ![0,0,0,0,0,1])) := by
  let s : parabolic₁ (F := F) := ⟨weylS,mem_sup_right (subset_closure (Set.mem_singleton _))⟩
  let r : parabolic₂ (F := F) := ⟨weylR,weylR_mem_parabolic⟩
  have hE : rootE (1:F) ∈ unipotent := by simpa [unipotentProduct] using rootU (F := F) ![0,0,0,0,1,0]
  have hB : rootB (1:F) ∈ unipotent := by simpa [unipotentProduct] using rootU (F := F) ![0,1,0,0,0,0]
  have hD : rootD (1:F) ∈ unipotent := by simpa [unipotentProduct] using rootU (F := F) ![0,0,0,1,0,0]
  have hC : rootC (1:F) ∈ unipotent := by simpa [unipotentProduct] using rootU (F := F) ![0,0,1,0,0,0]
  have hF : rootF (1:F) ∈ unipotent := by simpa [unipotentProduct] using rootU (F := F) ![0,0,0,0,0,1]
  have hEf : l outside=f (u₁ _ hE) := (ha _ _ _).symm
  have hCf : l G2ShortAction.short=f (u₁ _ hC) := (ha _ _ _).symm
  have hBl : f (u₁ _ hB)=l (u₂ _ hB) := ha _ _ _
  have hDl : f (u₁ _ hD)=l (u₂ _ hD) := ha _ _ _
  refine ⟨l r * f s,?_,?_⟩
  · rw [map_mul,MulAut.mul_apply,hEf]
    have hs : MulAut.conj (f s) (f (u₁ _ hE))=f (u₁ _ hB) := by
      simp only [MulAut.conj_apply,←map_inv,←map_mul]
      exact congrArg f (Subtype.ext rootE_to_B)
    rw [hs,hBl]
    have hr : MulAut.conj (l r) (l (u₂ _ hB))=l G2ShortAction.long := by
      simp only [MulAut.conj_apply,←map_inv,←map_mul]
      exact congrArg l (Subtype.ext rootB_to_A)
    rw [hr]
    exact (ha _ (G2CompletionFusion.long (1:F)).property G2ShortAction.long.property).symm
  · rw [map_mul,MulAut.mul_apply,hCf]
    have hs : MulAut.conj (f s) (f (u₁ _ hC))=f (u₁ _ hD) := by
      simp only [MulAut.conj_apply,←map_inv,←map_mul]
      exact congrArg f (Subtype.ext weylS_rootC)
    rw [hs,hDl]
    have hr : MulAut.conj (l r) (l (u₂ _ hD))=l (u₂ _ hF) := by
      simp only [MulAut.conj_apply,←map_inv,←map_mul]
      exact congrArg l (Subtype.ext (weylR_rootD (1:F)))
    rw [hr]
    exact (ha _ (u₁ _ hF).property (u₂ _ hF).property).symm


omit [Finite F] in
/-- Pair exchange separates the two long-root orbits in the full ambient
short-root centralizer. The full long-root centralizer must preserve the
original short-parabolic radical, not merely a chosen local subgroup. -/
private theorem compatible_orbits_distinct
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩=l ⟨x,hy⟩)
    (hC : centralizer ({f (G2CompletionFusion.long 1)} : Set G) ≤
      normalizer (((radical₁ (F := F)).subgroupOf parabolic₁).map f : Set G)) :
    ¬ IsConj (G2ShortAction.longMark l) (outsideMark l) := by
  obtain ⟨w,hwz,hwt⟩ := exchange f l ha
  have hz : l G2ShortAction.long=f (G2CompletionFusion.long 1) :=
    (ha _ (G2CompletionFusion.long (1:F)).property G2ShortAction.long.property).symm
  let Q := ((radical₁ (F := F)).subgroupOf parabolic₁).map f
  have hv : f (G2CompletionFusion.short 1)=l G2ShortAction.short := ha _ _ _
  have hvQ : l G2ShortAction.short ∈ Q := by
    rw [←hv]
    apply mem_map_of_mem
    exact ⟨![0,0,1,0,0,0],rfl,by simp [unipotentProduct,G2CompletionFusion.short]⟩
  rintro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have hg' : MulAut.conj g.val (f (G2CompletionFusion.long 1))=l outside := by
    have hh := congrArg Subtype.val hg
    change MulAut.conj g.val (l G2ShortAction.long)=l outside at hh
    rwa [hz] at hh
  have hk : w*g.val ∈ centralizer ({f (G2CompletionFusion.long 1)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    change MulAut.conj (w*g.val) _ = _
    rw [map_mul,MulAut.mul_apply,hg',hwz]
  have hgt : MulAut.conj g.val (l G2ShortAction.short)=l G2ShortAction.short :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property)
  have htQ := (mem_normalizer_iff.mp (hC hk) (l G2ShortAction.short)).mp hvQ
  change MulAut.conj (w*g.val) (l G2ShortAction.short) ∈ Q at htQ
  rw [map_mul,MulAut.mul_apply,hgt,hwt] at htQ
  obtain ⟨y,hy,he⟩ := htQ
  have hyF : y.val=rootF 1 := congrArg Subtype.val (hf he)
  have hFR : rootF (1:F) ∈ radical₁ := hyF ▸ hy
  obtain ⟨t,ht,he⟩ := hFR
  have hF : rootF (1:F)=unipotentProduct ![0,0,0,0,0,1] := by simp [unipotentProduct]
  rw [hF] at he
  have he' := congrFun (unipotentProduct_injective he) 5
  exact one_ne_zero (he'.symm.trans ht)

omit [Finite F] in
/-- Inside the original right factor, the short-root centralizer is already
in the common Sylow. This identifies the subgroup normalized by the full
common centralizer of the two marked roots. -/
private theorem local_short_centralizer_le_unipotent :
    local₁ (F := F) ⊓ centralizer ({rootC (1:F)} : Set (Model F)) ≤ unipotent := by
  intro g hg
  have hgb : g ∈ Atlas.G2.borel := (LieParabolicSetup.parabolics_intersection (F := F)).le
    (show g ∈ parabolic₁ ⊓ parabolic₂ from
      ⟨(le_sup_left.trans_eq local₁_sup_borel) hg.1,
        centralizer_rootC_le_parabolic 1 one_ne_zero hg.2⟩)
  obtain ⟨⟨u,t⟩,het⟩ := borelProductEquiv.surjective ⟨g,hgb⟩
  have he : u.val*t.val=g := congrArg Subtype.val het
  obtain ⟨⟨l,m⟩,hlm⟩ := t.property
  change torus l m=t.val at hlm
  rw [←hlm] at he
  obtain ⟨a,ha⟩ := (unipotent_eq_range (K := F)).le u.property
  have hga : Commute (u.val * torus l m) (rootA (1:F)) :=
    he.symm ▸ mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA 1 hg.1)
  have hta : Commute (torus l m) (rootA (1:F)) := by
    have hua : Commute u.val (rootA (1:F)) := ha ▸ unipotentProduct_commute_rootA a 1
    simpa only [inv_mul_cancel_left] using hua.inv_left.mul_left hga
  have hchar : (l:F)*(m:F)=1 := by
    have hh := rootA_injective ((torus_rootA l m 1).symm.trans hta.mul_inv_cancel)
    simpa using hh
  have hgc : (u.val * torus l m) * rootC (1:F) * (u.val * torus l m)⁻¹=rootC 1 :=
    he.symm ▸ mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg.2)
  have hc : u.val * rootC (l:F)=rootC 1 * u.val := by
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      _ = u.val*(torus l m*rootC 1*(torus l m)⁻¹)*u.val⁻¹ := by rw [torus_rootC]; simp
      _ = rootC 1 := by simpa only [mul_inv_rev,mul_assoc] using hgc
  have hC (b:F) : rootC b=unipotentProduct ![0,0,b,0,0,0] := by simp [unipotentProduct]
  rw [←ha,hC,hC,unipotentProduct_mul,unipotentProduct_mul] at hc
  have hl : (l:F)=1 := by
    have hh := congrFun (unipotentProduct_injective hc) 2
    have hh' : (l:F)+a 2=a 2+1 := by simpa [unipotentProductParameters] using hh
    exact add_right_cancel (hh'.trans (add_comm (a 2) 1))
  have hm : (m:F)=1 := by simpa [hl] using hchar
  have hl' : l=1 := Units.ext hl
  have hm' : m=1 := Units.ext hm
  rw [hl',hm'] at he
  have ht1 : torus (1:Fˣ) 1=1 := by
    exact (torusHom (K := F)).map_one
  rw [ht1,mul_one] at he
  exact he ▸ u.property

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2ShortOrbits

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]


/-- The actual right-factor centralizer is exactly the intersection with the
original S. This equality holds before the ambient Sylow equality S=T. -/
theorem Preparation.g2_short_factor_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    let v := (e.right.symm (G2CompletionFusion.short (1:F))).val
    residual H ⊓ centralizer ({v} : Set G) = sourceS L H ⊓ centralizer ({v} : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hJ : J=solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJf : J.map f=residual H := by
    rw [hJ,show f=P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hTH hp 1
  have hS := source_g2_inverse_sylow_image d h hTH e
  apply le_antisymm
  · rintro x ⟨hxK,hxC⟩
    refine ⟨?_,hxC⟩
    rw [←hJf] at hxK
    obtain ⟨y,hy,rfl⟩ := hxK
    have hyC : y.val ∈ centralizer ({rootC (1:F)} : Set (Model F)) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh : y * G2CompletionFusion.short (1:F)=G2CompletionFusion.short 1 * y := by
        apply hf
        rw [map_mul,map_mul]
        exact mem_centralizer_singleton_iff.mp hxC
      exact congrArg Subtype.val hh
    have hyU : y.val ∈ unipotent := G2ShortOrbits.local_short_centralizer_le_unipotent ⟨hy,hyC⟩
    rw [←hS]
    exact mem_map_of_mem f hyU
  · exact inf_le_inf_right _ ((d.g2_local_structure h hTH hp F (Or.inr ⟨e⟩)).2.2.2.2 1)

/-- Two ambient-conjugate long roots lie in distinct orbits of the full
short-root centralizer. The original right two-core separates the orbits
by commuting-pair exchange; no equality S=T is required. -/
theorem Preparation.g2_short_centralizer_distinct_long_orbits
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
      let f := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom
      let z := G2ShortAction.longMark f
      let u := G2ShortOrbits.outsideMark f
      IsConj z.val u.val ∧ ¬ IsConj z u := by
  obtain ⟨e,z,_,hz,_,hzK,hz2,_,_,_⟩ := d.g2_completion_involution_classes h hH hp F he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* G := Q.subtype.comp e.left.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  have ha (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂) :
      f ⟨x,hx⟩=l ⟨x,hy⟩ := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  have hz' : l G2ShortAction.long=f (G2CompletionFusion.long 1) :=
    (ha (rootA 1) (G2CompletionFusion.long (1:F)).property G2ShortAction.long.property).symm
  have hq : 2 < Nat.card F := by
    rw [(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent
  let J := (local₁ (F := F)).subgroupOf parabolic₁
  have hJ : J=solvableResidual (parabolic₁ (F := F)) := by
    apply map_injective (parabolic₁ (F := F)).subtype_injective
    rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
      HigherFieldResiduals.parabolic₁_residual hq]
  have hJf : J.map f=residual H := by
    rw [hJ,show f=P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 1
  have hQ : ((radical₁ (F := F)).subgroupOf parabolic₁).map f=(residual H).pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 local₁ parabolic₁ (le_sup_left.trans_eq local₁_sup_borel),
      local₁_pCoreIn] at hh
    exact hh
  have hC : centralizer ({f (G2CompletionFusion.long 1)} : Set G) ≤
      normalizer (((radical₁ (F := F)).subgroupOf parabolic₁).map f : Set G) := by
    rw [hQ]
    have hc := d.g2_central_involution_centralizers h hH hp F he 1 z.val hzK
      ((Subgroup.orderOf_coe z).trans hz2)
    exact (hz ▸ hc).trans (normalizer_le_normalizer_characteristic_image (residual H)
      (pCore 2 (residual H)))
  refine ⟨e,?_,G2ShortOrbits.compatible_orbits_distinct f hf l ha hC⟩
  obtain ⟨w,hw,_⟩ := G2ShortOrbits.exchange f l ha
  change IsConj (l G2ShortAction.long) (l G2ShortOrbits.outside)
  rw [hz']
  exact (isConj_iff.mpr ⟨w,hw⟩).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
