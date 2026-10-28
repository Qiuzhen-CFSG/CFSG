module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortAction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CompletionFusionModel
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong.RootSeparation

/-!
# Fusion comparison on both entire G₂ parabolics

The root-coordinate reduction tracks the ambient and model classes at once,
using only the two compatible local maps. Sylow conjugacy inside either
parabolic extends this comparison from the common Sylow to every local
involution. The explicit octonion displacement obstruction separates the
model root classes; the original source nonfusion separates their ambient
images. Consequently the compatible maps preserve and reflect fusion for
involutions in either endpoint, including pairs in different endpoints.

This is the local class comparison used in the orbital exchange in F.4.42.
It does not identify local centralizer orbits with full ambient centralizer
orbits, or assert the remaining unique-fixed-coset condition. No S=T or
completion isomorphism is required. The internal import reuses the existing
coordinate reduction without changing its public boundary.

Source: Aschbacher–Smith F.4.35 and F.4.42, printed pp.292 and 295, and
5.3.3, p.659 (`refs/quasithin.pdf`). Coordinates reuse the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2LocalFusion
open G2CompletionFusion
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

private theorem simultaneous_classes
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩ = l ⟨x,hy⟩)
    (x : parabolic₁ (F := F)) (hx : x.val ∈ unipotent) (hx2 : orderOf x = 2) :
    (IsConj (f (long 1)) (f x) ∧ IsConj (rootA (1:F)) x.val) ∨
      (IsConj (f (short 1)) (f x) ∧ IsConj (rootC (1:F)) x.val) := by
  let P : Model F → Prop := fun y => ∀ hy : y ∈ parabolic₁,
    (IsConj (f (long 1)) (f ⟨y,hy⟩) ∧ IsConj (rootA (1:F)) y) ∨
      (IsConj (f (short 1)) (f ⟨y,hy⟩) ∧ IsConj (rootC (1:F)) y)
  have hA (a : F) (ha0 : a ≠ 0) : P (rootA a) := by
    intro _
    exact Or.inl ⟨long_conj_one f a ha0,
      long_conj_one (parabolic₁ (F := F)).subtype a ha0⟩
  have hC (a : F) (ha0 : a ≠ 0) : P (rootC a) := by
    intro _
    exact Or.inr ⟨short_conj_one f a ha0,
      short_conj_one (parabolic₁ (F := F)).subtype a ha0⟩
  have hstep : ∀ g : Model F, g ∈ parabolic₁ ∨ g ∈ parabolic₂ →
      ∀ y ∈ unipotent, MulAut.conj g y ∈ unipotent →
        (P (MulAut.conj g y) ↔ P y) := by
    intro g hg y hy hgy
    have hc : IsConj (f ⟨y,u1 hy⟩) (f ⟨MulAut.conj g y,u1 hgy⟩) := by
      rcases hg with hg | hg
      · exact map_local_conj f g hg y _ (u1 hy) (u1 hgy) rfl
      · rw [ha y (u1 hy) (u2 hy),ha _ (u1 hgy) (u2 hgy)]
        apply isConj_iff.mpr
        refine ⟨l ⟨g,hg⟩,?_⟩
        rw [←map_inv,←map_mul,←map_mul]
        rfl
    have hm : IsConj y (MulAut.conj g y) := isConj_iff.mpr ⟨g,rfl⟩
    constructor
    · intro hh _
      exact (hh (u1 hgy)).elim
        (fun h => Or.inl ⟨h.1.trans hc.symm,h.2.trans hm.symm⟩)
        (fun h => Or.inr ⟨h.1.trans hc.symm,h.2.trans hm.symm⟩)
    · intro hh _
      exact (hh (u1 hy)).elim
        (fun h => Or.inl ⟨h.1.trans hc,h.2.trans hm⟩)
        (fun h => Or.inr ⟨h.1.trans hc,h.2.trans hm⟩)
  rw [unipotent_eq_range] at hx
  obtain ⟨t,ht⟩ := hx
  have hs : unipotentProduct t ^ 2 = 1 := by
    rw [ht]
    exact congrArg Subtype.val (hx2 ▸ pow_orderOf_eq_one x)
  have hn : unipotentProduct t ≠ 1 := by
    rw [ht]
    intro he
    have hh : x = 1 := Subtype.ext he
    simp [hh] at hx2
  have hh := unipotent_reduction P hA hC hstep t hs hn
  rw [ht] at hh
  exact hh x.property

private theorem parabolic_classes
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩ = l ⟨x,hy⟩)
    (Q : Subgroup (Model F)) (hUQ : unipotent ≤ Q) (k : Q →* G)
    (hk : ∀ x hx, k ⟨x,hUQ hx⟩ = f ⟨x,u1 hx⟩)
    (x : Q) (hx2 : orderOf x = 2) :
    (IsConj (f (long 1)) (k x) ∧ IsConj (rootA (1:F)) x.val) ∨
      (IsConj (f (short 1)) (k x) ∧ IsConj (rootC (1:F)) x.val) := by
  let U := (sylow (F := F)).subtype hUQ
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hx2,pow_one])
  obtain ⟨V,hV⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Q V U
  let y := g*x*g⁻¹
  have hy : y.val ∈ unipotent := by
    have hh : y ∈ (U : Subgroup Q) := by
      rw [←hg]
      exact ⟨x,hV (mem_zpowers x),rfl⟩
    exact hh
  let z : parabolic₁ (F := F) := ⟨y.val,u1 hy⟩
  have hz2 : orderOf z = 2 := by
    rw [←Subgroup.orderOf_coe,show z.val = y.val from rfl,Subgroup.orderOf_coe]
    exact ((MulAut.conj g).orderOf_eq x).trans hx2
  have hky : k y = f z := hk y.val hy
  have hc : IsConj (k x) (f z) := hky ▸ k.map_isConj (isConj_iff.mpr ⟨g,rfl⟩)
  have hm : IsConj x.val z.val := Q.subtype.map_isConj (isConj_iff.mpr ⟨g,rfl⟩)
  exact (simultaneous_classes f l ha z hy hz2).elim
    (fun h => Or.inl ⟨h.1.trans hc.symm,h.2.trans hm.symm⟩)
    (fun h => Or.inr ⟨h.1.trans hc.symm,h.2.trans hm.symm⟩)

omit [Finite F] in
private theorem model_nonfusion : ¬ IsConj (rootA (1:F)) (rootC (1:F)) := by
  rintro h
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  exact EvenInvolutionGeometry.PureLong.rootC_not_long one_ne_zero ⟨1,one_ne_zero,g,hg.symm⟩

omit [Finite F] in
private theorem fusion_iff_of_matching {a b z v : G} {a' b' : Model F}
    (hn : ¬ IsConj z v)
    (ha : (IsConj z a ∧ IsConj (rootA (1:F)) a') ∨
      (IsConj v a ∧ IsConj (rootC (1:F)) a'))
    (hb : (IsConj z b ∧ IsConj (rootA (1:F)) b') ∨
      (IsConj v b ∧ IsConj (rootC (1:F)) b')) :
    IsConj a b ↔ IsConj a' b' := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ⟨fun _ => ha.2.symm.trans hb.2,fun _ => ha.1.symm.trans hb.1⟩
  · exact ⟨fun h => (hn (ha.1.trans (h.trans hb.1.symm))).elim,
      fun h => (model_nonfusion (ha.2.trans (h.trans hb.2.symm))).elim⟩
  · exact ⟨fun h => (hn (hb.1.trans (h.symm.trans ha.1.symm))).elim,
      fun h => (model_nonfusion (hb.2.trans (h.symm.trans ha.2.symm))).elim⟩
  · exact ⟨fun _ => ha.2.symm.trans hb.2,fun _ => ha.1.symm.trans hb.1⟩

/-- The compatible maps preserve and reflect ambient fusion for involutions
in either whole parabolic, including pairs from different endpoints. -/
theorem compatible_parabolic_fusion
    (f : parabolic₁ (F := F) →* G) (l : parabolic₂ (F := F) →* G)
    (ha : ∀ (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂),
      f ⟨x,hx⟩ = l ⟨x,hy⟩)
    (hn : ¬ IsConj (f (long 1)) (f (short 1))) :
    (∀ x y : parabolic₁ (F := F), orderOf x = 2 → orderOf y = 2 →
      (IsConj (f x) (f y) ↔ IsConj x.val y.val)) ∧
    (∀ x y : parabolic₂ (F := F), orderOf x = 2 → orderOf y = 2 →
      (IsConj (l x) (l y) ↔ IsConj x.val y.val)) ∧
    (∀ (x : parabolic₁ (F := F)) (y : parabolic₂ (F := F)),
      orderOf x = 2 → orderOf y = 2 → (IsConj (f x) (l y) ↔ IsConj x.val y.val)) := by
  have h₁ := parabolic_classes f l ha parabolic₁ u1 f (fun _ _ => rfl)
  have h₂ := parabolic_classes f l ha parabolic₂ u2 l (fun x hx => (ha x (u1 hx) (u2 hx)).symm)
  exact ⟨fun x y hx hy => fusion_iff_of_matching hn (h₁ x hx) (h₁ y hy),
    fun x y hx hy => fusion_iff_of_matching hn (h₂ x hx) (h₂ y hy),
    fun x y hx hy => fusion_iff_of_matching hn (h₁ x hx) (h₂ y hy)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2LocalFusion

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- F.4.35's class comparison on the two entire original parabolics. The
original nonfusion theorem supplies the same marked comparison on both
sides; no fusion or recognition premise is added. -/
theorem Preparation.g2_parabolic_involution_fusion
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
      ¬ IsConj (e.right.symm (G2CompletionFusion.long (1:F))).val
        (e.right.symm (G2CompletionFusion.short (1:F))).val ∧
      (∀ x y : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0,
        orderOf x = 2 → orderOf y = 2 →
          (IsConj x.val y.val ↔ IsConj (e.left x).val (e.left y).val)) ∧
      (∀ x y : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
        orderOf x = 2 → orderOf y = 2 →
          (IsConj x.val y.val ↔ IsConj (e.right x).val (e.right y).val)) ∧
      (∀ (x : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
        (y : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1),
        orderOf x = 2 → orderOf y = 2 →
          (IsConj x.val y.val ↔ IsConj (e.left x).val (e.right y).val)) := by
  obtain ⟨e,z,v,hz,hv,_,_,_,hn,_⟩ := d.g2_completion_involution_classes h hH hp F he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  let l : parabolic₂ (F := F) →* G := Q.subtype.comp e.left.symm.toMonoidHom
  have ha (x : Model F) (hx : x ∈ parabolic₁) (hy : x ∈ parabolic₂) :
      f ⟨x,hx⟩ = l ⟨x,hy⟩ := by
    let b : ChapterF.GreenBook.LieModels.G2.overlap (F := F) := ⟨x,hx,hy⟩
    exact (congrArg Subtype.val (e.symm.right_commutes b)).trans
      (congrArg Subtype.val (e.symm.left_commutes b)).symm
  have hn' : ¬ IsConj (f (G2CompletionFusion.long 1)) (f (G2CompletionFusion.short 1)) := by
    change ¬ IsConj (e.right.symm (G2CompletionFusion.long (1:F))).val
      (e.right.symm (G2CompletionFusion.short (1:F))).val
    rwa [←hz,←hv]
  obtain ⟨hr,hl,hlr⟩ := G2LocalFusion.compatible_parabolic_fusion f l ha hn'
  have hfr (x : P) : f (e.right x) = x.val := congrArg Subtype.val (e.right.symm_apply_apply x)
  have hll (x : Q) : l (e.left x) = x.val := congrArg Subtype.val (e.left.symm_apply_apply x)
  refine ⟨e,hn',?_,?_,?_⟩
  · intro x y hx hy
    simpa only [hll] using hl (e.left x) (e.left y)
      ((e.left.orderOf_eq x).trans hx) ((e.left.orderOf_eq y).trans hy)
  · intro x y hx hy
    simpa only [hfr] using hr (e.right x) (e.right y)
      ((e.right.orderOf_eq x).trans hx) ((e.right.orderOf_eq y).trans hy)
  · intro x y hx hy
    have hh := hlr (e.right y) (e.left x)
      ((e.right.orderOf_eq y).trans hy) ((e.left.orderOf_eq x).trans hx)
    rw [hfr,hll] at hh
    exact ⟨fun h => (hh.mp h.symm).symm,fun h => (hh.mpr h.symm).symm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
