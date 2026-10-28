module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelFusion
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.InvolutionFusion

/-!
# Full involution fusion in the ordinary marked U₄(2) completion

Every involution of the original overlap Sylow is moved into the plane
radical by the point endpoint. We retain both the concrete model conjugation
and its image under the actual completion. Model fusion on that radical
lifts through the plane endpoint. Conversely, the source normalizer and
centralizer hypotheses force ambient fusion there to occur in the same
endpoint, and injectivity reflects it back to the model.

This proves F.4.35 for the ordinary U₄(2) amalgam, including the short-root
separation needed later in F.4.42. The graph extension and its exceptional
F.5 completion are separate source branches.
Source: Aschbacher--Smith, printed pp.291--292.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.FullPlainFusion
open GreenBook.LieModels.UnitaryFour
open InvolutionPlacement InvolutionFusion
local notation "hn" => Nat.le_refl 1
local notation "L" => L2 1 hn
local notation "B" => overlap 1 hn
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

/-- Placement preserves the literal conjugation equations in both the
model and the supplied completion. -/
theorem marked_placement (a : B) (ha : a ∈ S0) (ha2 : a ^ 2 = 1) :
    ∃ g : P, ∃ q : pCore 2 L,
      g.val * a.val * g.val⁻¹ = q.val.val ∧
      i (c.left g) * i (c.middle a) * (i (c.left g))⁻¹ =
        PlainFusion.planeEmbedding c i q.val := by
  have ha2' : a.val ^ 2 = 1 := congrArg Subtype.val ha2
  obtain ⟨g, hg⟩ := projective_sylow_involution_placement a.val ha ha2'
  obtain ⟨q, hq, he⟩ := hg
  change q.val = g.val * a.val * g.val⁻¹ at he
  have haP : a.val ∈ P := (show a.val ∈ P ⊓ R by
    rw [exact_overlap]; exact a.property).1
  have hqP : q.val ∈ P := by
    rw [he]
    exact (pointParabolic 1 hn).mul_mem ((pointParabolic 1 hn).mul_mem g.property haP) ((pointParabolic 1 hn).inv_mem g.property)
  have hqB : q.val ∈ B := by
    rw [← exact_overlap]
    exact ⟨hqP, L2_le_planeParabolic 1 hn q.property⟩
  let b : B := ⟨q.val, hqB⟩
  have hleft : g * (amalgam 1 hn).left a * g⁻¹ =
      (amalgam 1 hn).left b := Subtype.ext he.symm
  refine ⟨g, ⟨q, hq⟩, he.symm, ?_⟩
  calc
    i (c.left g) * i (c.middle a) * (i (c.left g))⁻¹ =
        i (c.left (g * (amalgam 1 hn).left a * g⁻¹)) := by
      simp only [map_mul, map_inv]
      rfl
    _ = i (c.middle b) := by rw [hleft]; rfl
    _ = i (c.right ((amalgam 1 hn).right b)) :=
      congrArg i (DFunLike.congr_fun c.compatible b)
    _ = PlainFusion.planeEmbedding c i q := rfl

/-- Concrete model fusion of overlap involutions lifts through any faithful
completion, retaining the original two endpoint maps. -/
theorem model_fusion_lifts (a b : B) (ha : a ∈ S0) (hb : b ∈ S0)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hab : IsConj a.val b.val) :
    IsConj (i (c.middle a)) (i (c.middle b)) := by
  obtain ⟨g, q, hq, hq'⟩ := marked_placement c i a ha ha2
  obtain ⟨h, r, hr, hr'⟩ := marked_placement c i b hb hb2
  have haq : IsConj a.val q.val.val := isConj_iff.mpr ⟨g.val, hq⟩
  have hbr : IsConj b.val r.val.val := isConj_iff.mpr ⟨h.val, hr⟩
  obtain ⟨p, hp⟩ := ModelFusion.plane_fusion
    (show q.val.val ∈ planeCore from ⟨q.val, q.property, rfl⟩)
    (show r.val.val ∈ planeCore from ⟨r.val, r.property, rfl⟩)
    (haq.symm.trans (hab.trans hbr))
  let qR : R := inclusion (L2_le_planeParabolic 1 hn) q.val
  let rR : R := inclusion (L2_le_planeParabolic 1 hn) r.val
  have hpR : p * qR * p⁻¹ = rR := Subtype.ext hp
  have hpG : IsConj (PlainFusion.planeEmbedding c i q.val)
      (PlainFusion.planeEmbedding c i r.val) := by
    exact (i.comp c.right).map_isConj (isConj_iff.mpr ⟨p, hpR⟩)
  exact (isConj_iff.mpr ⟨i (c.left g), hq'⟩).trans
    (hpG.trans (isConj_iff.mpr ⟨i (c.left h), hr'⟩).symm)

/-- The source hypotheses prevent any further fusion of involutions in the
ordinary overlap Sylow. -/
theorem ambient_fusion_reflects [Finite G]
    (hi : Function.Injective i)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) =
      (i.comp c.right).range)
    (a b : B) (ha : a ∈ S0) (hb : b ∈ S0)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hab : IsConj (i (c.middle a)) (i (c.middle b))) :
    IsConj a.val b.val := by
  obtain ⟨g, q, hq, hq'⟩ := marked_placement c i a ha ha2
  obtain ⟨h, r, hr, hr'⟩ := marked_placement c i b hb hb2
  have haq : IsConj (i (c.middle a)) (PlainFusion.planeEmbedding c i q.val) :=
    isConj_iff.mpr ⟨i (c.left g), hq'⟩
  have hbr : IsConj (i (c.middle b)) (PlainFusion.planeEmbedding c i r.val) :=
    isConj_iff.mpr ⟨i (c.left h), hr'⟩
  rw [PlainFusion.sourcePlaneRootImage_eq] at hnorm
  obtain ⟨p, hp⟩ := PlainFusion.source_plain_plane_fusion c i hi z hz hzroot hc
    hnorm ⟨q.val, q.property, rfl⟩ ⟨r.val, r.property, rfl⟩
    (haq.symm.trans (hab.trans hbr))
  let qR : R := inclusion (L2_le_planeParabolic 1 hn) q.val
  let rR : R := inclusion (L2_le_planeParabolic 1 hn) r.val
  have hpR : p * qR * p⁻¹ = rR := by
    apply (hi.comp c.right_injective)
    simpa only [Function.comp_apply, map_mul, map_inv, PlainFusion.planeEmbedding,
      MonoidHom.comp_apply, qR, rR] using hp
  have hpM : IsConj q.val.val r.val.val :=
    isConj_iff.mpr ⟨p.val, congrArg Subtype.val hpR⟩
  exact (isConj_iff.mpr ⟨g.val, hq⟩).trans
    (hpM.trans (isConj_iff.mpr ⟨h.val, hr⟩).symm)

/-- Original F.4.35 for the ordinary marked U₄(2) amalgam. Involutions in
the actual overlap Sylow are fused in the concrete projective model exactly
when their images are fused in the ambient source group. -/
theorem source_plain_involution_fusion_iff [Finite G]
    (hi : Function.Injective i)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) =
      (i.comp c.right).range)
    (a b : B) (ha : a ∈ S0) (hb : b ∈ S0)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    IsConj a.val b.val ↔ IsConj (i (c.middle a)) (i (c.middle b)) :=
  ⟨model_fusion_lifts c i a b ha hb ha2 hb2,
    ambient_fusion_reflects c i hi z hz hzroot hc hnorm a b ha hb ha2 hb2⟩

end CFSG.Quasithin.ChapterF.UnitaryTwo.FullPlainFusion
