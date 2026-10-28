module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ModelClasses
public import Theory.GroupTheory.SylowInvolutionFusionTransport
/-!
# Matching involution classes across the original endpoints

Sylow conjugacy reduces endpoint fusion to the marked overlap fusion theorem.
Both endpoint embeddings preserve and reflect the literal long and short
involution classes.
-/

open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.EndpointFusion
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion ModelClasses
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn
local notation "B" => overlap 1 hn
local notation "M" => ProjectiveGroup 1 hn
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

theorem point_involution_class_iff
    (hi : Function.Injective i)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (a b : P) (ha : a ^ 2 = 1) :
    IsConj a.val b.val ↔ IsConj (i (c.left a)) (i (c.left b)) := by
  let T := (projectiveSylow 1 hn).subtype (projectiveSylow_le_parabolics 1 hn).1
  apply T.involution_class_transport (P).subtype (i.comp c.left)
    (P).subtype_injective (hi.comp c.left_injective) _ a b ha
  intro x y hx hy hx2 hy2
  let xB : B := ⟨x.val,upperProjective_le_overlap 1 hn hx⟩
  let yB : B := ⟨y.val,upperProjective_le_overlap 1 hn hy⟩
  exact FullPlainFusion.source_plain_involution_fusion_iff c i hi z hz hzroot hc hnorm
    xB yB hx hy (Subtype.ext (congrArg (fun q : P => q.val) hx2)) (Subtype.ext (congrArg (fun q : P => q.val) hy2))

theorem plane_involution_class_iff
    (hi : Function.Injective i)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (a b : R) (ha : a ^ 2 = 1) :
    IsConj a.val b.val ↔ IsConj (i (c.right a)) (i (c.right b)) := by
  let T := (projectiveSylow 1 hn).subtype (projectiveSylow_le_parabolics 1 hn).2
  apply T.involution_class_transport (R).subtype (i.comp c.right)
    (R).subtype_injective (hi.comp c.right_injective) _ a b ha
  intro x y hx hy hx2 hy2
  let xB : B := ⟨x.val,upperProjective_le_overlap 1 hn hx⟩
  let yB : B := ⟨y.val,upperProjective_le_overlap 1 hn hy⟩
  have hh := FullPlainFusion.source_plain_involution_fusion_iff c i hi z hz hzroot hc hnorm
    xB yB hx hy (Subtype.ext (congrArg (fun q : R => q.val) hx2)) (Subtype.ext (congrArg (fun q : R => q.val) hy2))
  have he (v : R) (hV : v.val ∈ upperProjective 1 hn) :
      i (c.middle ⟨v.val,upperProjective_le_overlap 1 hn hV⟩) = i (c.right v) :=
    congrArg i (DFunLike.congr_fun c.compatible _)
  rw [he x hx,he y hy] at hh
  exact hh
end CFSG.Quasithin.ChapterF.UnitaryTwo.EndpointFusion