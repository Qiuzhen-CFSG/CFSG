module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourProjectiveInvolutionPlacement
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PlainFusion

/-!
# Involution placement in the ordinary binary unitary completion

The explicit Hermitian coordinates place every involution of the marked
overlap Sylow into the plane two-core, after conjugation by the point
parabolic.  The source wrapper records the actual ambient Thompson subgroup
produced by F.4.33, so this is usable in the faithful-completion fusion
argument without replacing the marked maps by an abstract model.

This is the placement part of F.4.35.  Complete involution fusion, the
short-centralizer recognition, and the graph-extension branch remain separate.
-/
@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.InvolutionFusion
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo.InvolutionPlacement
open CFSG.Quasithin.ChapterF.UnitaryTwo
local notation "hn" => Nat.le_refl 1
def S0 : Subgroup (overlap 1 hn) :=
  (projectiveSylow 1 hn).subtype (upperProjective_le_overlap 1 hn)

variable {G G0 : Type*} [Group G] [Group G0]

/-- Every involution in the marked overlap Sylow is point-conjugate into the
plane two-core.  This uses only the concrete U₄(2) coordinates. -/
theorem overlap_involution_to_plane
    (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
      (amalgam 1 hn) (G := G0))
    (i : G0 →* G) (hi : Function.Injective i)
    {x : G}
    (hx : x ∈ (S0 : Subgroup (overlap 1 hn)).map (i.comp c.middle))
    (hx2 : x ^ 2 = 1) :
    ∃ g : pointParabolic 1 hn,
      i (c.left g) * x * (i (c.left g))⁻¹ ∈ PlainFusion.planeImage c i := by
  obtain ⟨a, ha, rfl⟩ := hx
  have haU : (a : ProjectiveGroup 1 hn) ∈ upperProjective 1 hn := ha
  have hmiddle : Function.Injective (i.comp c.middle) := hi.comp c.middle_injective
  have hsqS : a ^ 2 = 1 := by
    apply hmiddle
    simpa only [map_pow, map_one] using hx2
  have hsq : (a : ProjectiveGroup 1 hn) ^ 2 = 1 := by
    simpa using congrArg (fun q : overlap 1 hn => (q : ProjectiveGroup 1 hn)) hsqS
  obtain ⟨g, hg⟩ := InvolutionPlacement.projective_sylow_involution_placement
    (a : ProjectiveGroup 1 hn) haU hsq
  refine ⟨g, ?_⟩
  let p : ProjectiveGroup 1 hn := g.val * (a : ProjectiveGroup 1 hn) * g.val⁻¹
  have hp : p ∈ InvolutionPlacement.planeCore := hg
  have haInf : (a : ProjectiveGroup 1 hn) ∈
      pointParabolic 1 hn ⊓ planeParabolic 1 hn := by
    rw [exact_overlap 1 hn]
    exact a.property
  have haP : (a : ProjectiveGroup 1 hn) ∈ pointParabolic 1 hn := haInf.1
  have hpP : p ∈ pointParabolic 1 hn := by
    exact (pointParabolic 1 hn).mul_mem
      ((pointParabolic 1 hn).mul_mem g.property haP)
      ((pointParabolic 1 hn).inv_mem g.property)
  have hpPlane : p ∈ planeParabolic 1 hn := by
    obtain ⟨q, hq, hqp⟩ := hp
    rw [← hqp]
    exact L2_le_planeParabolic 1 hn q.property
  have hpOinf : p ∈ pointParabolic 1 hn ⊓ planeParabolic 1 hn := ⟨hpP, hpPlane⟩
  have hpO : p ∈ overlap 1 hn := by
    rw [← exact_overlap 1 hn]
    exact hpOinf
  have heq : i (c.left g) * i (c.middle a) * (i (c.left g))⁻¹ =
      i (c.middle ⟨p, hpO⟩) := by
    change i (c.left g) * i (c.left ((amalgam 1 hn).left a)) *
      (i (c.left g))⁻¹ = i (c.left ((amalgam 1 hn).left ⟨p, hpO⟩))
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  change i (c.left g) * i (c.middle a) * (i (c.left g))⁻¹ ∈
    PlainFusion.planeImage c i
  rw [heq]
  obtain ⟨q, hq, hqp⟩ := hp
  refine ⟨q, hq, ?_⟩
  let qP : planeParabolic 1 hn := ⟨q, L2_le_planeParabolic 1 hn q.property⟩
  change i (c.right qP) = i (c.middle ⟨p, hpO⟩)
  rw [DFunLike.congr_fun c.compatible ⟨p, hpO⟩]
  apply congrArg i
  apply congrArg c.right
  apply Subtype.ext
  exact hqp

/-- Source-facing version: the ambient Sylow and Thompson subgroup are the
ones supplied by the marked F.4.33 hypotheses. -/
theorem source_overlap_involution_to_plane
    (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
      (amalgam 1 hn) (G := G0))
    (i : G0 →* G) (hi : Function.Injective i)
    [Finite G]
    (z : pointParabolic 1 hn) (hz : orderOf z = 2)
    (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range)
    {x : G}
    (hx : x ∈ (S0 : Subgroup (overlap 1 hn)).map (i.comp c.middle))
    (hx2 : x ^ 2 = 1) :
    ∃ S : Sylow 2 G, ∃ g : pointParabolic 1 hn,
      (S : Subgroup G) =
        ((projectiveSylow 1 hn).subtype (upperProjective_le_overlap 1 hn) :
          Subgroup (overlap 1 hn)).map (i.comp c.middle) ∧
      i (c.left g) * x * (i (c.left g))⁻¹ ∈ PlainFusion.planeImage c i := by
  obtain ⟨S, hS, hJ⟩ := PlainFusion.completion_thompson c i hi z hz hzroot hc
  obtain ⟨g, hg⟩ := overlap_involution_to_plane c i hi hx hx2
  have hS' := hS.trans (PlainFusion.middle_sylow_image c i).symm
  exact ⟨S, g, hS', hg⟩

end CFSG.Quasithin.ChapterF.UnitaryTwo.InvolutionFusion
