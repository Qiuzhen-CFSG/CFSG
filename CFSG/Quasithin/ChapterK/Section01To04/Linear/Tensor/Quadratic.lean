module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Quadratic.Sylow
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Quadratic.Radicals
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Ratios

/-!
# Inner quadratic actors on the Hermitian tensor

Every elementary inner actor is conjugate into the image of the standard
unitriangular subgroup. Quadraticity and binary rank survive conjugation,
so the two explicit radical calculations give rank at most n. The marking
is constructed from the actual SL₃ Sylow image and extended to the source
overgroup; no faithful-cover assumption is made for odd n.

The application to the existing quadratic-ratio assembly discharges its
inner-rank premise. The earlier root-dimension input and the independent
outer-actor exclusion remain explicit with the parent assembly owner.
This module also exports the genuine marked-Sylow witness used by the
minimizing-actor theorem.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.4,
printed pp.455–456/PDF pp.466–467.
-/

public section

open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.BinaryOffender
open scoped ENNReal
noncomputable section
namespace CFSG.Quasithin.ChapterK.Linear.Tensor

private theorem quadratic_conjugate {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    {A : Subgroup G} (hA : IsQuadratic ρ A) (g : G) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h

variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
include hM

/-- The inner quadratic rank bound, with the actual source-overgroup hypothesis. -/
theorem inner_quadratic_rank_le (A : Subgroup M) (hA : IsElementaryTwo A)
    (hAI : A ≤ innerActor n M) (hq : IsQuadratic (overgroupAction n M) A) :
    rank A ≤ n := by
  obtain ⟨g,hg⟩ := elementary_conjugate_le_unipotent n M hM A hA hAI
  have hb := quadratic_rank_le_of_le_unipotent n M hM
    (A.map (MulAut.conj g).toMonoidHom) (hA.map_conj g) hg (quadratic_conjugate hq g)
  simpa only [rank_map_conj] using hb

/-- Apply the rank bound to the literal ratio theorem; only the earlier root
dimension and independent outer-action inputs remain for the parent. -/
theorem quadraticRatio_gt_two_of_root_and_outer
    (hroot : InnerRootDimensions n M)
    (houter : ∀ A : Subgroup M, IsElementaryTwo A → IsQuadratic (overgroupAction n M) A →
      actionRatio (overgroupAction n M) A ≤ 2 → A ≤ innerActor n M) :
    2 < quadraticRatio (overgroupAction n M) :=
  quadraticRatio_gt_two_of_inner_rank n M hroot houter (inner_quadratic_rank_le n M hM)

end CFSG.Quasithin.ChapterK.Linear.Tensor
