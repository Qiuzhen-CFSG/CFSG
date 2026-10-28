module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OrderComparison
/-!
# The original completion equals its ambient group

The source normalizer and centralizer hypotheses descend through the
original faithful embedding M₀→M. Applying F.4.43 on both groups gives
the same order 25,920, so that very embedding is onto. This is the
M₀=M step in F.4.44; the independent small-completion recognition
theorem then identifies their common group with the unitary model.
-/

open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.CompletionEquality
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open OrderComparison
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
  (amalgam 1 hn) (G := G0)) (i : G0 →* G)

omit [Finite G] in
theorem source_centralizer_descends (hi : Function.Injective i)
    (z : P)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    centralizer ({c.left z} : Set G0) ≤ c.left.range := by
  intro x hx
  have hiC : i x ∈ centralizer ({i (c.left z)} : Set G) :=
    mem_centralizer_singleton_iff.mpr (by
      simpa only [map_mul] using congrArg i (mem_centralizer_singleton_iff.mp hx))
  obtain ⟨p,hp⟩ := hc hiC
  exact ⟨p,hi hp⟩

omit [Finite G] in
theorem source_normalizer_descends (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range) :
    normalizer (PlainFusion.sourcePlaneRootImage c (MonoidHom.id G0) : Set G0) = c.right.range := by
  let Q := PlainFusion.sourcePlaneRootImage c (MonoidHom.id G0)
  have hQ : Q.map i = PlainFusion.sourcePlaneRootImage c i := by
    simp only [Q,PlainFusion.sourcePlaneRootImage,map_map]
    rfl
  have hh : (normalizer (PlainFusion.sourcePlaneRootImage c i : Set G)).comap i = normalizer (Q : Set G0) := by
    rw [← hQ,comap_normalizer_eq_of_le_range (Q.map_le_range i),comap_map_eq_self_of_injective hi]
  rw [hnorm] at hh
  rw [← hh]
  ext x
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,hi hp⟩
  · rintro ⟨p,rfl⟩
    exact ⟨p,rfl⟩

/-- F.4.43 also computes the order of the original completion M₀. -/
theorem completion_order (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    Nat.card G0 = 25920 := by
  let : Finite G0 := Finite.of_injective i hi
  exact source_order c (MonoidHom.id G0) Function.injective_id
    (source_normalizer_descends c i hi hnorm) z hz hzroot
    (source_centralizer_descends c i hi z hc)

/-- The original embedding M₀≤M is onto, as required in F.4.44. -/
theorem source_embedding_surjective (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) :
    Function.Surjective i :=
  ((Nat.bijective_iff_injective_and_card i).mpr ⟨hi,
    (completion_order c i hi hnorm z hz hzroot hc).trans
      (source_order c i hi hnorm z hz hzroot hc).symm⟩).2


/-- The original inclusion becomes an isomorphism, retaining its literal map. -/
def sourceEmbeddingEquiv (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) : G0 ≃* G :=
  MulEquiv.ofBijective i ⟨hi,source_embedding_surjective c i hi hnorm z hz hzroot hc⟩

theorem sourceEmbeddingEquiv_apply (hi : Function.Injective i)
    (hnorm : normalizer (PlainFusion.sourcePlaneRootImage c i : Set G) = (i.comp c.right).range)
    (z : P) (hz : orderOf z = 2) (hzroot : z ∈ PointCore.rootSubgroup)
    (hc : centralizer ({i (c.left z)} : Set G) ≤ (i.comp c.left).range) (g : G0) :
    sourceEmbeddingEquiv c i hi hnorm z hz hzroot hc g = i g := rfl

end CFSG.Quasithin.ChapterF.UnitaryTwo.CompletionEquality
