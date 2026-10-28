module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryPlane
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Restricting original extension markings through the full Borel

The original source endpoints embed compatibly in an automorphism group.
Their residuals mark the native local factors, while their intersections with
the inner group mark the native parabolics. If the original S lies in the
selected right residual, then S and both source Borels have inner images.
Generation therefore makes both full endpoints inner. Restriction through the
faithful inner embedding preserves all three original maps and both squares.

This is the common transport in the normalized-Borel deduction of F.1.12,
printed p.264 of Aschbacher--Smith (`refs/quasithin.pdf`). The triality
application supplies S ≤ R using its native core calculation and the original
normalized right Borel. The shared DGS source producer still owns construction
of the broad markings; this module does not assert exhaustive recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalExtension
variable {G X : Type*} [Group G] [Group X]
  (L R S : Subgroup G) (K₀ K₁ P₀ P₁ : Subgroup X)

/-- Original endpoint and full-overlap markings in the automorphism group.
Only intersection with the inner group is identified with the native parabolic. -/
structure Marking where
  left : ChapterF.Source.parabolic ![L,R] S 0 →* MulAut X
  right : ChapterF.Source.parabolic ![L,R] S 1 →* MulAut X
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  agrees : ∀ x, left ((sourceParabolicAmalgam ![L,R] S).left x) =
    right ((sourceParabolicAmalgam ![L,R] S).right x)
  left_residual : (solvableResidual (ChapterF.Source.parabolic ![L,R] S 0)).map left =
    K₀.map MulAut.conj
  right_residual : (solvableResidual (ChapterF.Source.parabolic ![L,R] S 1)).map right =
    K₁.map MulAut.conj
  left_base : left.range ⊓ MulAut.innerSubgroup X = P₀.map MulAut.conj
  right_base : right.range ⊓ MulAut.innerSubgroup X = P₁.map MulAut.conj
  whole_overlap : (left.comp (sourceParabolicAmalgam ![L,R] S).left).range =
    left.range ⊓ right.range
end OriginalExtension

namespace Preparation
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  {K₀ K₁ Q₀ Q₁ : Subgroup X}
  (e : OriginalExtension.Marking L R (sourceS L H) K₀ K₁ Q₀ Q₁)

include d h hTH hp in
theorem original_local_eq_residual (i : Fin 2) :
    (![L,R] i).subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) =
      solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) := by
  apply Subgroup.map_injective (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype_injective
  rw [d.parabolic_residuals h hTH hp i,
    map_subgroupOf_eq_of_le (show ![L,R] i ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i
      from le_sup_left.trans le_sup_left)]

include d h hTH hp in
/-- Both ORIGINAL full endpoints are inner. The proof transfers S and both
odd Borels across the same full-overlap square before using generation. -/
theorem original_extension_endpoints_inner (hSR : sourceS L H ≤ R) :
    e.left.range ≤ MulAut.innerSubgroup X ∧
    e.right.range ≤ MulAut.innerSubgroup X := by
  let P₀ := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  let P₁ := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let I := MulAut.innerSubgroup X
  let K₀ := (I.comap e.left).map P₀.subtype
  let K₁ := (I.comap e.right).map P₁.subtype
  have hL₀ : L ≤ P₀ := le_sup_left.trans le_sup_left
  have hR₁ : R ≤ P₁ := le_sup_left.trans le_sup_left
  have hS₀ : sourceS L H ≤ P₀ := le_sup_right.trans le_sup_left
  have hS₁ : sourceS L H ≤ P₁ := le_sup_right.trans le_sup_left
  have hL : L ≤ K₀ := by
    intro x hx
    refine ⟨⟨x,hL₀ hx⟩,?_,rfl⟩
    change e.left ⟨x,hL₀ hx⟩ ∈ I
    have he := e.left_residual ▸ (mem_map_of_mem e.left
      ((d.original_local_eq_residual h hTH hp 0).le (show (⟨x,hL₀ hx⟩ : P₀) ∈ L.subgroupOf P₀ from hx)))
    exact (Subgroup.map_le_range _ _) he
  have hR : R ≤ K₁ := by
    intro x hx
    refine ⟨⟨x,hR₁ hx⟩,?_,rfl⟩
    change e.right ⟨x,hR₁ hx⟩ ∈ I
    have he := e.right_residual ▸ (mem_map_of_mem e.right
      ((d.original_local_eq_residual h hTH hp 1).le (show (⟨x,hR₁ hx⟩ : P₁) ∈ R.subgroupOf P₁ from hx)))
    exact (Subgroup.map_le_range _ _) he
  have hsame (x : (P₀ ⊓ P₁ : Subgroup G)) : (x : G) ∈ K₀ ↔ (x : G) ∈ K₁ := by
    change (x : G) ∈ (I.comap e.left).map P₀.subtype ↔
      (x : G) ∈ (I.comap e.right).map P₁.subtype
    change P₀.subtype ⟨x,x.property.1⟩ ∈ (I.comap e.left).map P₀.subtype ↔
      P₁.subtype ⟨x,x.property.2⟩ ∈ (I.comap e.right).map P₁.subtype
    rw [mem_map_iff_mem P₀.subtype_injective,mem_map_iff_mem P₁.subtype_injective]
    change e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) ∈ I ↔
      e.right ((sourceParabolicAmalgam ![L,R] (sourceS L H)).right x) ∈ I
    rw [e.agrees]
  have hs : sourceS L H ≤ K₁ :=
    hSR.trans hR
  have hs' : sourceS L H ≤ K₀ := fun x hx =>
    (hsame ⟨x,hS₀ hx,hS₁ hx⟩).mpr (hs hx)
  have hbR₀ : ChapterF.Source.borel R (sourceS L H) ≤ P₀ := le_sup_right
  have hbL₁ : ChapterF.Source.borel L (sourceS L H) ≤ P₁ := le_sup_right
  have hbR : ChapterF.Source.borel R (sourceS L H) ≤ K₀ := fun x hx =>
    (hsame ⟨x,hbR₀ hx,hR₁ hx.1⟩).mpr (hR hx.1)
  have hbL : ChapterF.Source.borel L (sourceS L H) ≤ K₁ := fun x hx =>
    (hsame ⟨x,hL₀ hx.1,hbL₁ hx⟩).mp (hL hx.1)
  have hP₀ : P₀ ≤ K₀ := sup_le (sup_le hL hs') hbR
  have hP₁ : P₁ ≤ K₁ := sup_le (sup_le hR hs) hbL
  constructor
  · rintro _ ⟨x,rfl⟩
    exact (mem_map_iff_mem P₀.subtype_injective).mp (hP₀ x.property)
  · rintro _ ⟨x,rfl⟩
    exact (mem_map_iff_mem P₁.subtype_injective).mp (hP₁ x.property)

end Preparation
namespace OriginalExtension
variable {X : Type*} [Group X] (hi : Function.Injective (MulAut.conj : X →* MulAut X))

private def restrictEndpoint {Y : Type*} [Group Y]
    (f : Y →* MulAut X) (hf : Function.Injective f)
    (P : Subgroup X) (he : f.range = P.map MulAut.conj) : Y ≃* P :=
  (MonoidHom.ofInjective hf).trans ((MulEquiv.subgroupCongr he).trans
    (P.equivMapOfInjective MulAut.conj hi).symm)

private theorem restrictEndpoint_apply {Y : Type*} [Group Y]
    (f : Y →* MulAut X) (hf : Function.Injective f)
    (P : Subgroup X) (he : f.range = P.map MulAut.conj) (x : Y) :
    MulAut.conj (restrictEndpoint hi f hf P he x).val = f x := by
  exact congrArg Subtype.val ((P.equivMapOfInjective MulAut.conj hi).apply_symm_apply
      ((MulEquiv.subgroupCongr he) (MonoidHom.ofInjective hf x)))

variable {G : Type*} [Group G] {L R S : Subgroup G} {K₀ K₁ P₀ P₁ : Subgroup X}

/-- Restrict the two endpoint maps and their whole intersection through the
faithful inner embedding. Both squares retain the original markings. -/
def Marking.restrict (e : Marking L R S K₀ K₁ P₀ P₁)
    (hbase : e.left.range ≤ MulAut.innerSubgroup X ∧
      e.right.range ≤ MulAut.innerSubgroup X) :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] S)
      (RankTwoAmalgam.ofSubgroups P₀ (P₀ ⊓ P₁) P₁ inf_le_left inf_le_right) := by
  have hl : e.left.range = P₀.map MulAut.conj := by
    simpa only [inf_eq_left.mpr hbase.1] using e.left_base
  have hr : e.right.range = P₁.map MulAut.conj := by
    simpa only [inf_eq_left.mpr hbase.2] using e.right_base
  let fm := e.left.comp (sourceParabolicAmalgam ![L,R] S).left
  have hfm : Function.Injective fm := e.left_injective.comp (inclusion_injective inf_le_left)
  have hm : fm.range = (P₀ ⊓ P₁).map MulAut.conj := by
    rw [e.whole_overlap,hl,hr,Subgroup.map_inf _ _ _ hi]
  refine { left := restrictEndpoint hi e.left e.left_injective _ hl
           middle := restrictEndpoint hi fm hfm _ hm
           right := restrictEndpoint hi e.right e.right_injective _ hr
           left_commutes := ?_
           right_commutes := ?_ }
  · intro x
    apply Subtype.ext
    apply hi
    exact (restrictEndpoint_apply hi e.left e.left_injective _ hl _).trans
      (restrictEndpoint_apply hi fm hfm _ hm x).symm
  · intro x
    apply Subtype.ext
    apply hi
    exact (restrictEndpoint_apply hi e.right e.right_injective _ hr _).trans
      ((e.agrees x).symm.trans (restrictEndpoint_apply hi fm hfm _ hm x).symm)

variable (e : Marking L R S K₀ K₁ P₀ P₁)
    (hbase : e.left.range ≤ MulAut.innerSubgroup X ∧
      e.right.range ≤ MulAut.innerSubgroup X)

/-- Restriction realizes the original left marking. -/
theorem Marking.restrict_left_apply (x : ChapterF.Source.parabolic ![L,R] S 0) :
    MulAut.conj ((e.restrict hi hbase).left x).val = e.left x :=
  restrictEndpoint_apply hi e.left e.left_injective _ _ x

/-- Restriction realizes the original right marking. -/
theorem Marking.restrict_right_apply (x : ChapterF.Source.parabolic ![L,R] S 1) :
    MulAut.conj ((e.restrict hi hbase).right x).val = e.right x :=
  restrictEndpoint_apply hi e.right e.right_injective _ _ x

/-- Restriction retains every element of the full common Borel. -/
theorem Marking.restrict_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] S 0 ⊓ ChapterF.Source.parabolic ![L,R] S 1 : Subgroup G)) :
    MulAut.conj ((e.restrict hi hbase).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] S).left x) :=
  restrictEndpoint_apply hi _ _ _ _ x
end OriginalExtension
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
