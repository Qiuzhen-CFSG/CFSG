module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.LinearCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Removing the marked original linear extension

The input marks original endpoints in Aut(PSL₃(F)), their solvable
residuals, their intersections with the inner group, and the entire common
Borel. It permits outer automorphisms in both endpoints and does not assume
a pure-model comparison or a local-core equality.

Perfectness identifies the original L and selected R with the marked
residuals. The normalized right Borel gives S ≤ R by `LinearCore`.
Agreement on the full overlap then puts both source Borels and S inside
the inner images. Generation removes the outer parts of both endpoints.
Restricting the original three maps through the faithful inner embedding
constructs both inclusion squares, in either orientation. The existing
local comparison fixes the field exponent to n > 1 and identifies both
original natural blocks.

This proves the conditional original-extension reduction for the linear
row, for every preparation and perfect selected R. Construction of the
marked original extension belongs to the shared DGS source assembly;
the other rows and final GlobalExit assembly remain separate obligations.

Source: Aschbacher–Smith F.1.12, printed pp.263–264, and 5.2.6,
printed pp.650–651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalLinear
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.RootPlaneGeometry

variable {G : Type*} [Group G] (L R S : Subgroup G)
  (F : Type) [Field F] [Finite F] (point : Bool)

/-- Marked original extension data. Only intersections with the inner group
are identified with native parabolics; the original endpoints may contain
outer automorphisms. Residual marks and the entire overlap are retained. -/
structure Marking where
  left : ChapterF.Source.parabolic ![L,R] S 0 →* MulAut PSL(3,F)
  right : ChapterF.Source.parabolic ![L,R] S 1 →* MulAut PSL(3,F)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  agrees : ∀ x, left ((sourceParabolicAmalgam ![L,R] S).left x) =
    right ((sourceParabolicAmalgam ![L,R] S).right x)
  left_residual : (solvableResidual (ChapterF.Source.parabolic ![L,R] S 0)).map left =
    (localFactor F point).map MulAut.conj
  right_residual : (solvableResidual (ChapterF.Source.parabolic ![L,R] S 1)).map right =
    (localFactor F (!point)).map MulAut.conj
  left_base : left.range ⊓ MulAut.innerSubgroup PSL(3,F) =
    (parabolic F point).map MulAut.conj
  right_base : right.range ⊓ MulAut.innerSubgroup PSL(3,F) =
    (parabolic F (!point)).map MulAut.conj
  whole_overlap : (left.comp (sourceParabolicAmalgam ![L,R] S).left).range =
    left.range ⊓ right.range

end OriginalLinear

namespace Preparation
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.RootPlaneGeometry
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (e : OriginalLinear.Marking L R (sourceS L H) F point)

include d h hTH hp in
private theorem local_eq_residual (i : Fin 2) :
    (![L,R] i).subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) =
      solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) := by
  apply Subgroup.map_injective (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype_injective
  rw [d.parabolic_residuals h hTH hp i,
    map_subgroupOf_eq_of_le (show ![L,R] i ≤ ChapterF.Source.parabolic ![L,R] (sourceS L H) i
      from le_sup_left.trans le_sup_left)]

include d h hTH hp hm hF e in
/-- The literal marked original linear row contains S in the selected R. -/
theorem sourceS_le_right_of_original_linear : sourceS L H ≤ R := by
  apply d.sourceS_le_right_of_linear_extension h hTH F hm hF (!point)
    e.right e.right_injective
  have he := d.local_eq_residual h hTH hp 1
  change R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) = _ at he
  rw [he]
  exact e.right_residual

include d h hTH hp hm hF in
/-- Both ORIGINAL full endpoints are inner. The proof transfers S and both
odd Borels across the same full-overlap square before using generation. -/
theorem original_linear_endpoints_inner :
    e.left.range ≤ MulAut.innerSubgroup PSL(3,F) ∧
    e.right.range ≤ MulAut.innerSubgroup PSL(3,F) := by
  let P₀ := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  let P₁ := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  let I := MulAut.innerSubgroup PSL(3,F)
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
      ((d.local_eq_residual h hTH hp 0).le (show (⟨x,hL₀ hx⟩ : P₀) ∈ L.subgroupOf P₀ from hx)))
    exact (Subgroup.map_le_range _ _) he
  have hR : R ≤ K₁ := by
    intro x hx
    refine ⟨⟨x,hR₁ hx⟩,?_,rfl⟩
    change e.right ⟨x,hR₁ hx⟩ ∈ I
    have he := e.right_residual ▸ (mem_map_of_mem e.right
      ((d.local_eq_residual h hTH hp 1).le (show (⟨x,hR₁ hx⟩ : P₁) ∈ R.subgroupOf P₁ from hx)))
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
    (d.sourceS_le_right_of_original_linear h hTH hp F hm hF point e).trans hR
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


namespace OriginalLinear
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
variable (F : Type) [Field F] [Finite F]

private def restrictEndpoint {X : Type*} [Group X]
    (f : X →* MulAut PSL(3,F)) (hf : Function.Injective f)
    (P : Subgroup PSL(3,F)) (he : f.range = P.map MulAut.conj) : X ≃* P :=
  (MonoidHom.ofInjective hf).trans ((MulEquiv.subgroupCongr he).trans
    (P.equivMapOfInjective MulAut.conj (Matrix.PSL3.ExtensionBorel.inner_injective F)).symm)

omit [Finite F] in
private theorem restrictEndpoint_apply {X : Type*} [Group X]
    (f : X →* MulAut PSL(3,F)) (hf : Function.Injective f)
    (P : Subgroup PSL(3,F)) (he : f.range = P.map MulAut.conj) (x : X) :
    MulAut.conj (restrictEndpoint F f hf P he x).val = f x := by
  exact congrArg Subtype.val ((P.equivMapOfInjective MulAut.conj
    (Matrix.PSL3.ExtensionBorel.inner_injective F)).apply_symm_apply
      ((MulEquiv.subgroupCongr he) (MonoidHom.ofInjective hf x)))

omit [Finite F] in
private theorem borel_le_side (point : Bool) : borel F ≤ parabolic F point := by
  cases point
  · exact ChapterF.GreenBook.LieModels.LinearThree.borel_le_line F
  · exact ChapterF.GreenBook.LieModels.LinearThree.borel_le_point F

/-- The native inclusion amalgam, with its two possible literal orientations. -/
@[expose] def orientedAmalgam (point : Bool) :
    RankTwoAmalgam (parabolic F point) (borel F) (parabolic F (!point)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (by exact borel_le_side F point) (by exact borel_le_side F (!point))

variable {G : Type*} [Group G] {L R S : Subgroup G} {point : Bool}

/-- Restrict BOTH endpoint maps and their full common overlap through the
faithful inner embedding once their outer parts have been eliminated. -/
def Marking.restrict (e : Marking L R S F point)
    (hi : e.left.range ≤ MulAut.innerSubgroup PSL(3,F) ∧
      e.right.range ≤ MulAut.innerSubgroup PSL(3,F)) :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] S) (orientedAmalgam F point) := by
  have hl : e.left.range = (parabolic F point).map MulAut.conj := by
    simpa only [inf_eq_left.mpr hi.1] using e.left_base
  have hr : e.right.range = (parabolic F (!point)).map MulAut.conj := by
    simpa only [inf_eq_left.mpr hi.2] using e.right_base
  let fm := e.left.comp (sourceParabolicAmalgam ![L,R] S).left
  have hfm : Function.Injective fm := e.left_injective.comp (inclusion_injective inf_le_left)
  have hm : fm.range = (borel F).map MulAut.conj := by
    rw [e.whole_overlap,hl,hr,← Subgroup.map_inf _ _ _ (Matrix.PSL3.ExtensionBorel.inner_injective F)]
    congr 1
    cases point
    · change lineParabolic F ⊓ pointParabolic F = borel F
      rw [inf_comm]
      exact ChapterF.GreenBook.LieModels.LinearThree.parabolic_intersection F
    · exact ChapterF.GreenBook.LieModels.LinearThree.parabolic_intersection F
  refine { left := restrictEndpoint F e.left e.left_injective _ hl
           middle := restrictEndpoint F fm hfm _ hm
           right := restrictEndpoint F e.right e.right_injective _ hr
           left_commutes := ?_
           right_commutes := ?_ }
  · intro x
    apply Subtype.ext
    apply Matrix.PSL3.ExtensionBorel.inner_injective F
    exact (restrictEndpoint_apply F e.left e.left_injective _ hl _).trans
      (restrictEndpoint_apply F fm hfm _ hm x).symm
  · intro x
    apply Subtype.ext
    apply Matrix.PSL3.ExtensionBorel.inner_injective F
    exact (restrictEndpoint_apply F e.right e.right_injective _ hr _).trans
      ((e.agrees x).symm.trans (restrictEndpoint_apply F fm hfm _ hm x).symm)

end OriginalLinear

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (e : OriginalLinear.Marking L R (sourceS L H) F point)
include d h hTH hp hm hF e

/-- The original-extension linear row yields a pure comparison in its
original orientation, with both full-Borel squares proved. -/
def originalLinearComparison :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (OriginalLinear.orientedAmalgam F point) :=
  e.restrict F (d.original_linear_endpoints_inner h hTH hp F hm hF point e)

/-- The literal consumer catalogue is constructed from the BROAD marked
original linear extension, rather than assumed as an input. -/
theorem concreteComparison_of_original_linear :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  apply ConcreteAmalgamComparison.linear F m hm hF
  have he := d.originalLinearComparison h hTH hp F hm hF point e
  cases point
  · exact Or.inr ⟨he⟩
  · exact Or.inl ⟨he⟩

end Preparation


namespace OriginalLinear
open scoped MatrixGroups
variable (F : Type) [Field F] [Finite F]
  {G : Type*} [Group G] {L R S : Subgroup G} {point : Bool}
  (e : Marking L R S F point)
  (hi : e.left.range ≤ MulAut.innerSubgroup PSL(3,F) ∧
    e.right.range ≤ MulAut.innerSubgroup PSL(3,F))

/-- The restricted left endpoint realizes the original automorphism marking. -/
theorem Marking.restrict_left_apply (x : ChapterF.Source.parabolic ![L,R] S 0) :
    MulAut.conj ((e.restrict F hi).left x).val = e.left x :=
  restrictEndpoint_apply F e.left e.left_injective _ _ x

/-- The restricted right endpoint realizes the original automorphism marking. -/
theorem Marking.restrict_right_apply (x : ChapterF.Source.parabolic ![L,R] S 1) :
    MulAut.conj ((e.restrict F hi).right x).val = e.right x :=
  restrictEndpoint_apply F e.right e.right_injective _ _ x

/-- The entire middle, including both odd Cartans, retains its original mark. -/
theorem Marking.restrict_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] S 0 ⊓ ChapterF.Source.parabolic ![L,R] S 1 : Subgroup G)) :
    MulAut.conj ((e.restrict F hi).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] S).left x) :=
  restrictEndpoint_apply F _ _ _ _ x

end OriginalLinear

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (e : OriginalLinear.Marking L R (sourceS L H) F point)
include d h hTH hp hm hF e

/-- The constructed comparison has the original nonbinary exponent and
both original natural local factors. In particular the binary row is excluded. -/
theorem original_linear_field_and_blocks :
    m = n ∧ 1 < m ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n := by
  have he := d.originalLinearComparison h hTH hp F hm hF point e
  have hc : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,R] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse) := by
    cases point
    · exact Or.inr ⟨he⟩
    · exact Or.inl ⟨he⟩
  obtain ⟨hmn,hL,hR⟩ := d.linear_amalgam_blocks h hTH hp F hm hF hc
  exact ⟨hmn, hmn ▸ h.exponent, hL,hR⟩

end Preparation

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
