module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Centralizer.ElementaryIndex.MatrixFactorization
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualEquality
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Standard

/-!+# The split orthogonal eight-space calculation for triality

Split the natural eight-space into two determinant four-spaces. The left SL₂
on the first summand has a commuting right SL₂ and two SL₂ factors on the
second summand. The existing orthogonal residual theorem, including the
split-four endpoint, puts every defining-characteristic element of the left
centralizer in this three-factor image. The scalar quotients are the literal
ones of `ClassicalOrthogonal`; no injectivity of the product is asserted.

`MarkedComparison` states the separate comparison needed to apply this result
to the Geck group: a faithful homomorphism identifying the highest-root and
the three numbered arm subgroups. It contains no centralizer or factorization
assertion. Constructing this homomorphism remains a separate obligation.

Sources: GLS3 §§2.6–2.7 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith A.2.17, printed p.39, (*) and the triality case.
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent

namespace OrthogonalModel
open ClassicalOrthogonal ClassicalOrthogonal.Fundamental
open ClassicalOrthogonal.Fundamental.SplitOddBlocks
variable {F : Type*} [Field F]

/-- The marked left factor on the first determinant four-space. -/
def highest : SL(2, F) →* POmegaPlus 4 F :=
  leftProjective (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm

/-- Combine the two factors on the second determinant four-space. -/
def toRightFactors : (SL(2, F) × SL(2, F)) × SL(2, F) →*
    SL(2, F) × OmegaPlus 2 F :=
  ((MonoidHom.id _).prodMap
    (fourMap.comp (MulEquiv.prodComm : SL(2, F) × SL(2, F) ≃*
      SL(2, F) × SL(2, F)).toMonoidHom)).comp
      (MulEquiv.prodAssoc : (SL(2, F) × SL(2, F)) × SL(2, F) ≃*
        SL(2, F) × (SL(2, F) × SL(2, F))).toMonoidHom

/-- The three commuting factors, in the order corresponding to arms 0, 2, 3. -/
def arms : (SL(2, F) × SL(2, F)) × SL(2, F) →* POmegaPlus 4 F :=
  (rightProjective (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm).comp
    toRightFactors

def armZero : SL(2, F) →* POmegaPlus 4 F :=
  arms.comp ((MonoidHom.inl _ _).comp (MonoidHom.inl _ _))

def armTwo : SL(2, F) →* POmegaPlus 4 F :=
  arms.comp ((MonoidHom.inl _ _).comp (MonoidHom.inr _ _))

def armThree : SL(2, F) →* POmegaPlus 4 F := arms.comp (MonoidHom.inr _ _)

theorem arms_apply (a b c : SL(2, F)) :
    arms ((a, b), c) = armZero a * armTwo b * armThree c := by
  change arms ((a, b), c) = arms ((a, 1), 1) * arms ((1, b), 1) * arms ((1, 1), c)
  rw [← map_mul, ← map_mul]
  simp

/-- Defining-characteristic elements in the actual projective orthogonal
centralizer factor through the three marked SL₂ maps, including in characteristic three. -/
theorem p_element_mem_arms [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2)
    (g : Subgroup.centralizer ((highest (F := F)).range : Set (POmegaPlus 4 F)))
    (n : ℕ) (hg : g ^ (p ^ n) = 1) : g.val ∈ (arms (F := F)).range := by
  have hres := Subgroup.mem_primeToResidual_of_pow hg
  have heq := rightProjective_range_eq_residual_of_index p hp
    (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm
    (IsometryQuotients.elementary_index_coprime_formD p hp 2 (by decide))
  have hmem : g.val ∈
      (rightProjective (formD 2 F) (formD 4 F) (splitDIsometry 2 2).symm).range := by
    rw [heq]
    exact ⟨g, hres, rfl⟩
  obtain ⟨⟨a, b⟩, hb⟩ := hmem
  obtain ⟨⟨c, d⟩, rfl⟩ := fourMap_surjective b
  exact ⟨((a, d), c), hb⟩

end OrthogonalModel

open Parabolics
variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- The full highest-root SL₂, with the same conjugation as `highestCurve`. -/
def highestHom : SL(2, ExtensionField P) →* SplitGroup P :=
  (MulAut.conj (splitHighestWeyl D C)).toMonoidHom.comp (D.hom 1)

/-- An explicit model-comparison obligation. Each of the four named subgroup
images must be proved for the genuine Geck group. No centralizer identification,
order formula, factorization, or injectivity of the three-arm product is a field. -/
structure MarkedComparison where
  hom : SplitGroup P →* ClassicalOrthogonal.POmegaPlus 4 (ExtensionField P)
  injective : Function.Injective hom
  highest_range : (hom.comp (highestHom D C)).range = OrthogonalModel.highest.range
  armZero_range : (hom.comp (D.hom 0)).range = OrthogonalModel.armZero.range
  armTwo_range : (hom.comp (D.hom 2)).range = OrthogonalModel.armTwo.range
  armThree_range : (hom.comp (D.hom 3)).range = OrthogonalModel.armThree.range

/-- The three separate subgroup markings identify their ordered product images.
No uniqueness of a factorization is required. -/
theorem MarkedComparison.arms_range (E : MarkedComparison D C) :
    (E.hom.comp (D.armsProduct C)).range = OrthogonalModel.arms.range := by
  apply le_antisymm
  · rintro _ ⟨⟨⟨a, b⟩, c⟩, rfl⟩
    obtain ⟨x, hx⟩ := E.armZero_range.le ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := E.armTwo_range.le ⟨b, rfl⟩
    obtain ⟨z, hz⟩ := E.armThree_range.le ⟨c, rfl⟩
    refine ⟨((x, y), z), ?_⟩
    simp only [OrthogonalModel.arms_apply, hx, hy, hz, MonoidHom.comp_apply,
      PinnedRankOneMaps.armsProduct_apply, map_mul]
  · rintro _ ⟨⟨⟨x, y⟩, z⟩, rfl⟩
    obtain ⟨a, ha⟩ := E.armZero_range.ge ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := E.armTwo_range.ge ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := E.armThree_range.ge ⟨z, rfl⟩
    refine ⟨((a, b), c), ?_⟩
    simpa only [OrthogonalModel.arms_apply, MonoidHom.comp_apply,
      PinnedRankOneMaps.armsProduct_apply, map_mul] using
      congrArg₂ (· * ·) (congrArg₂ (· * ·) ha hb) hc

end Triality.Standard.OddFundamentalCentralizer.ElementaryIndex.HighestUnipotent
