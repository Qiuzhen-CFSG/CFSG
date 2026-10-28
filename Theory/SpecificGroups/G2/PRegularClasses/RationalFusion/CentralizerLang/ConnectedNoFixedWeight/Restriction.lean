module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.CoordinateModel
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.Peirce
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockModel

/-!
# Regular faithful restriction of the actual centralizer to its Peirce block

For a torus element with no nonconstant fixed weight, its literal closed
centralizer fixes the two diagonal idempotents. Restriction to coordinates
0, 5, 6 is therefore an injective regular map into the diagonal centralizer
in SL₃. Regularity follows from the matrix-entry comparison for the actual
octonion coordinate model. This direction does not yet assert surjectivity,
a regular inverse, or connectedness.

The intended application is the G₂ case of Steinberg 8.5 and 12.5,
`refs/KGroup/GLS3/Chapter2St2.tex`. Coordinate multiplication is inherited
from the licensed ATLAS port (`LICENSES/ATLAS.txt`).
-/

@[expose] public section

open Theory.AlgebraicGroup Atlas.SplitOctonion
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]

/-- Restriction to coordinates 0, 5, 6 is a determinant-one diagonal-centralizing matrix. -/
def centralizerBlockElement (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (g : Subgroup.centralizer ({torus l m} : Set (Model K))) :
    Subgroup.centralizer ({diagonalSL (peirceWeights l m) (peirceWeights_prod l m)} :
      Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  have hf := centralizer_fixes_idempotents l m hl hm hlm g.val g.property
  exact ⟨⟨peirceMatrix g.val, peirceMatrix_det g.val hf.1 hf.2⟩,
    (mem_diagonalSL_centralizer_iff _ _ _).mpr
      (peirceMatrix_weight_relation l m g.val g.property)⟩

def centralizerBlockPoint (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (p : Variety.Point (centralizerVariety (torus l m))) :
    Variety.Point (blockVariety (peirceWeights l m) (peirceWeights_prod l m)) :=
  (blockPointEquiv _ _).symm
    (centralizerBlockElement l m hl hm hlm (centralizerPointEquiv (torus l m) p))

theorem centralizerBlockPoint_entry (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (p : Variety.Point (centralizerVariety (torus l m))) (i j : Fin 3) :
    (centralizerBlockPoint l m hl hm hlm p).val (ULift.up (i,j)) =
      p.val (Sum.inl (peirceIndex i,peirceIndex j)) := by
  rw [← blockPointEquiv_entry]
  change ((blockPointEquiv _ _ ((blockPointEquiv _ _).symm
      (centralizerBlockElement l m hl hm hlm (centralizerPointEquiv (torus l m) p)))).val :
        Matrix (Fin 3) (Fin 3) K) i j = _
  rw [MulEquiv.apply_symm_apply]
  change peirceMatrix (centralizerPointEquiv (torus l m) p).val i j = _
  simpa only [peirceMatrix, coordinateMatrix_entry] using
    centralizerPointEquiv_entry (torus l m) p (peirceIndex i) (peirceIndex j)

/-- The literal coordinate projection to the three-dimensional action is regular. -/
def centralizerRestriction (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m) :
    Variety.Morphism (centralizerVariety (torus l m))
      (blockVariety (peirceWeights l m) (peirceWeights_prod l m)) where
  toFun := centralizerBlockPoint l m hl hm hlm
  regular := by
    rintro ⟨⟨i,j⟩⟩
    refine ⟨MvPolynomial.X (Sum.inl (peirceIndex i,peirceIndex j)), ?_⟩
    intro p
    rw [centralizerBlockPoint_entry, evalPolynomial_X]

theorem centralizerRestriction_injective (l m : Kˣ)
    (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m) :
    Function.Injective (centralizerRestriction l m hl hm hlm).toFun := by
  intro p q he
  have hmat := congrArg (fun a => ((blockPointEquiv (peirceWeights l m)
    (peirceWeights_prod l m) a).val : Matrix (Fin 3) (Fin 3) K)) he
  change peirceMatrix (centralizerPointEquiv (torus l m) p).val =
    peirceMatrix (centralizerPointEquiv (torus l m) q).val at hmat
  apply (centralizerPointEquiv (torus l m)).injective
  apply Subtype.ext
  have hp := centralizer_fixes_idempotents l m hl hm hlm
    (centralizerPointEquiv (torus l m) p).val (centralizerPointEquiv (torus l m) p).property
  have hq := centralizer_fixes_idempotents l m hl hm hlm
    (centralizerPointEquiv (torus l m) q).val (centralizerPointEquiv (torus l m) q).property
  exact peirceMatrix_injective_on_fixers _ _ hp.1 hp.2 hq.1 hq.2 hmat

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
