module

public import Theory.AlgebraicGroup.RootSubgroups.BinaryCorootWord
public import Theory.AlgebraicGroup.RootSubgroups.OppositePairSL2Recognition

/-!
# Source-convention SL₂ charts for opposite root subgroups

The upper and lower SL₂ curves give the regular word `n(1)⁻¹n(t)`.
A two-by-two matrix calculation identifies it with `diag(t⁻¹,t)` in
characteristic two and proves its multiplicativity. Naturality transports
this word through a regular SL₂ morphism compatible with two specified
one-parameter subgroups.

A chart additionally requires containment of that diagonal image in a
specified torus. Restricting the morphism then constructs a torus cocharacter
and identifies its inclusion with the word in the actual curves. Cartan
normalization remains a separate geometric assertion.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6 and the defining formulas of
Theorem 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k]
/-- Regular coroot words commute with algebraic-group morphisms. -/
theorem binaryCorootWord_map {H G : Variety k} [AlgebraicGroup H] [AlgebraicGroup G]
    (φ : Morphism H G) (x y : Variety.Morphism (KPlus k) H)
    (t : Variety.Point (KMult k)) :
    φ.onPoints ((binaryCorootWord x y).toFun t) =
      (binaryCorootWord (φ.toVariety.comp x) (φ.toVariety.comp y)).toFun t := by
  rw [binaryCorootWord_apply, binaryCorootWord_apply]
  simp only [map_mul, map_inv]
  rfl

variable [IsAlgClosed k]
/-- A compatible rank-one morphism transports the source-convention word
to the actual parametrized opposite root subgroups. -/
theorem OppositePairSL2Compatible.binaryCorootWord_eq {G : Variety k} [AlgebraicGroup G]
    (X Y : ClosedSubgroup G)
    (xp : OneParameterParametrization X.carrierVariety)
    (xm : OneParameterParametrization Y.carrierVariety)
    (f : Morphism (slVariety k 2) (oppositePairGeneratedSubgroup X Y).carrierVariety)
    (hf : OppositePairSL2Compatible X Y xp xm f)
    (t : Variety.Point (KMult k)) :
    (binaryCorootWord ((X.inclusion.comp xp.hom).toVariety)
      ((Y.inclusion.comp xm.hom).toVariety)).toFun t =
        (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
          (f.onPoints ((binaryCorootWord standardSL2UpperMorphism.toVariety
            standardSL2LowerMorphism.toVariety).toFun t)) := by
  let q := (oppositePairGeneratedSubgroup X Y).inclusion.comp f
  have hp : q.comp standardSL2UpperMorphism = X.inclusion.comp xp.hom := by
    apply Morphism.ext
    funext s
    change (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      ((f.comp standardSL2UpperMorphism).onPoints s) = _
    rw [← hf.1]
    exact oppositePairPlusMorphism_inclusion_apply X Y (xp.hom.onPoints s)
  have hm : q.comp standardSL2LowerMorphism = Y.inclusion.comp xm.hom := by
    apply Morphism.ext
    funext s
    change (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      ((f.comp standardSL2LowerMorphism).onPoints s) = _
    rw [← hf.2]
    exact oppositePairMinusMorphism_inclusion_apply X Y (xm.hom.onPoints s)
  have h := binaryCorootWord_map q standardSL2UpperMorphism.toVariety standardSL2LowerMorphism.toVariety t
  change q.onPoints _ = (binaryCorootWord (q.comp standardSL2UpperMorphism).toVariety
    (q.comp standardSL2LowerMorphism).toVariety).toFun t at h
  rw [hp, hm] at h
  exact h.symm
end Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]
private noncomputable def binarySL2Word : Variety.Morphism (KMult k) (slVariety k 2) :=
  binaryCorootWord standardSL2UpperMorphism.toVariety standardSL2LowerMorphism.toVariety
variable [CharP k 2]

private theorem binarySL2Word_matrix (t : Variety.Point (KMult k)) :
    slPointMatrix 2 ((binarySL2Word (k := k)).toFun t) =
        Matrix.diagonal (fun i : Fin 2 => if i = 0 then
          (dPointEquiv 1 t 0 : k)⁻¹ else (dPointEquiv 1 t 0 : k)) := by
  have hmatrix (x : Variety.Point (slVariety k 2)) :
      slPointMatrix 2 x = ((slPointMulEquiv 2) x).val := by
    rw [slPointMulEquiv_apply]
    rfl
  rw [hmatrix]
  change ((slPointMulEquiv 2) ((binaryCorootWord _ _).toFun t)).val = _
  rw [binaryCorootWord_apply]
  simp only [map_mul, map_inv, slPointMulEquiv_apply]
  change ((Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : k) *
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1 *
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1)⁻¹ *
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (dPointEquiv 1 t 0 : k) *
    Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (dPointEquiv 1 t 0 : k)⁻¹ *
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (dPointEquiv 1 t 0 : k)) :
    Matrix.SpecialLinearGroup (Fin 2) k).val = _
  simp only [mul_inv_rev, Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
  have ht : (dPointEquiv 1 t 0 : k) ≠ 0 := (dPointEquiv 1 t 0).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
      Matrix.one_apply, Matrix.diagonal, CharTwo.add_self_eq_zero, ht]

omit [CharP k 2] in
private lemma slMatrix_mul (x y : Variety.Point (slVariety k 2)) :
    slPointMatrix 2 (x * y) = slPointMatrix 2 x * slPointMatrix 2 y := rfl

omit [CharP k 2] in
private lemma slMatrix_inj : Function.Injective (slPointMatrix (k := k) 2) := by
  intro x y h
  apply (slPointEquiv 2).injective
  exact Subtype.ext h

private def corootMatrix (a : kˣ) : Matrix (Fin 2) (Fin 2) k :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then (a : k)⁻¹ else (a : k))

omit [IsAlgClosed k] [CharP k 2] in
private lemma corootMatrix_mul (a b : kˣ) :
    corootMatrix (a * b) = corootMatrix a * corootMatrix b := by
  rw [corootMatrix, corootMatrix, corootMatrix, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext i
  simp only [Units.val_mul]
  split_ifs <;> simp [mul_comm]

private theorem binarySL2Word_mul (s t : Variety.Point (KMult k)) :
    (binarySL2Word (k := k)).toFun (s * t) =
      (binarySL2Word (k := k)).toFun s * (binarySL2Word (k := k)).toFun t := by
  apply slMatrix_inj
  exact (binarySL2Word_matrix (s * t)).trans
    ((congrArg corootMatrix (congrFun (dPointEquiv_mul 1 s t) 0)).trans
      ((corootMatrix_mul (dPointEquiv 1 s 0) (dPointEquiv 1 t 0)).trans
        ((congrArg₂ (fun a b : Matrix (Fin 2) (Fin 2) k => a * b)
          (binarySL2Word_matrix s).symm (binarySL2Word_matrix t).symm).trans
            (slMatrix_mul _ _).symm)))

/-- The regular cocharacter `diag(t⁻¹,t)`, constructed from the upper and lower
SL₂ curves using the GLS word `n(1)⁻¹n(t)` in characteristic two. -/
noncomputable def binarySL2Coroot : Morphism (KMult k) (slVariety k 2) where
  toVariety := binarySL2Word
  map_one := binaryCorootWord_one _ _
  map_mul := binarySL2Word_mul

/-- The cocharacter has exactly the published regular word as underlying map. -/
theorem binarySL2Coroot_toVariety :
    (binarySL2Coroot (k := k)).toVariety =
      binaryCorootWord standardSL2UpperMorphism.toVariety
        standardSL2LowerMorphism.toVariety := by
  rfl

/-- The source-convention word has inverse parameter in the first diagonal entry. -/
theorem binarySL2Coroot_matrix (t : Variety.Point (KMult k)) :
    slPointMatrix 2 ((binarySL2Coroot (k := k)).onPoints t) =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then
        (dPointEquiv 1 t 0 : k)⁻¹ else (dPointEquiv 1 t 0 : k)) :=
  binarySL2Word_matrix t

end Theory.AlgebraicGroup

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]

/-- Rank-one geometric data for two specified closed subgroups: a compatible
regular SL₂ morphism whose diagonal image lies in the specified torus.
Constructing this chart and proving its Cartan normalization are separate
geometric obligations. The stored model cocharacter is not part of the data. -/
structure BinaryOppositeRootSL2Chart {G : Variety k} [AlgebraicGroup G]
    (T X Y : ClosedSubgroup G) where
  plus : OneParameterParametrization X.carrierVariety
  minus : OneParameterParametrization Y.carrierVariety
  map : Morphism (slVariety k 2) (oppositePairGeneratedSubgroup X Y).carrierVariety
  compatible : OppositePairSL2Compatible X Y plus minus map
  diagonal_mem : ∀ t : Variety.Point (KMult k),
    (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      (map.onPoints (binarySL2Coroot.onPoints t)) ∈ T

namespace BinaryOppositeRootSL2Chart
variable {G : Variety k} [AlgebraicGroup G] {T X Y : ClosedSubgroup G}
variable (C : BinaryOppositeRootSL2Chart T X Y)

/-- The rank-one diagonal morphism restricted to the actual torus. -/
noncomputable def cocharacter : ClosedSubgroupTorusCocharacter T :=
  (((oppositePairGeneratedSubgroup X Y).inclusion.comp C.map).comp binarySL2Coroot).codRestrictClosedSubgroup
    T C.diagonal_mem

/-- Restriction to the torus preserves the rank-one diagonal image. -/
theorem cocharacter_inclusion_apply (t : Variety.Point (KMult k)) :
    T.inclusion.onPoints (C.cocharacter.onPoints t) =
      (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
        (C.map.onPoints (binarySL2Coroot.onPoints t)) :=
  Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ t

/-- The word in the actual two root curves is the chart cocharacter. -/
theorem word_eq_cocharacter (t : Variety.Point (KMult k)) :
    (binaryCorootWord (X.inclusion.comp C.plus.hom).toVariety
      (Y.inclusion.comp C.minus.hom).toVariety).toFun t =
        T.inclusion.onPoints (C.cocharacter.onPoints t) := by
  rw [cocharacter_inclusion_apply]
  exact OppositePairSL2Compatible.binaryCorootWord_eq X Y C.plus C.minus C.map C.compatible t
end BinaryOppositeRootSL2Chart
end Theory.AlgebraicGroup
