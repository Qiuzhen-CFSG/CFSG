module
public import Theory.SpecificGroups.LieType.F4RootSL2.Representation
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootGeneration

/-!
# A noncentral long-root involution in the F₄ matrix group

The element −1 of the explicit SL₂ fixes every Cartan coordinate and negates
each natural root-string block. The neighboring root α₁ belongs to such a
block. Its positive curve at parameter 1 sends the α₀ Cartan vector to that
vector plus the α₁ root vector, so it does not commute with the involution
when 2 is nonzero. This supplies the concrete matrix separation used to prove
both injectivity and properness after the central quotient.

Source: the long-root fundamental subgroup in Aschbacher–Smith A.2.17,
printed p.39 of `refs/quasithin.pdf`; the common-lattice construction in GLS3
§§1.12 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootSL2
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
local instance separationBasisDecidableEq : DecidableEq Basis := fun a b => instDecidableEqSum a b

variable {F : Type*} [Field F]

lemma neg_one_cartan (j : Fin 4) :
    (ambientHom (-1 : SL(2, F))).val *ᵥ
      Pi.single (latticeEquiv (.inl (.inl j))) 1 =
        Pi.single (latticeEquiv (.inl (.inl j))) 1 := by
  ext a
  obtain ⟨r, rfl⟩ := latticeEquiv.surjective a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, ambientHom_entry]
  rcases r with (r | r) | (⟨r,k⟩ | r) <;>
    simp [blockMatrix, specialBlock, SpecialLinearGroup.coe_neg,
      Matrix.one_apply, Pi.single_apply, latticeEquiv.injective.eq_iff]
  all_goals aesop

lemma neg_one_natural (r : Fin 2) (k : Fin 14) :
    (ambientHom (-1 : SL(2, F))).val *ᵥ
      Pi.single (latticeEquiv (.inr (.inl (r,k)))) 1 =
        -Pi.single (latticeEquiv (.inr (.inl (r,k)))) 1 := by
  ext a
  obtain ⟨s, rfl⟩ := latticeEquiv.surjective a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, ambientHom_entry]
  rcases s with (s | s) | (⟨s,l⟩ | s) <;>
    simp [blockMatrix, SpecialLinearGroup.coe_neg,
      Matrix.one_apply, Matrix.blockDiagonal, Pi.single_apply, latticeEquiv.injective.eq_iff]
  split_ifs <;> simp_all

lemma lattice_cartan (j : Fin 4) :
    latticeEquiv (.inl (.inl j)) = .inl (typeF4RootPairing_baseEquiv j) := by
  fin_cases j <;> rfl

lemma lattice_neighbor :
    latticeEquiv (.inr (.inl (1,6))) = .inr (typeF4RootPairing_baseEquiv 1).val := by
  change Sum.inr (root 30) = Sum.inr (typeF4SimpleRootIndex 1)
  congr 1
  apply Subtype.ext
  ext q
  fin_cases q <;> norm_num [root, realCoord, coord, typeF4SimpleRootIndex,
    typeF4SimpleRoot, basisVector, Pi.single_apply, Fin.ext_iff]

lemma positive_cartan (i j : typeF4RootPairing_base.support) (t : F) :
    positiveMatrix i t *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 +
        (t * ((|typeF4RootPairing_base.cartanMatrix i j| : ℤ) : F)) •
          Pi.single (Sum.inr i.val) 1 := by
  ext a
  rcases a with a | a <;>
    simp [positiveMatrix_formula, eDividedPower,
      eMatrix, Matrix.one_apply, Pi.single_apply, smul_eq_mul]

lemma neg_one_not_commute_neighbor (hF : (2 : F) ≠ 0) :
    ¬ Commute (ambientHom (-1 : SL(2, F)))
      (positiveUnit (typeF4RootPairing_baseEquiv 1) (1 : F)) := by
  intro hc
  let u : Basis → F := Pi.single (Sum.inl (typeF4RootPairing_baseEquiv 0)) 1
  let v : Basis → F := Pi.single (Sum.inr (typeF4RootPairing_baseEquiv 1).val) 1
  have hu : (ambientHom (-1 : SL(2, F))).val *ᵥ u = u := by
    simpa only [lattice_cartan] using neg_one_cartan (F := F) 0
  have hv : (ambientHom (-1 : SL(2, F))).val *ᵥ v = -v := by
    simpa only [lattice_neighbor] using neg_one_natural (F := F) 1 6
  have hx : (positiveUnit (typeF4RootPairing_baseEquiv 1) (1 : F)).val *ᵥ u = u + v := by
    rw [positiveUnit_val, positive_cartan, typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]
    rfl
  have he := congrArg (fun A : (Matrix Basis Basis F)ˣ => A.val *ᵥ u) hc.eq
  change ((ambientHom (-1 : SL(2, F))).val * (positiveUnit _ (1 : F)).val) *ᵥ u =
    ((positiveUnit _ (1 : F)).val * (ambientHom (-1 : SL(2, F))).val) *ᵥ u at he
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, hu,
    Matrix.mulVec_add, hu, hv, hx] at he
  have hh := congrFun he (Sum.inr (typeF4RootPairing_baseEquiv 1).val)
  have hneg : (-1 : F) = 1 := by simpa [u,v] using hh
  exact hF (by linear_combination -hneg)

end ExceptionalSplit.F4RootSL2

end
