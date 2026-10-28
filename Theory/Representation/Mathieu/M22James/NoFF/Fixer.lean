module
public import Theory.Representation.Mathieu.M22James.NoFF.FixerData

/-!
# A rank-one displacement forced by a sixteen-element pointwise fixer

A Hermitian matrix annihilating the four fixed vectors is determined by its
entries (0,0), (2,2), and (0,2). Its two diagonal entries lie in the binary
subfield, so these matrices inject into a sixteen-element parameter space.
Any faithful sixteen-element family fills that space and consequently contains
the explicit rank-one displacement. For the genuine triple Mathieu action,
square-one unitary actors have Hermitian displacement, giving the actual
subgroup application used by the no-offender proof.

Source: Aschbacher–Smith H.12.1(12), printed pp.393–395. This is a direct
unitary common-fixer argument for the FF consequence of that source clause.
-/

@[expose] public section
open Matrix Representation.SL2FourNatural
open scoped Matrix
namespace Sporadic.Mathieu.M22TripleCover.NoFF
open Sporadic.Mathieu.M22TripleCover.Unitary

private theorem fixedBasis_columns (D : Matrix (Fin 6) (Fin 6) F)
    (h : ∀ k, D *ᵥ fixedBasis k = 0) (i : Fin 6) :
    D i 1 = D i 0 ∧ D i 3 = D i 0 * fieldEntry 3 ∧
    D i 4 = D i 0 * fieldEntry 2 ∧ D i 5 = D i 2 * fieldEntry 2 := by
  have h0 := congrFun (h 0) i
  have h1 := congrFun (h 1) i
  have h2 := congrFun (h 2) i
  have h3 := congrFun (h 3) i
  have hz : fieldEntry 0 = (0 : F) := rfl
  have ho : fieldEntry 1 = (1 : F) := rfl
  simp only [fixedBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val_two, Matrix.cons_val_three,
    Fin.sum_univ_zero, Matrix.head_cons, Matrix.tail_cons, hz, ho,
    mul_zero, mul_one, add_zero, zero_add, Pi.zero_apply] at h0 h1 h2 h3
  exact ⟨(eq_neg_of_add_eq_zero_right h0).trans (CharTwo.neg_eq _),
    (eq_neg_of_add_eq_zero_right h1).trans (CharTwo.neg_eq _),
    (eq_neg_of_add_eq_zero_right h2).trans (CharTwo.neg_eq _),
    (eq_neg_of_add_eq_zero_right h3).trans (CharTwo.neg_eq _)⟩

theorem commonFixer_ext (D E : Matrix (Fin 6) (Fin 6) F)
    (hD : D.transpose.map fieldFrobenius = D)
    (hE : E.transpose.map fieldFrobenius = E)
    (hDf : ∀ k, D *ᵥ fixedBasis k = 0) (hEf : ∀ k, E *ᵥ fixedBasis k = 0)
    (h00 : D 0 0 = E 0 0) (h22 : D 2 2 = E 2 2) (h02 : D 0 2 = E 0 2) : D = E := by
  have hDe (i j) : fieldFrobenius (D j i) = D i j := congrArg (fun M => M i j) hD
  have hEe (i j) : fieldFrobenius (E j i) = E i j := congrArg (fun M => M i j) hE
  have h20 : D 2 0 = E 2 0 := fieldFrobenius.injective
    ((hDe 0 2).trans (h02.trans (hEe 0 2).symm))
  have hrow0 (j : Fin 6) : D 0 j = E 0 j := by
    rcases fixedBasis_columns D hDf 0 with ⟨d1,d3,d4,d5⟩
    rcases fixedBasis_columns E hEf 0 with ⟨e1,e3,e4,e5⟩
    fin_cases j
    · exact h00
    · exact d1.trans (h00.trans e1.symm)
    · exact h02
    · exact d3.trans ((congrArg (· * fieldEntry 3) h00).trans e3.symm)
    · exact d4.trans ((congrArg (· * fieldEntry 2) h00).trans e4.symm)
    · exact d5.trans ((congrArg (· * fieldEntry 2) h02).trans e5.symm)
  have hrow2 (j : Fin 6) : D 2 j = E 2 j := by
    rcases fixedBasis_columns D hDf 2 with ⟨d1,d3,d4,d5⟩
    rcases fixedBasis_columns E hEf 2 with ⟨e1,e3,e4,e5⟩
    fin_cases j
    · exact h20
    · exact d1.trans (h20.trans e1.symm)
    · exact h22
    · exact d3.trans ((congrArg (· * fieldEntry 3) h20).trans e3.symm)
    · exact d4.trans ((congrArg (· * fieldEntry 2) h20).trans e4.symm)
    · exact d5.trans ((congrArg (· * fieldEntry 2) h22).trans e5.symm)
  have hcol0 (i : Fin 6) : D i 0 = E i 0 := fieldFrobenius.injective
    ((hDe 0 i).trans ((hrow0 i).trans (hEe 0 i).symm))
  have hcol2 (i : Fin 6) : D i 2 = E i 2 := fieldFrobenius.injective
    ((hDe 2 i).trans ((hrow2 i).trans (hEe 2 i).symm))
  apply Matrix.ext
  intro i j
  rcases fixedBasis_columns D hDf i with ⟨d1,d3,d4,d5⟩
  rcases fixedBasis_columns E hEf i with ⟨e1,e3,e4,e5⟩
  fin_cases j
  · exact hcol0 i
  · exact d1.trans ((hcol0 i).trans e1.symm)
  · exact hcol2 i
  · exact d3.trans ((congrArg (· * fieldEntry 3) (hcol0 i)).trans e3.symm)
  · exact d4.trans ((congrArg (· * fieldEntry 2) (hcol0 i)).trans e4.symm)
  · exact d5.trans ((congrArg (· * fieldEntry 2) (hcol2 i)).trans e5.symm)


private theorem fixed_re_inj (x y : F)
    (hx : fieldFrobenius x = x) (hy : fieldFrobenius y = y) (h : x.re = y.re) : x = y := by
  revert x y
  decide +kernel

private def parameters (D : Matrix (Fin 6) (Fin 6) F) : (ZMod 2 × ZMod 2) × F :=
  ((D 0 0 |>.re, D 2 2 |>.re), D 0 2)

private theorem parameters_ext (D E : Matrix (Fin 6) (Fin 6) F)
    (hD : D.transpose.map fieldFrobenius = D)
    (hE : E.transpose.map fieldFrobenius = E)
    (hDf : ∀ k, D *ᵥ fixedBasis k = 0) (hEf : ∀ k, E *ᵥ fixedBasis k = 0)
    (he : parameters D = parameters E) : D = E := by
  apply commonFixer_ext D E hD hE hDf hEf
  · apply fixed_re_inj
    · exact congrArg (fun M => M 0 0) hD
    · exact congrArg (fun M => M 0 0) hE
    · exact congrArg (fun p => p.1.1) he
  · apply fixed_re_inj
    · exact congrArg (fun M => M 2 2) hD
    · exact congrArg (fun M => M 2 2) hE
    · exact congrArg (fun p => p.1.2) he
  · exact congrArg Prod.snd he

theorem commonFixer_realizes_rankOne {α : Type*}
    (D : α → Matrix (Fin 6) (Fin 6) F) (hi : Function.Injective D)
    (hc : Nat.card α = 16)
    (hD : ∀ a, (D a).transpose.map fieldFrobenius = D a)
    (hf : ∀ a k, D a *ᵥ fixedBasis k = 0) :
    ∃ a, D a = rankOneDisplacement := by
  have hp : Function.Injective (fun a => parameters (D a)) := by
    intro a b he
    apply hi
    exact parameters_ext _ _ (hD a) (hD b) (hf a) (hf b) he
  have ht : Nat.card ((ZMod 2 × ZMod 2) × F) = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hs := ((Nat.bijective_iff_injective_and_card (fun a => parameters (D a))).mpr
    ⟨hp, hc.trans ht.symm⟩).2
  obtain ⟨a, ha⟩ := hs (parameters rankOneDisplacement)
  exact ⟨a, parameters_ext _ _ (hD a) rankOneDisplacement_hermitian
    (hf a) rankOneDisplacement_fixedBasis ha⟩

noncomputable section
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private theorem actionMatrix_mulVec (g : M22TripleCover) (v : Unitary.Vector) :
    (matrixAction g : Matrix (Fin 6) (Fin 6) F) *ᵥ v = fieldAction g v := by
  change LinearMap.toMatrix' (fieldAction g) *ᵥ v = _
  exact LinearMap.toMatrix'_mulVec _ _

private theorem involution_displacement_hermitian (g : M22TripleCover) (hs : g ^ 2 = 1) :
    ((matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1).transpose.map fieldFrobenius =
      (matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1 := by
  let M : Matrix (Fin 6) (Fin 6) F := matrixAction g
  have hsq : M * M = 1 := by
    change ((matrixAction g * matrixAction g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1
    rw [← map_mul, ← pow_two, hs, map_one]
    rfl
  have hm : M.transpose.map fieldFrobenius = M := by
    calc
      M.transpose.map fieldFrobenius = M.transpose.map fieldFrobenius * (M * M) := by
        rw [hsq, mul_one]
      _ = (M.transpose.map fieldFrobenius * M) * M := (mul_assoc _ _ _).symm
      _ = M := by rw [matrixAction_unitary, one_mul]
  apply Matrix.ext
  intro i j
  change fieldFrobenius (M j i - (1 : Matrix (Fin 6) (Fin 6) F) j i) =
    M i j - (1 : Matrix (Fin 6) (Fin 6) F) i j
  rw [map_sub]
  have he : fieldFrobenius (M j i) = M i j := congrArg (fun N => N i j) hm
  rw [he]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

private theorem matrix_displacement_injective {G : Type*} [Group G]
    (f : G →* GL (Fin 6) F) (hf : Function.Injective f) :
    Function.Injective (fun g => (f g : Matrix (Fin 6) (Fin 6) F) - 1) := by
  intro g h he
  apply hf
  apply Units.ext
  exact sub_left_inj.mp he

theorem subgroup_realizes_rankOne (A : Subgroup M22TripleCover)
    (hsq : ∀ a : A, (a : M22TripleCover) ^ 2 = 1) (hc : Nat.card A = 16)
    (hf : ∀ a : A, ∀ v, fieldAction coreGeneratorB v = v →
      fieldAction (a : M22TripleCover) v = v) :
    ∃ a : A, (matrixAction (a : M22TripleCover) : Matrix (Fin 6) (Fin 6) F) =
      1 + rankOneDisplacement := by
  let D (a : A) : Matrix (Fin 6) (Fin 6) F := matrixAction (a : M22TripleCover) - 1
  have hi : Function.Injective D := by
    intro a b he
    exact Subtype.ext (matrix_displacement_injective matrixAction matrixAction_faithful he)
  have hh (a : A) : (D a).transpose.map fieldFrobenius = D a :=
    involution_displacement_hermitian _ (hsq a)
  have hk (a : A) (k : Fin 4) : D a *ᵥ fixedBasis k = 0 := by
    dsimp only [D]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, actionMatrix_mulVec]
    apply sub_eq_zero.mpr
    apply hf a
    rw [← actionMatrix_mulVec, matrixAction_generatorB]
    exact generatorB_fixedBasis k
  obtain ⟨a, ha⟩ := commonFixer_realizes_rankOne D hi hc hh hk
  refine ⟨a, ?_⟩
  exact (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)

end
end Sporadic.Mathieu.M22TripleCover.NoFF
