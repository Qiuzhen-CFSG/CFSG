module
public import Theory.AlgebraicGroup.RootSystems.IntegralGeckConstruction
public import Theory.AlgebraicGroup.RootSystems.GeckDiagramAction

/-!
# Equivariance of integral Geck matrices under pinned diagram automorphisms

The base permutation and root permutation act on the Cartan-plus-root indices.
Preservation of root strings and the Cartan matrix gives equivariance of the
positive and negative simple operators, then of the integral divided powers.
The negative divided powers follow by the involution reversing all roots.

Source: GLS3, §§1.12 and 2.1–2.3, and the integral Geck construction.
-/
namespace RootPairing.IntegralGeckConstruction
@[expose] public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
variable (d : P.Equiv P) (db : b.support ≃ b.support)
  (hd : ∀ i : b.support, d.indexEquiv i = (db i : ι))
include hd

@[simp] theorem diagram_eMatrix (i : b.support) :
    diagramMatrixEquiv d db ℤ (eMatrix i) = eMatrix (db i) := by
  let _ := P.indexNeg
  have hn (r : ι) :
      P.reflectionPerm (d.indexEquiv r) (d.indexEquiv r) =
        d.indexEquiv (P.reflectionPerm r r) := (diagram_neg d r).symm
  have ha (j k : ι) : P.root (d.indexEquiv j) =
      P.root (db i) + P.root (d.indexEquiv k) ↔ P.root j = P.root i + P.root k := by
    rw [← hd i, diagram_root_add_iff]
  apply (diagramMatrixEquiv_eq_iff d db ℤ _ _).mpr
  rintro (j | j) (k | k) <;>
    simp [diagramIndexEquiv, eMatrix, ← hd, hn, diagram_cartanMatrix d db hd]
  rw [ha]

@[simp] theorem diagram_fMatrix (i : b.support) :
    diagramMatrixEquiv d db ℤ (fMatrix i) = fMatrix (db i) := by
  let _ := P.indexNeg
  have hn (r : ι) :
      P.reflectionPerm (d.indexEquiv r) (d.indexEquiv r) =
        d.indexEquiv (P.reflectionPerm r r) := (diagram_neg d r).symm
  have hs (j k : ι) : P.root (d.indexEquiv j) =
      P.root (d.indexEquiv k) - P.root (db i) ↔ P.root j = P.root k - P.root i := by
    rw [← hd i, diagram_root_sub_iff]
  apply (diagramMatrixEquiv_eq_iff d db ℤ _ _).mpr
  rintro (j | j) (k | k) <;>
    simp [diagramIndexEquiv, fMatrix, ← hd, hn, diagram_cartanMatrix d db hd]
  rw [hs]

omit hd in
@[simp] theorem diagram_omegaMatrix :
    diagramMatrixEquiv d db ℤ (omegaMatrix (b := b)) = omegaMatrix (b := b) := by
  let _ := P.indexNeg
  have hn (r : ι) :
      P.reflectionPerm (d.indexEquiv r) (d.indexEquiv r) =
        d.indexEquiv (P.reflectionPerm r r) := (diagram_neg d r).symm
  apply (diagramMatrixEquiv_eq_iff d db ℤ _ _).mpr
  rintro (j | j) (k | k) <;>
    simp [diagramIndexEquiv, omegaMatrix, hn, Matrix.one_apply]

@[simp] theorem diagram_eDividedPower (i : b.support) (n : ℕ) :
    diagramMatrixEquiv d db ℤ (eDividedPower i n) = eDividedPower (db i) n := by
  cases n with
  | zero => exact map_one _
  | succ n =>
    cases n with
    | zero => exact diagram_eMatrix d db hd i
    | succ n =>
      apply (diagramMatrixEquiv_eq_iff d db ℤ _ _).mpr
      rintro (j | j) (k | k) <;>
        simp [diagramIndexEquiv, eDividedPower, ← hd]
      rw [← hd i, diagram_root_add_nsmul_iff]

@[simp] theorem diagram_fDividedPower (i : b.support) (n : ℕ) :
    diagramMatrixEquiv d db ℤ (fDividedPower i n) = fDividedPower (db i) n := by
  simp only [fDividedPower, map_mul, diagram_omegaMatrix,
    diagram_eDividedPower d db hd]

end
end
end RootPairing.IntegralGeckConstruction
