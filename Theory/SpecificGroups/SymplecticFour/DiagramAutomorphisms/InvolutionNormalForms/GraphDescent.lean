module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Lang
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-field descent of exceptional graph cocycles

Solve the graph Lang equation over the algebraic closure. The cocycle identity
forces the solution to be fixed by the square of the graph power, hence by the
Frobenius power of the original finite field. Its entries are roots of
X^|F| - X and therefore lie in F; the symplectic equations descend with them.
This produces a genuine symplectic coboundary over F, including the odd-degree
graph case needed for Quasithin 2.5.19 and E.6.23 (via 16.1.4).
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open ExceptionalGraph
variable {F K : Type*} [Field F] [Field K]

private theorem finiteField_range_of_pow_card [Finite F] (f : F →+* K) (a : K)
    (ha : a ^ Nat.card F = a) : ∃ b : F, f b = a := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let p : Polynomial F := Polynomial.X ^ Fintype.card F - Polynomial.X
  have hp : p.Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
    simp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hr : (p.map f).IsRoot a := by
    simpa [p,Polynomial.IsRoot,←Nat.card_eq_fintype_card] using sub_eq_zero.mpr ha
  exact hp.mem_range_of_isRoot hp0 hr

private theorem matrix_descent [Finite F] (f : F →+* K) (g : Sp K)
    (hg : ∀ i j, g.val i j ^ Nat.card F = g.val i j) :
    ∃ h : Sp F, coefficientMap f h = g := by
  classical
  choose A hA using fun i j => finiteField_range_of_pow_card f (g.val i j) (hg i j)
  let A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := A
  have he : A'.map f = g.val := by
    ext i j
    exact hA i j
  have hsp : A' ∈ Matrix.symplecticGroup (Fin 2) F := by
    have hh := g.property
    rw [←he] at hh
    rw [SymplecticGroup.mem_iff] at hh ⊢
    apply Matrix.map_injective f.injective
    simpa only [Matrix.map_mul,Matrix.transpose_map,Matrix.map_J] using hh
  refine ⟨⟨A',hsp⟩,Subtype.ext ?_⟩
  ext i j
  rw [coefficientMap_apply]
  exact hA i j

public theorem graph_cocycle_coboundary [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 0 < n)
    (g : Sp F) (hg : g * (graphAut ^ n) g = 1) :
    ∃ h : Sp F, g = h * ((graphAut ^ n) h)⁻¹ := by
  let K := AlgebraicClosure F
  let f : F →+* K := algebraMap F K
  let σ : Monoid.End (Sp K) := graphEndomorphism ^ n
  let γ := coefficientMap f g
  have hγ : γ * σ γ = 1 := by
    change coefficientMap f g * (graphEndomorphism ^ n) (coefficientMap f g) = 1
    rw [←coefficientMap_graphPower,←map_mul,←graphAut_pow_apply]
    rw [hg,map_one]
  obtain ⟨t,ht⟩ := graphEnd_lang_surjective (k := K) n hn γ
  change t * (σ t)⁻¹ = γ at ht
  have ht2 : σ (σ t) = t := by
    have hh := hγ
    rw [←ht,map_mul,map_inv] at hh
    have he : t * (σ (σ t))⁻¹ = 1 := by simpa only [mul_assoc,inv_mul_cancel_left] using hh
    exact (mul_inv_eq_one.mp he).symm
  have htwice : (graphEndomorphism ^ (2*n)) t = t := by
    rw [two_mul,pow_add]
    exact ht2
  obtain ⟨h,hh⟩ := matrix_descent f t (by
    intro i j
    rw [hcard]
    have he := graphEnd_even_power n t i j
    rw [htwice] at he
    exact he.symm)
  refine ⟨h,coefficientMap_injective f ?_⟩
  rw [map_mul,map_inv,graphAut_pow_apply,coefficientMap_graphPower,hh]
  exact ht.symm
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
