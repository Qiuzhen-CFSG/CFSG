module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.Definitions
public import Theory.AlgebraicGroup.Representations.Semisimple
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.FinCases

/-!
# The natural spectrum of a projective cubic in SL₃(4)

A lift of a projective cubic has scalar cube `a`. If `a ≠ 1`, the polynomial
`X³ - a` has no root over the four-element field, so it is irreducible and is
both the minimal and characteristic polynomial of the lift. Its constant
coefficient contradicts determinant one. Thus the lift itself has cube one.

Separability gives a natural eigenbasis. Determinant one forces a repeated
cubic eigenvalue to occur three times, which would make the lift central.
The three distinct eigenvalues therefore give a permutation of `1, ω, ω²`.
Reindexing supplies the specified basis for every coefficient embedding and
every chosen primitive cubic root, as required for the two adjoint factors.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
This proves the natural-spectrum input to the direct adjoint calculation.
-/

public section

open scoped MatrixGroups
open Polynomial Representation.SL3.BinaryDefiningFactors
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
variable {F K : Type*} [Field F] [Field K]

private theorem projective_cubic_cube_eq_one [Finite F] (hcard : Nat.card F = 4) (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3) : g ^ 3 = 1 := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨_, a, ha, hmat, _⟩ := projective_cubic_lift g hg
  have ha1 : a = 1 := by
    by_contra ha1
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    have hirr : Irreducible (X ^ 3 - C a : F[X]) := by
      apply irreducible_of_degree_le_three_of_not_isRoot
      · simp
      · intro x hx
        have hx3 : x ^ 3 = a := by simpa [Polynomial.IsRoot, sub_eq_zero] using hx
        have hx0 : x ≠ 0 := by intro h; simp [h] at hx3; exact ha0 hx3.symm
        have hpow := FiniteField.pow_card_sub_one_eq_one x hx0
        have hc : Fintype.card F = 4 := by simpa [Nat.card_eq_fintype_card] using hcard
        rw [hc] at hpow
        exact ha1 (hx3.symm.trans hpow)
    have heval : aeval g.val (X ^ 3 - C a) = 0 := by
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [← Matrix.SpecialLinearGroup.coe_pow, hmat]
      exact sub_self _
    have hmin := minpoly.eq_of_irreducible_of_monic hirr heval (monic_X_pow_sub_C a (by decide : 3 ≠ 0))
    have hchar : g.val.charpoly = (X ^ 3 - C a : F[X]) := by
      apply eq_of_monic_of_dvd_of_natDegree_le (monic_X_pow_sub_C a (by decide)) g.val.charpoly_monic
      · rw [hmin]; exact g.val.minpoly_dvd_charpoly
      · simp
    have hc := g.val.det_eq_sign_charpoly_coeff
    rw [hchar] at hc
    apply ha1
    norm_num [g.property] at hc
    exact hc.symm
  apply Subtype.ext
  rw [hmat, ha1, map_one]
  rfl

private theorem natural_injective (η : F →+* K) : Function.Injective (natural η) := by
  intro g h he
  apply Subtype.ext
  have hm : g.val.map η = h.val.map η := Matrix.toLin'.injective he
  ext i j
  exact η.injective (congrArg (fun A => A i j) hm)

private theorem natural_det (η : F →+* K) (g : SL(3,F)) :
    LinearMap.det (natural η g) = 1 := by
  change LinearMap.det (Matrix.toLin' (Matrix.SpecialLinearGroup.map η g).val) = 1
  rw [LinearMap.det_toLin']
  exact (Matrix.SpecialLinearGroup.map η g).property

private theorem cubic_values_injective_or_constant (μ : Fin 3 → K)
    (hc : ∀ i, μ i ^ 3 = 1) (hd : μ 0 * μ 1 * μ 2 = 1) :
    Function.Injective μ ∨ ∀ i, μ i = μ 0 := by
  have h0 : ∀ i, μ i ≠ 0 := by
    intro i he
    simpa [he] using hc i
  have h01 (h : μ 0 = μ 1) : μ 2 = μ 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (h0 0))
    calc
      μ 0 ^ 2 * μ 2 = 1 := by simpa [pow_two, ← h] using hd
      _ = μ 0 ^ 2 * μ 0 := by rw [← pow_succ]; exact (hc 0).symm
  have h02 (h : μ 0 = μ 2) : μ 1 = μ 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (h0 0))
    calc
      μ 0 ^ 2 * μ 1 = 1 := by simpa [pow_two, ← h, mul_comm, mul_left_comm, mul_assoc] using hd
      _ = μ 0 ^ 2 * μ 0 := by rw [← pow_succ]; exact (hc 0).symm
  have h12 (h : μ 1 = μ 2) : μ 0 = μ 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (h0 1))
    calc
      μ 1 ^ 2 * μ 0 = 1 := by simpa [pow_two, ← h, mul_comm, mul_left_comm, mul_assoc] using hd
      _ = μ 1 ^ 2 * μ 1 := by rw [← pow_succ]; exact (hc 1).symm
  by_cases h : μ 0 = μ 1
  · right
    intro i
    fin_cases i
    · rfl
    · exact h.symm
    · exact h01 h
  · left
    have hn02 : μ 0 ≠ μ 2 := fun he => h (h02 he).symm
    have hn12 : μ 1 ≠ μ 2 := fun he => h (h12 he)
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact False.elim (h hij) | exact False.elim (h hij.symm) |
        exact False.elim (hn02 hij) | exact False.elim (hn02 hij.symm) |
        exact False.elim (hn12 hij) | exact False.elim (hn12 hij.symm)

private theorem natural_eigenbasis_of_cube_eq_one [IsAlgClosed K] [CharP K 2] (η : F →+* K) (g : SL(3,F))
    (hnc : g ∉ Subgroup.center SL(3,F)) (hg3 : g ^ 3 = 1)
    (ω : K) (hω : orderOf ω = 3) :
    ∃ b : Module.Basis (Fin 3) K (Fin 3 → K),
      ∀ i, natural η g (b i) = ω ^ i.val • b i := by
  classical
  let T : Module.End K (Fin 3 → K) := natural η g
  have hT3 : T ^ 3 = 1 := by dsimp [T]; rw [← map_pow, hg3, map_one]
  have hs : T.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (separable_X_pow_sub_C' 2 3 (1 : K) (by decide) one_ne_zero).squarefree
    simp [hT3]
  have hex : ∃ (b : Module.Basis (Fin 3) K (Fin 3 → K)) (μ : Fin 3 → K),
      ∀ i, T (b i) = μ i • b i := by
    have hex := Theory.AlgebraicGroup.Module.End.IsSemisimple.exists_fin_eigenbasis T hs
    rw [Module.finrank_fin_fun] at hex
    exact hex
  obtain ⟨b, μ, hb⟩ := hex
  have hc : ∀ i, μ i ^ 3 = 1 := by
    intro i
    have heig : T.HasEigenvector (μ i) (b i) :=
      ⟨Module.End.mem_eigenspace_iff.mpr (hb i), b.ne_zero i⟩
    have he := heig.pow_apply 3
    rw [hT3, Module.End.one_apply] at he
    apply smul_left_injective K (b.ne_zero i)
    exact he.symm.trans (one_smul K (b i)).symm
  have hm : LinearMap.toMatrix b b T = Matrix.diagonal μ := by
    ext i j
    by_cases h : i = j
    · subst j; simp [LinearMap.toMatrix_apply, hb]
    · simp [LinearMap.toMatrix_apply, hb, h]
  have hd : μ 0 * μ 1 * μ 2 = 1 := by
    have hh := natural_det η g
    rw [← LinearMap.det_toMatrix b, hm, Matrix.det_diagonal, Fin.prod_univ_three] at hh
    exact hh
  have hi : Function.Injective μ := by
    rcases cubic_values_injective_or_constant μ hc hd with h | h
    · exact h
    exfalso
    apply hnc
    have he : T = μ 0 • (1 : Module.End K (Fin 3 → K)) := by
      apply b.ext
      intro i
      simp [hb, h]
    rw [Subgroup.mem_center_iff]
    intro x
    apply natural_injective η
    rw [map_mul, map_mul]
    change natural η x * T = T * natural η x
    rw [he]
    simp
  have hprim : IsPrimitiveRoot ω 3 := IsPrimitiveRoot.iff_orderOf.mpr hω
  have he : ∀ i, ∃ j : Fin 3, μ i = ω ^ j.val := by
    intro i
    obtain ⟨j, hj, he⟩ := hprim.eq_pow_of_pow_eq_one (hc i)
    exact ⟨⟨j, hj⟩, he.symm⟩
  choose e he using he
  have heinj : Function.Injective e := by
    intro i j hij
    apply hi
    rw [he i, he j, hij]
  let E := Equiv.ofBijective e ((Fintype.bijective_iff_injective_and_card e).mpr ⟨heinj, rfl⟩)
  refine ⟨b.reindex E, fun i => ?_⟩
  simp only [Module.Basis.reindex_apply]
  change T (b (E.symm i)) = ω ^ i.val • b (E.symm i)
  rw [hb, he]
  change ω ^ (E (E.symm i)).val • b (E.symm i) = _
  rw [E.apply_symm_apply]

/-- Every lift of a projective cubic in SL₃(4) has an actual natural eigenbasis
with the prescribed weights, for the given embedding and the given cubic root. -/
theorem projective_cubic_natural_eigenbasis [Finite F] [CharP F 2]
    [IsAlgClosed K] [CharP K 2] (hcard : Nat.card F = 4)
    (η : F →+* K) (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3)
    (ω : K) (hω : orderOf ω = 3) :
    ∃ b : Module.Basis (Fin 3) K (Fin 3 → K),
      ∀ i, natural η g (b i) = ω ^ i.val • b i :=
  natural_eigenbasis_of_cube_eq_one η g (projective_cubic_lift g hg).1
    (projective_cubic_cube_eq_one hcard g hg) ω hω

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
