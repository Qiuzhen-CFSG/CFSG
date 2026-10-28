module

public import Theory.SpecificGroups.SL3.InvolutionBlock
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Conjugacy of involutions in SL₃

An involution over a field of characteristic different from two is the direct
sum of its `+1` and `-1` eigenspaces.  In dimension three, determinant one and
nontriviality force the `-1` eigenspace to have dimension two.  A basis adapted
to these eigenspaces gives the standard representative.  We then rescale one
coordinate to make the diagonalizing matrix determinant one.

This is the conjugacy part of Aschbacher--Smith, *The Classification of
Quasithin Groups*, Lemma A.3.21(a), printed p. 55.
-/

public section

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix
noncomputable section

namespace Matrix.SL3

variable (F : Type*) [Field F]

private def eigPlus {V : Type*} [AddCommGroup V] [Module F V]
    (t : V →ₗ[F] V) : Submodule F V := LinearMap.ker (t - LinearMap.id)

private def eigMinus {V : Type*} [AddCommGroup V] [Module F V]
    (t : V →ₗ[F] V) : Submodule F V := LinearMap.ker (t + LinearMap.id)

private lemma mem_eigPlus {V : Type*} [AddCommGroup V] [Module F V]
    (t : V →ₗ[F] V) (x : V) : x ∈ eigPlus F t ↔ t x = x := by
  simp [eigPlus, LinearMap.mem_ker, sub_eq_zero]

private lemma mem_eigMinus {V : Type*} [AddCommGroup V] [Module F V]
    (t : V →ₗ[F] V) (x : V) : x ∈ eigMinus F t ↔ t x = -x := by
  simp [eigMinus, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

private lemma eigenspaces_compl {V : Type*} [AddCommGroup V] [Module F V]
    (t : V →ₗ[F] V) (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    IsCompl (eigPlus F t) (eigMinus F t) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    rw [mem_eigPlus F t] at hx
    rw [mem_eigMinus F t] at hy
    have he : x = -x := hx.symm.trans hy
    have hz : (2 : F) • x = 0 := by
      calc
        _ = x + x := two_smul F x
        _ = x + -x := congrArg (fun z => x + z) he
        _ = 0 := add_neg_cancel x
    exact (smul_eq_zero.mp hz).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨(2 : F)⁻¹ • (x + t x), ?_, (2 : F)⁻¹ • (x - t x), ?_, ?_⟩
    · rw [mem_eigPlus F t]
      simp only [map_smul, map_add, ht x]
      rw [add_comm]
    · rw [mem_eigMinus F t]
      simp only [map_smul, map_sub, ht x]
      rw [← smul_neg, neg_sub]
    · rw [← smul_add]
      have he : (x + t x) + (x - t x) = (2 : F) • x := by
        rw [two_smul]
        abel
      rw [he, smul_smul, inv_mul_cancel₀ h2, one_smul]

private lemma det_neg_eigenspace (M : Submodule F (Fin 3 → F)) :
    LinearMap.det (-LinearMap.id : M →ₗ[F] M) =
      (-1 : F) ^ Module.finrank F M := by
  let b := Module.Free.chooseBasis F M
  rw [← LinearMap.det_toMatrix b]
  rw [show Module.finrank F M = Fintype.card (Module.Free.ChooseBasisIndex F M) from
    Module.finrank_eq_card_basis b]
  rw [show LinearMap.toMatrix b b (-LinearMap.id) = -(1 : Matrix _ _ F) by
    ext i j
    classical
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]]
  rw [Matrix.det_neg]
  simp

private lemma det_of_involution (t : (Fin 3 → F) →ₗ[F] (Fin 3 → F))
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0) :
    LinearMap.det t = (-1 : F) ^ Module.finrank F (eigMinus F t) := by
  let P := eigPlus F t
  let M := eigMinus F t
  let d := Submodule.prodEquivOfIsCompl P M (eigenspaces_compl F t ht h2)
  have he : d.symm.toLinearMap ∘ₗ t ∘ₗ d.toLinearMap =
      LinearMap.prodMap LinearMap.id (-LinearMap.id) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply d.injective
    change d (d.symm (t (d (x, y)))) = d (x, -y)
    rw [d.apply_symm_apply]
    rw [show d (x, y) = x.1 + y.1 by rfl,
      show d (x, -y) = x.1 + (-y.1) by rfl]
    rw [map_add]
    have hx : t x.1 = x.1 :=
      (mem_eigPlus F t x.1).mp (show x.1 ∈ eigPlus F t from x.2)
    have hy : t y.1 = -y.1 :=
      (mem_eigMinus F t y.1).mp (show y.1 ∈ eigMinus F t from y.2)
    rw [hx, hy]
  have hd := congrArg LinearMap.det he
  have hdet : LinearMap.det (d.symm.toLinearMap ∘ₗ t ∘ₗ d.toLinearMap) =
      LinearMap.det t := by
    simpa only [LinearEquiv.symm_symm] using LinearMap.det_conj t d.symm
  rw [hdet] at hd
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul, det_neg_eigenspace] at hd
  simpa [M] using hd

private lemma minus_finrank_three (t : (Fin 3 → F) →ₗ[F] (Fin 3 → F))
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0)
    (hdet : LinearMap.det t = 1) (hne : t ≠ LinearMap.id) :
    Module.finrank F (eigMinus F t) = 2 := by
  let P := eigPlus F t
  let M := eigMinus F t
  have hc := eigenspaces_compl F t ht h2
  have hd : Module.finrank F P + Module.finrank F M = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P M
    rw [hc.sup_eq_top, hc.inf_eq_bot] at h
    simpa using h.symm
  have hM : M ≠ ⊥ := by
    intro hM
    have hP : P = ⊤ := by
      apply top_unique
      have hc' : P ⊔ M = ⊤ := hc.sup_eq_top
      simpa [hM] using hc'.ge
    apply hne
    apply LinearMap.ext
    intro x
    have hx : x ∈ P := hP ▸ Submodule.mem_top
    exact (mem_eigPlus F t x).mp hx
  have hn0 : 0 < Module.finrank F M := by
    exact Nat.pos_of_ne_zero ((Submodule.finrank_eq_zero.not).mpr hM)
  have hnle : Module.finrank F M ≤ 3 := by
    exact (Submodule.finrank_le M).trans_eq (by simp)
  have hpar : (1 : F) = (-1 : F) ^ Module.finrank F M := by
    calc
      1 = LinearMap.det t := hdet.symm
      _ = (-1 : F) ^ Module.finrank F (eigMinus F t) := det_of_involution F t ht h2
      _ = (-1 : F) ^ Module.finrank F M := by rfl
  change Module.finrank F M = 2
  interval_cases hN : Module.finrank F M
  · simp only [pow_one] at hpar
    exfalso
    apply h2
    linear_combination hpar
  · rfl
  · norm_num at hpar
    exact False.elim (h2 (by linear_combination hpar))

private lemma basis_diagonalize (t : (Fin 3 → F) →ₗ[F] (Fin 3 → F))
    (ht : Function.Involutive t) (h2 : (2 : F) ≠ 0)
    (hM : Module.finrank F (eigMinus F t) = 2)
    (hP : Module.finrank F (eigPlus F t) = 1) :
    ∃ e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F),
      e.toLinearMap ∘ₗ (Matrix.toLin' (!![-1, 0, 0; 0, -1, 0; 0, 0, 1])) =
        t ∘ₗ e.toLinearMap := by
  let M := eigMinus F t
  let P := eigPlus F t
  let hc : IsCompl M P := (eigenspaces_compl F t ht h2).symm
  let bM : Module.Basis (Fin 2) F M :=
    (Module.finBasis F M).reindex (finCongr hM)
  let bP : Module.Basis (Fin 1) F P :=
    (Module.finBasis F P).reindex (finCongr hP)
  let d : (M × P) ≃ₗ[F] (Fin 3 → F) :=
    Submodule.prodEquivOfIsCompl M P hc
  let b0 := bM.prod bP
  let b1 := b0.map d
  let b := b1.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)
  let e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) := b.equivFun.symm
  have hm (x : M) : t x.1 = -x.1 := (mem_eigMinus F t x.1).mp x.2
  have hp (x : P) : t x.1 = x.1 := (mem_eigPlus F t x.1).mp x.2
  have hb0 : t (b 0) = -b 0 := by
    simp only [b, b1, b0, Module.Basis.reindex_apply, Module.Basis.map_apply,
      Module.Basis.prod_apply]
    change t ((bM 0).1 + (0 : P).1) = -((bM 0).1 + (0 : P).1)
    simpa only [Submodule.coe_zero, add_zero] using hm (bM 0)
  have hb1 : t (b 1) = -b 1 := by
    simp only [b, b1, b0, Module.Basis.reindex_apply, Module.Basis.map_apply,
      Module.Basis.prod_apply]
    change t ((bM 1).1 + (0 : P).1) = -((bM 1).1 + (0 : P).1)
    simpa only [Submodule.coe_zero, add_zero] using hm (bM 1)
  have hb2 : t (b 2) = b 2 := by
    simp only [b, b1, b0, Module.Basis.reindex_apply, Module.Basis.map_apply,
      Module.Basis.prod_apply]
    change t ((0 : M).1 + (bP 0).1) = (0 : M).1 + (bP 0).1
    simpa only [Submodule.coe_zero, zero_add] using hp (bP 0)
  refine ⟨e, ?_⟩
  apply LinearMap.ext
  intro x
  have hex (y : Fin 3 → F) : e y = y 0 • b 0 + y 1 • b 1 + y 2 • b 2 := by
    rw [show e y = ∑ i : Fin 3, y i • b i from b.equivFun_symm_apply y]
    exact Fin.sum_univ_three (fun i : Fin 3 => y i • b i)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hex, map_add, map_smul,
    hb0, hb1, hb2]
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Every involution has a diagonalizing conjugator of determinant one. -/
theorem exists_standardInvolution_conjugator
    (z : SpecialLinearGroup (Fin 3) F) (hz : orderOf z = 2)
    (h2 : (2 : F) ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin 3) F,
      s * standardInvolution F * s⁻¹ = z := by
  let t : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := (SpecialLinearGroup.toLin' z).toLinearMap
  have hz2 : z ^ 2 = 1 := by
    rw [← pow_orderOf_eq_one z, hz]
  have ht : Function.Involutive t := by
    intro x
    have hlin := congrArg
      (fun A : SpecialLinearGroup (Fin 3) F => SpecialLinearGroup.toLin' A) hz2
    have hx := congrArg (fun f : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) => f x) hlin
    simpa [t, pow_two] using hx
  have hdet : LinearMap.det t = 1 := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun F (Fin 3))]
    rw [show LinearMap.toMatrix (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3)) t = z.val by
      exact LinearMap.toMatrix_toLin (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3)) z.val]
    exact z.property
  have hne : t ≠ LinearMap.id := by
    intro h
    have hz1 : z = 1 := by
      apply Subtype.ext
      apply Matrix.toLinAlgEquiv'.injective
      change Matrix.toLin' z.val = Matrix.toLin' (1 : Matrix (Fin 3) (Fin 3) F)
      rw [show Matrix.toLin' z.val = t by rfl, h]
      exact Matrix.toLin'_one.symm
    subst z
    simp at hz
  have hM : Module.finrank F (eigMinus F t) = 2 :=
    minus_finrank_three F t ht h2 hdet hne
  have hP : Module.finrank F (eigPlus F t) = 1 := by
    have hc := eigenspaces_compl F t ht h2
    have h := Submodule.finrank_sup_add_finrank_inf_eq (eigPlus F t) (eigMinus F t)
    rw [hc.sup_eq_top, hc.inf_eq_bot, hM] at h
    have hd : Module.finrank F (eigPlus F t) + 2 = 3 := by simpa using h.symm
    omega
  obtain ⟨e, he⟩ := basis_diagonalize F t ht h2 hM hP
  let G : Matrix (Fin 3) (Fin 3) F :=
    LinearMap.toMatrix (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3)) e.toLinearMap
  have hGdet : G.det ≠ 0 :=
    (e.isUnit_det (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3))).ne_zero
  let c : F := G.det⁻¹
  let D : Matrix (Fin 3) (Fin 3) F :=
    Matrix.diagonal (fun i => if i = 0 then c else 1)
  let S : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
  have hcomm : D * S = S * D := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, S, Matrix.mul_apply, Matrix.diagonal_apply]
  have hmatrix : G * S = z.val * G := by
    have hm := congrArg
      (LinearMap.toMatrix (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3))) he
    have htmat : t = Matrix.toLin' z.val := rfl
    rw [htmat] at hm
    rw [LinearMap.toMatrix_comp (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3)),
      LinearMap.toMatrix_comp (Pi.basisFun F (Fin 3)) (Pi.basisFun F (Fin 3))] at hm
    change G * LinearMap.toMatrix' (Matrix.toLin' S) =
      LinearMap.toMatrix' (Matrix.toLin' z.val) * G at hm
    simpa only [LinearMap.toMatrix'_toLin'] using hm
  have hG' : (G * D).det = 1 := by
    rw [Matrix.det_mul]
    simp [D, c, Matrix.det_diagonal, hGdet]
  let s : SpecialLinearGroup (Fin 3) F := ⟨G * D, hG'⟩
  have hmul : s * standardInvolution F = z * s := by
    apply Subtype.ext
    change (G * D) * S = z.val * (G * D)
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hmatrix, Matrix.mul_assoc]
  refine ⟨s, ?_⟩
  rw [hmul, mul_assoc, mul_inv_cancel, mul_one]

/-- Every element of order two in SL₃ is conjugate inside SL₃ to `diag(-1,-1,1)`. -/
theorem involution_isConj_standard (z : SpecialLinearGroup (Fin 3) F)
    (hz : orderOf z = 2) (h2 : (2 : F) ≠ 0) :
    IsConj z (standardInvolution F) := by
  obtain ⟨s, hs⟩ := exists_standardInvolution_conjugator F z hz h2
  exact (isConj_iff.mpr ⟨s, hs⟩).symm

/-- All actual involutions in SL₃ belong to one conjugacy class. -/
theorem involutions_isConj (z w : SpecialLinearGroup (Fin 3) F)
    (hz : orderOf z = 2) (hw : orderOf w = 2) (h2 : (2 : F) ≠ 0) :
    IsConj z w :=
  (involution_isConj_standard F z hz h2).trans
    (involution_isConj_standard F w hw h2).symm

/-- The full centralizer of any involution in SL₃ is isomorphic to GL₂. -/
noncomputable def involutionCentralizerEquiv (z : SpecialLinearGroup (Fin 3) F)
    (hz : orderOf z = 2) (h2 : (2 : F) ≠ 0) :
    Subgroup.centralizer ({z} : Set (SpecialLinearGroup (Fin 3) F)) ≃* GL (Fin 2) F := by
  let hc := isConj_iff.mp (involution_isConj_standard F z hz h2)
  let s := Classical.choose hc
  have hs : s * z * s⁻¹ = standardInvolution F := Classical.choose_spec hc
  let e := MulAut.conj s
  have hez : e z = standardInvolution F := hs
  let ce : Subgroup.centralizer ({z} : Set (SpecialLinearGroup (Fin 3) F)) ≃*
      Subgroup.centralizer ({standardInvolution F} : Set (SpecialLinearGroup (Fin 3) F)) :=
    { toFun := fun x => ⟨e x, Subgroup.mem_centralizer_singleton_iff.mpr (by
        rw [← hez, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp x.property])⟩
      invFun := fun x => ⟨e.symm x, Subgroup.mem_centralizer_singleton_iff.mpr (by
        apply e.injective
        simpa only [map_mul, e.apply_symm_apply, hez] using
          Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
  exact ce.trans (standardInvolutionCentralizerEquiv F h2).symm

end Matrix.SL3

end
