module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry.Generation.Contracts
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Full Levi transports for the marked quotient axis

An automorphism A of the coordinate hyperplane extends to the determinant-one
matrix diag(A, det(A)⁻¹) relative to the hyperplane and complementary coordinate
line. Conjugation sends the shear parameter w to det(A) • A(w). Transporting
this literal matrix through the supplied quotient marking works in either
recorded orientation.

Over the binary prime field, every nonzero determinant is one, so basis
extension transports any independent ordered pair. In a parameter plane,
choose B with B(u) = e, set δ = det(B) and x = δ⁻¹ • B(v). In the basis u,v,
the triangular map with columns (t⁻¹,0) and (a t⁻¹,δ⁻¹ t²), followed by B,
has determinant t. Its twisted action sends u to e and v to a • e + t³ • x.
At a = 0, t = 1 this supplies the initial determinant-one pair transport.

This proves the pair-transport input to axis generation in Aschbacher–Smith,
B.4.9(1), printed pp.92–93 (PDF pp.103–104), combined manuscript of 1 March
2004. The independent identification of original root groups is not used here.
-/

public section

open Representation Representation.BinaryOffender Matrix Module
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviTransport
variable (F : BinaryField) (n : ℕ) (j : Fin n)

private noncomputable def split : (Fin n → F.Carrier) ≃ₗ[F.Carrier]
    (coordinateHyperplane F n j × F.Carrier) where
  toFun v := (⟨v - v j • Pi.single j 1, by simp [mem_coordinateHyperplane]⟩, v j)
  invFun z := z.1.val + z.2 • Pi.single j 1
  left_inv v := sub_add_cancel _ _
  right_inv z := by
    rcases z with ⟨w,c⟩
    have hw : w.val j = 0 := w.property
    apply Prod.ext
    · apply Subtype.ext
      simp [hw]
    · simp [hw]
  map_add' u v := by
    apply Prod.ext
    · apply Subtype.ext
      change (u + v) - (u j + v j) • Pi.single j 1 =
        (u - u j • Pi.single j 1) + (v - v j • Pi.single j 1)
      rw [add_smul]
      abel
    · rfl
  map_smul' c v := by
    apply Prod.ext
    · apply Subtype.ext
      change c • v - (c * v j) • Pi.single j 1 = c • (v - v j • Pi.single j 1)
      rw [smul_sub, smul_smul]
    · rfl

private noncomputable def liftEnd (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) : (Fin n → F.Carrier) →ₗ[F.Carrier] (Fin n → F.Carrier) :=
  (split F n j).symm.toLinearMap ∘ₗ
    (LinearMap.prodMap A.toLinearMap (LinearMap.mulLeft F.Carrier (↑A.det : F.Carrier)⁻¹)) ∘ₗ
    (split F n j).toLinearMap

private lemma liftEnd_det (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) : (liftEnd F n j A).det = 1 := by
  have hc := LinearMap.det_conj
    (LinearMap.prodMap A.toLinearMap (LinearMap.mulLeft F.Carrier (↑A.det : F.Carrier)⁻¹))
    (split F n j).symm
  rw [LinearEquiv.symm_symm] at hc
  rw [liftEnd, hc, LinearMap.det_prodMap, LinearMap.det_mulLeft]
  simpa only [LinearEquiv.coe_det] using mul_inv_cancel₀ (Units.ne_zero A.det)

private noncomputable def lift (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) : Matrix.SpecialLinearGroup (Fin n) F.Carrier :=
  ⟨LinearMap.toMatrix' (liftEnd F n j A), by rw [LinearMap.det_toMatrix', liftEnd_det]⟩

private lemma lift_apply (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) (v : Fin n → F.Carrier) :
    linearNatural F n (lift F n j A) v = liftEnd F n j A v := by
  change Matrix.toLin' (LinearMap.toMatrix' _) v = _
  rw [Matrix.toLin'_toMatrix']

private lemma lift_axis (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) (w : coordinateHyperplane F n j) :
    linearNatural F n (lift F n j A) w.val = (A w).val := by
  rw [lift_apply]
  change (A ⟨w.val - w.val j • Pi.single j 1, _⟩).val +
    ((↑A.det : F.Carrier)⁻¹ * w.val j) • Pi.single j 1 = _
  simp only [show w.val j = 0 from w.property, zero_smul, sub_zero, mul_zero, add_zero]

private lemma lift_coordinate (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) (v : Fin n → F.Carrier) :
    linearNatural F n (lift F n j A) v j = (↑A.det : F.Carrier)⁻¹ * v j := by
  rw [lift_apply]
  change (A _).val j + ((↑A.det : F.Carrier)⁻¹ * v j) * (Pi.single j 1 : Fin n → F.Carrier) j = _
  rw [show (A _).val j = 0 from (A _).property, Pi.single_eq_same, mul_one, zero_add]

private lemma lift_conjugates (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) (w : coordinateHyperplane F n j) :
    lift F n j A * shear F n j w * (lift F n j A)⁻¹ =
      shear F n j ((↑A.det : F.Carrier) • A w) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply natural_injective F n
  apply LinearMap.ext
  intro v
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    shear_apply, shear_apply]
  change specialLinearNatural n _ (v + v j • w.val) = _
  rw [map_add, map_smul]
  change linearNatural F n (lift F n j A) v + v j • linearNatural F n (lift F n j A) w.val = _
  rw [lift_axis, lift_coordinate, Submodule.coe_smul, smul_smul]
  congr 1
  congr 1
  rw [mul_comm (↑A.det : F.Carrier)⁻¹, mul_assoc,
    inv_mul_cancel₀ (Units.ne_zero A.det), mul_one]

end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviTransport

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviTransport
section Parameters
variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]

private lemma pair_map (u v e x : H) (huv : LinearIndependent K ![u,v])
    (hex : LinearIndependent K ![e,x]) :
    ∃ A : H ≃ₗ[K] H, A u = e ∧ A v = x := by
  let f := huv.linearCombinationEquiv.symm.trans hex.linearCombinationEquiv
  obtain ⟨A, hA⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨A, ?_, ?_⟩
  · have h := hA (huv.linearCombinationEquiv (Finsupp.single 0 1))
    simpa [f] using h.symm
  · have h := hA (huv.linearCombinationEquiv (Finsupp.single 1 1))
    simpa [f] using h.symm

private noncomputable def triangle (b : Basis (Fin 2) K H) (r s c : K) : H →ₗ[K] H :=
  b.constr K ![r • b 0, c • b 0 + s • b 1]

omit [FiniteDimensional K H] in
private lemma triangle_det (b : Basis (Fin 2) K H) (r s c : K) :
    (triangle b r s c).det = r*s := by
  rw [← LinearMap.det_toMatrix b]
  have hm : LinearMap.toMatrix b b (triangle b r s c) = !![r,c;0,s] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, triangle]
  rw [hm, Matrix.det_fin_two]
  simp

private noncomputable def triangleEquiv (b : Basis (Fin 2) K H) (r s c : K)
    (hr : r ≠ 0) (hs : s ≠ 0) : H ≃ₗ[K] H :=
  LinearMap.equivOfIsUnitDet (f := triangle b r s c)
    (by rw [triangle_det]; exact isUnit_iff_ne_zero.mpr (mul_ne_zero hr hs))

private lemma triangleEquiv_det (b : Basis (Fin 2) K H) (r s c : K)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    (↑(triangleEquiv b r s c hr hs).det : K) = r*s := by
  rw [LinearEquiv.coe_det, triangleEquiv, LinearMap.coe_equivOfIsUnitDet, triangle_det]

private lemma triangleEquiv_zero (b : Basis (Fin 2) K H) (r s c : K)
    (hr : r ≠ 0) (hs : s ≠ 0) : triangleEquiv b r s c hr hs (b 0) = r • b 0 := by
  simp [triangleEquiv, triangle]

private lemma triangleEquiv_one (b : Basis (Fin 2) K H) (r s c : K)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    triangleEquiv b r s c hr hs (b 1) = c • b 0 + s • b 1 := by
  simp [triangleEquiv, triangle]

omit [FiniteDimensional K H] in
private lemma vector_map (u e : H) (hu : u ≠ 0) (he : e ≠ 0) :
    ∃ B : H ≃ₗ[K] H, B u = e := by
  let bu := LinearEquiv.toSpanNonzeroSingleton K H u hu
  let be := LinearEquiv.toSpanNonzeroSingleton K H e he
  obtain ⟨B,hB⟩ := Submodule.exists_linearEquiv_restrict_eq (bu.symm.trans be)
  refine ⟨B, ?_⟩
  have h := hB (bu 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [bu,be] using h.symm

private lemma plane_cubic (hdim : finrank K H = 2) (u v : H)
    (huv : LinearIndependent K ![u,v]) (e : H) (he : e ≠ 0) :
    ∃ x : H, (∀ w : H, ∃ a b : K, w = a • e + b • x) ∧
      ∀ a t : K, t ≠ 0 → ∃ A : H ≃ₗ[K] H,
        (↑A.det : K) • A u = e ∧ (↑A.det : K) • A v = a • e + t^3 • x := by
  classical
  let b : Basis (Fin 2) K H := basisOfLinearIndependentOfCardEqFinrank huv (by simp [hdim])
  have b0 : b 0 = u := by simp [b]
  have b1 : b 1 = v := by simp [b]
  obtain ⟨B,hBu⟩ := vector_map (K := K) u e (huv.ne_zero 0) he
  let δ : K := ↑B.det
  have hδ : δ ≠ 0 := Units.ne_zero B.det
  let x : H := δ⁻¹ • B v
  refine ⟨x, ?_, ?_⟩
  · intro w
    refine ⟨b.repr (B.symm w) 0, δ * b.repr (B.symm w) 1, ?_⟩
    have h := congrArg B (b.sum_repr (B.symm w))
    simp only [Fin.sum_univ_two, b0, b1, map_add, map_smul, hBu,
      LinearEquiv.apply_symm_apply] at h
    calc
      w = b.repr (B.symm w) 0 • e + b.repr (B.symm w) 1 • B v := h.symm
      _ = _ := ?_
    dsimp [x]
    rw [smul_smul]
    congr 1
    congr 1
    rw [mul_comm δ, mul_assoc, mul_inv_cancel₀ hδ, mul_one]
  · intro a t ht
    let C := triangleEquiv b t⁻¹ (δ⁻¹*t^2) (a*t⁻¹)
      (inv_ne_zero ht) (mul_ne_zero (inv_ne_zero hδ) (pow_ne_zero _ ht))
    let A := C.trans B
    have hd : (↑A.det : K) = t := by
      simp only [A, LinearEquiv.det_trans, Units.val_mul]
      change δ * (↑C.det : K) = t
      rw [triangleEquiv_det]
      field_simp [hδ, ht]
    have hCu : C u = t⁻¹ • u := by
      rw [← b0]
      exact triangleEquiv_zero ..
    have hCv : C v = (a*t⁻¹) • u + (δ⁻¹*t^2) • v := by
      rw [← b0, ← b1]
      exact triangleEquiv_one ..
    refine ⟨A, ?_, ?_⟩
    · rw [hd]
      change t • B (C u) = e
      rw [hCu, map_smul, hBu, smul_smul, mul_inv_cancel₀ ht, one_smul]
    · rw [hd]
      change t • B (C v) = a • e + t^3 • (δ⁻¹ • B v)
      rw [hCv, map_add, map_smul, map_smul, hBu, smul_add, smul_smul, smul_smul, smul_smul]
      congr 1
      · congr 1
        field_simp [ht]
      · congr 1
        ring
end Parameters
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.LeviTransport

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}
  {d : DoubleNatural F n ρ}
namespace QuotientCoordinates
variable (m : QuotientCoordinates d) (j : Fin n)

private noncomputable def fullLeviElement (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) : G :=
  m.action.groupEquiv.symm (LeviTransport.lift F n j A)

private lemma fullLeviElement_conjugates (A : coordinateHyperplane F n j ≃ₗ[F.Carrier]
    coordinateHyperplane F n j) (w : coordinateHyperplane F n j) :
    m.fullLeviElement j A * m.axisShear j w * (m.fullLeviElement j A)⁻¹ =
      m.axisShear j ((↑A.det : F.Carrier) • A w) := by
  simpa only [fullLeviElement, axisShear, map_mul, map_inv] using
    congrArg m.action.groupEquiv.symm (LeviTransport.lift_conjugates F n j A w)

private lemma binary_scalar_one (hF : F.degree = 1) (c : F.Carrier) (hc : c ≠ 0) : c = 1 := by
  have hs : Function.Surjective (algebraMap (ZMod 2) F.Carrier) :=
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp ((field_finrank F).trans hF)).2
  obtain ⟨z,rfl⟩ := hs c
  have hz : z = 0 ∨ z = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z
  rcases hz with rfl | rfl
  · exact (hc (map_zero _)).elim
  · exact map_one _

/-- Every axis automorphism extends to an actual element of the marked group.
Its conjugation action on all shear parameters is the determinant twist.
The same construction applies to both quotient orientations. -/
theorem exists_fullLevi_conjugator
    (A : coordinateHyperplane F n j ≃ₗ[F.Carrier] coordinateHyperplane F n j) :
    ∃ g : G, ∀ w : coordinateHyperplane F n j,
      g * m.axisShear j w * g⁻¹ = m.axisShear j ((↑A.det : F.Carrier) • A w) :=
  ⟨m.fullLeviElement j A, m.fullLeviElement_conjugates j A⟩

/-- The full Levi provides both required simultaneous pair transports. -/
theorem leviPairTransports : m.LeviPairTransports j := by
  constructor
  · intro hF _ u v huv e x hex
    obtain ⟨A,hAu,hAv⟩ := LeviTransport.pair_map u v e x huv hex
    have hd : (↑A.det : F.Carrier) = 1 := binary_scalar_one hF _ (Units.ne_zero A.det)
    obtain ⟨g,hg⟩ := m.exists_fullLevi_conjugator j A
    refine ⟨g, ?_, ?_⟩
    · rw [hg, hd, one_smul, hAu]
    · rw [hg, hd, one_smul, hAv]
  · intro hn u v huv e he
    have hdim : Module.finrank F.Carrier (coordinateHyperplane F n j) = 2 := by
      rw [coordinateHyperplane_finrank, hn]
    obtain ⟨x,hx,ht⟩ := LeviTransport.plane_cubic hdim u v huv e he
    refine ⟨x,hx,?_⟩
    intro a t ht0
    obtain ⟨A,hAu,hAv⟩ := ht a t ht0
    obtain ⟨g,hg⟩ := m.exists_fullLevi_conjugator j A
    refine ⟨g, ?_, ?_⟩
    · rw [hg, hAu]
    · rw [hg, hAv]

end QuotientCoordinates
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
