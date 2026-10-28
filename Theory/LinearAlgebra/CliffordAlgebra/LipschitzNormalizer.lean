module

public import Theory.LinearAlgebra.QuadraticForm.CartanDieudonne
public import Theory.LinearAlgebra.CliffordAlgebra.EvenCenter
public import Theory.LinearAlgebra.CliffordAlgebra.OddVolume
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Finite odd-dimensional Lipschitz normalizer reverse

This module proves the corrected reverse-normalizer theorem.  The
ordinary Clifford conjugation of an even unit gives a quadratic isometry of
the vector space.  Cartan--Dieudonne factors that isometry into anisotropic
reflections.  Comparing with the corresponding product of Clifford vector
units forces the factorization length to be even: an odd residual, multiplied
by the central odd volume unit, would be an invertible even element
anticommuting with every vector, contradicting the odd-dimensional even-center
calculation.  The remaining even residual is scalar and hence belongs to
Mathlib's generated Lipschitz group.

This supplies the homogeneous reverse implication left as a TODO in Mathlib's
`SpinGroup` module.  The explicit evenness premise is essential: in odd
dimension, mixed-parity central units preserve the vector range but need not
belong to the generated Lipschitz group.
-/

open CliffordAlgebra
open scoped Pointwise

universe u

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [Invertible (2 : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

omit [FiniteDimensional k V] in
private lemma cliffordIota_injective :
    Function.Injective (CliffordAlgebra.ι Q) := by
  intro v w hvw
  apply (ExteriorAlgebra.ι_leftInverse (R := k) (M := V)).injective
  have h := congrArg (CliffordAlgebra.equivExterior Q) hvw
  simpa [CliffordAlgebra.equivExterior,
    CliffordAlgebra.changeFormEquiv_apply, CliffordAlgebra.changeForm_ι] using h

private noncomputable def normalizerIotaEquivRange :
    V ≃ₗ[k] LinearMap.range (CliffordAlgebra.ι Q) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι Q)
    (cliffordIota_injective (Q := Q))

private noncomputable def normalizerConjLinearEquiv
    (x : (CliffordAlgebra Q)ˣ) :
    CliffordAlgebra Q ≃ₗ[k] CliffordAlgebra Q :=
  DistribMulAction.toLinearEquiv k (CliffordAlgebra Q)
    (ConjAct.toConjAct x)

private noncomputable def normalizerConjRangeEquiv
    (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) :
    LinearMap.range (CliffordAlgebra.ι Q) ≃ₗ[k]
      LinearMap.range (CliffordAlgebra.ι Q) :=
  (normalizerConjLinearEquiv (Q := Q) x).submoduleMap
      (LinearMap.range (CliffordAlgebra.ι Q)) |>.trans
    (LinearEquiv.ofEq _ _ hx)

private noncomputable def normalizerLinearEquiv
    (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) : V ≃ₗ[k] V :=
  (normalizerIotaEquivRange (Q := Q)).trans <|
    (normalizerConjRangeEquiv (Q := Q) x hx).trans
      (normalizerIotaEquivRange (Q := Q)).symm

omit [FiniteDimensional k V] in
private lemma normalizerLinearEquiv_spec
    (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) (v : V) :
    CliffordAlgebra.ι Q (normalizerLinearEquiv x hx v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        (↑(x⁻¹) : CliffordAlgebra Q) := by
  change CliffordAlgebra.ι Q
      ((normalizerIotaEquivRange (Q := Q)).symm
        (normalizerConjRangeEquiv (Q := Q) x hx
          (normalizerIotaEquivRange (Q := Q) v))) = _
  have hrange := congrArg Subtype.val
    ((normalizerIotaEquivRange (Q := Q)).apply_symm_apply
      (normalizerConjRangeEquiv (Q := Q) x hx
        (normalizerIotaEquivRange (Q := Q) v)))
  change ((normalizerIotaEquivRange (Q := Q))
    ((normalizerIotaEquivRange (Q := Q)).symm
      (normalizerConjRangeEquiv (Q := Q) x hx
        (normalizerIotaEquivRange (Q := Q) v)))).val = _
  rw [hrange]
  rfl

omit [FiniteDimensional k V] in
private lemma normalizerLinearEquiv_preserves
    (x : (CliffordAlgebra Q)ˣ)
    (hx : ConjAct.toConjAct x • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q)) (v : V) :
    Q (normalizerLinearEquiv x hx v) = Q v := by
  have hs := congrArg (fun z : CliffordAlgebra Q => z * z)
    (normalizerLinearEquiv_spec x hx v)
  rw [CliffordAlgebra.ι_sq_scalar] at hs
  have hconj :
      ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
          ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) =
        algebraMap k (CliffordAlgebra Q) (Q v) := by
    calc
      ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
            ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) =
          (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
            (↑(x⁻¹) * (x : CliffordAlgebra Q)) *
              CliffordAlgebra.ι Q v * ↑(x⁻¹) := by noncomm_ring
      _ = (x : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) * ↑(x⁻¹) := by
        rw [Units.inv_mul]
        simp [mul_assoc]
      _ = (x : CliffordAlgebra Q) *
          algebraMap k (CliffordAlgebra Q) (Q v) * ↑(x⁻¹) := by
        rw [CliffordAlgebra.ι_sq_scalar]
      _ = algebraMap k (CliffordAlgebra Q) (Q v) *
          (x : CliffordAlgebra Q) * ↑(x⁻¹) := by
        rw [Algebra.commutes]
      _ = algebraMap k (CliffordAlgebra Q) (Q v) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
  change algebraMap k (CliffordAlgebra Q)
      (Q (normalizerLinearEquiv x hx v)) =
    ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
      ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) at hs
  rw [hconj] at hs
  let _ : Nontrivial (CliffordAlgebra Q) :=
    (CliffordAlgebra.equivExterior Q).symm.injective.nontrivial
  exact (FaithfulSMul.algebraMap_injective k (CliffordAlgebra Q)) hs

omit [FiniteDimensional k V] in
private lemma cliffordVectorUnit_conjugation_reflection
    (a : {v : V // Q v ≠ 0}) (v : V) :
    (cliffordAnisotropicVectorUnit a : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v *
          (↑((cliffordAnisotropicVectorUnit a)⁻¹) : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q
        (-QuadraticForm.anisotropicReflection Q a.1 a.2 v) := by
  let _ : Invertible (Q a.1) := invertibleOfNonzero a.2
  let _ : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  rw [← invOf_units (cliffordAnisotropicVectorUnit a)]
  simp only [cliffordAnisotropicVectorUnit_coe]
  change CliffordAlgebra.ι Q a.1 * CliffordAlgebra.ι Q v *
      ⅟(CliffordAlgebra.ι Q a.1) = _
  rw [CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  apply congrArg (CliffordAlgebra.ι Q)
  rw [QuadraticForm.anisotropicReflection_apply]
  have hpolar : QuadraticMap.polar Q a.1 v =
      2 * QuadraticMap.associated Q a.1 v := by
    have h := DFunLike.congr_fun (DFunLike.congr_fun
      (QuadraticMap.two_nsmul_associated k Q) a.1) v
    simpa [two_smul, two_mul] using h.symm
  rw [hpolar, invOf_eq_inv]
  module

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma cliffordVectorUnits_prod_mem_lipschitzGroup
    (vs : List {v : V // Q v ≠ 0}) :
    (vs.map cliffordAnisotropicVectorUnit).prod ∈ lipschitzGroup Q := by
  apply (lipschitzGroup Q).list_prod_mem
  intro z hz
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
  exact cliffordAnisotropicVectorUnit_mem_lipschitzGroup v

omit [FiniteDimensional k V] in
private lemma cliffordVectorUnits_prod_conjugation
    (vs : List {v : V // Q v ≠ 0}) (v : V) :
    CliffordAlgebra.ι Q
        (((-1 : k) ^ vs.length) •
          QuadraticForm.anisotropicReflectionsProduct Q vs v) =
      ((vs.map cliffordAnisotropicVectorUnit).prod : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q v *
          (↑((vs.map cliffordAnisotropicVectorUnit).prod⁻¹) :
            CliffordAlgebra Q) := by
  induction vs with
  | nil => simp
  | cons a vs ih =>
      have hvec :
          ((-1 : k) ^ (a :: vs).length) •
              QuadraticForm.anisotropicReflectionsProduct Q (a :: vs) v =
            -QuadraticForm.anisotropicReflection Q a.1 a.2
              (((-1 : k) ^ vs.length) •
                QuadraticForm.anisotropicReflectionsProduct Q vs v) := by
        simp only [List.length_cons,
          QuadraticForm.anisotropicReflectionsProduct_cons,
          LinearEquiv.mul_apply, map_smul, pow_succ]
        module
      rw [hvec, ← cliffordVectorUnit_conjugation_reflection, ih]
      simp only [List.map_cons, List.prod_cons, Units.val_mul, mul_inv_rev]
      simp [mul_assoc]

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma cliffordVectorUnit_inv_mem_odd
    (a : {v : V // Q v ≠ 0}) :
    (↑((cliffordAnisotropicVectorUnit a)⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q 1 := by
  let _ : Invertible (Q a.1) := invertibleOfNonzero a.2
  let _ : Invertible (CliffordAlgebra.ι Q a.1) :=
    CliffordAlgebra.invertibleιOfInvertible Q a.1
  rw [← invOf_units (cliffordAnisotropicVectorUnit a)]
  simp only [cliffordAnisotropicVectorUnit_coe]
  rw [CliffordAlgebra.invOf_ι]
  exact CliffordAlgebra.ι_mem_evenOdd_one Q _

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma cliffordVectorUnits_prod_inv_mem_evenOdd
    (vs : List {v : V // Q v ≠ 0}) :
    (↑((vs.map cliffordAnisotropicVectorUnit).prod⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (vs.length : ZMod 2) := by
  induction vs with
  | nil => simpa using
      (SetLike.one_mem_graded (A := CliffordAlgebra.evenOdd Q))
  | cons a vs ih =>
      simp only [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul]
      simpa [add_comm] using SetLike.mul_mem_graded ih
        (cliffordVectorUnit_inv_mem_odd a)

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma commutes_even_of_commutes_iota
    (z : CliffordAlgebra Q)
    (hz : ∀ v : V, z * CliffordAlgebra.ι Q v =
      CliffordAlgebra.ι Q v * z) :
    ∀ y : CliffordAlgebra Q, y ∈ CliffordAlgebra.even Q →
      z * y = y * z := by
  intro y hy
  induction y, hy using CliffordAlgebra.even_induction Q with
  | algebraMap r => exact (Algebra.commutes r z).symm
  | add a b ha hb iha ihb => rw [mul_add, add_mul, iha, ihb]
  | ι_mul_ι_mul a b y hy ih =>
      calc
        z * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * y) =
            (z * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q b * y := by
              simp only [mul_assoc]
        _ = (CliffordAlgebra.ι Q a * z) * CliffordAlgebra.ι Q b * y := by
              rw [hz a]
        _ = CliffordAlgebra.ι Q a * (z * CliffordAlgebra.ι Q b) * y := by
              simp only [mul_assoc]
        _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * (z * y) := by
              rw [hz b]
              simp only [mul_assoc]
        _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * (y * z) := by
              rw [ih]
        _ = (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * y) * z := by
              simp only [mul_assoc]

omit [Invertible (2 : k)] [FiniteDimensional k V] in
private lemma commutes_even_of_anticommutes_iota
    (z : CliffordAlgebra Q)
    (hz : ∀ v : V, z * CliffordAlgebra.ι Q v =
      -(CliffordAlgebra.ι Q v * z)) :
    ∀ y : CliffordAlgebra Q, y ∈ CliffordAlgebra.even Q →
      z * y = y * z := by
  intro y hy
  induction y, hy using CliffordAlgebra.even_induction Q with
  | algebraMap r => exact (Algebra.commutes r z).symm
  | add a b ha hb iha ihb => rw [mul_add, add_mul, iha, ihb]
  | ι_mul_ι_mul a b y hy ih =>
      calc
        z * (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * y) =
            (z * CliffordAlgebra.ι Q a) * CliffordAlgebra.ι Q b * y := by
              simp only [mul_assoc]
        _ = (-(CliffordAlgebra.ι Q a * z)) *
            CliffordAlgebra.ι Q b * y := by rw [hz a]
        _ = -(CliffordAlgebra.ι Q a *
            (z * CliffordAlgebra.ι Q b) * y) := by noncomm_ring
        _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * (z * y) := by
              rw [hz b]
              noncomm_ring
        _ = CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * (y * z) := by
              rw [ih]
        _ = (CliffordAlgebra.ι Q a * CliffordAlgebra.ι Q b * y) * z := by
              simp only [mul_assoc]

private lemma no_even_unit_anticommutes_iota
    (hQ : Q.Nondegenerate) (hodd : Odd (Module.finrank k V))
    (hpos : 0 < Module.finrank k V) (z : (CliffordAlgebra Q)ˣ)
    (hzEven : (z : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q)
    (hz : ∀ v : V, (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
      -(CliffordAlgebra.ι Q v * (z : CliffordAlgebra Q))) : False := by
  have hcomm := commutes_even_of_anticommutes_iota (Q := Q)
    (z : CliffordAlgebra Q) hz
  obtain ⟨a, ha⟩ :=
    CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_even
      hQ hodd (z : CliffordAlgebra Q) hzEven hcomm
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hcommv : (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
      CliffordAlgebra.ι Q v * (z : CliffordAlgebra Q) := by
    rw [ha]
    exact Algebra.commutes a (CliffordAlgebra.ι Q v)
  have hneg := hz v
  rw [← hcommv] at hneg
  have hadd :
      (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v +
        (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v = 0 :=
    eq_neg_iff_add_eq_zero.mp hneg
  have hsmul : (2 : k) •
      ((z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v) = 0 := by
    simpa [two_smul] using hadd
  have hzero : (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v = 0 :=
    (smul_eq_zero.mp hsmul).resolve_left two_ne_zero
  have hiotaZero := congrArg
    (fun q : CliffordAlgebra Q => (↑(z⁻¹) : CliffordAlgebra Q) * q) hzero
  have hiotaZero' : CliffordAlgebra.ι Q v = 0 := by
    simpa [mul_assoc] using hiotaZero
  apply hv
  apply cliffordIota_injective (Q := Q)
  simpa using hiotaZero'

/-- In finite positive odd dimension, an even Clifford unit whose ordinary
conjugation stabilizes the embedded vector range lies in Mathlib's generated
Lipschitz group. -/
public theorem mem_lipschitzGroup_of_mem_even_of_conjAct_smul_range_ι_eq
    [IsAlgClosed k] (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) (hodd : Odd (Module.finrank k V))
    (x : (CliffordAlgebra Q)ˣ)
    (hxEven : (x : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q)
    (hxRange : ConjAct.toConjAct x •
      LinearMap.range (CliffordAlgebra.ι Q) =
        LinearMap.range (CliffordAlgebra.ι Q)) :
    x ∈ lipschitzGroup Q := by
  let g : V ≃ₗ[k] V := normalizerLinearEquiv x hxRange
  have hg : ∀ v : V, Q (g v) = Q v := by
    intro v
    exact normalizerLinearEquiv_preserves x hxRange v
  obtain ⟨vs, _hlen, hfactor⟩ :=
    QuadraticForm.cartanDieudonne Q hQ g hg
  let p : (CliffordAlgebra Q)ˣ :=
    (vs.map cliffordAnisotropicVectorUnit).prod
  let z : (CliffordAlgebra Q)ˣ := p⁻¹ * x
  have hpMem : p ∈ lipschitzGroup Q :=
    cliffordVectorUnits_prod_mem_lipschitzGroup vs
  have hpInvGrade : (↑(p⁻¹) : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (vs.length : ZMod 2) :=
    cliffordVectorUnits_prod_inv_mem_evenOdd vs
  have hzGrade : (z : CliffordAlgebra Q) ∈
      CliffordAlgebra.evenOdd Q (vs.length : ZMod 2) := by
    simpa [z] using SetLike.mul_mem_graded hpInvGrade hxEven
  have hxSpec (v : V) : CliffordAlgebra.ι Q (g v) =
      (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹) := by
    exact normalizerLinearEquiv_spec x hxRange v
  have hvsEven : Even vs.length := by
    by_contra hnotEven
    have hvsOdd : Odd vs.length := Nat.not_even_iff_odd.mp hnotEven
    have hsign : (-1 : k) ^ vs.length = -1 := hvsOdd.neg_one_pow
    have hpNeg (v : V) :
        (p : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(p⁻¹) =
          -((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) := by
      rw [← cliffordVectorUnits_prod_conjugation vs v]
      simp only [hsign, neg_one_smul, map_neg]
      rw [← hfactor, hxSpec]
    have hzOdd : (z : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 1 := by
      have hcast : (vs.length : ZMod 2) = 1 := hvsOdd.natCast_zmod_two
      rwa [hcast] at hzGrade
    have hzAnti (v : V) :
        (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
          -(CliffordAlgebra.ι Q v * (z : CliffordAlgebra Q)) := by
      have hxNeg :
          (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹) =
            -((p : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(p⁻¹)) := by
        rw [hpNeg v]
        simp
      change (↑(p⁻¹ * x) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
        -(CliffordAlgebra.ι Q v * (↑(p⁻¹ * x) : CliffordAlgebra Q))
      simp only [Units.val_mul]
      calc
        ↑(p⁻¹) * (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
            ↑(p⁻¹) *
              ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
                (x : CliffordAlgebra Q) := by simp [mul_assoc]
        _ = ↑(p⁻¹) *
              (-((p : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(p⁻¹))) *
                (x : CliffordAlgebra Q) := by rw [hxNeg]
        _ = -(CliffordAlgebra.ι Q v *
              (↑(p⁻¹) * (x : CliffordAlgebra Q))) := by
            simp [mul_assoc]
    obtain ⟨omega, _, homegaOdd, homegaComm⟩ :=
      exists_odd_cliffordVolumeUnit hQ hodd
    let w : (CliffordAlgebra Q)ˣ := omega * z
    have hwEven : (w : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
      have hwGrade := SetLike.mul_mem_graded homegaOdd hzOdd
      change (↑(omega * z) : CliffordAlgebra Q) ∈
        CliffordAlgebra.evenOdd Q 0
      rw [← show (1 + 1 : ZMod 2) = 0 by decide]
      exact hwGrade
    have hwAnti (v : V) :
        (w : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
          -(CliffordAlgebra.ι Q v * (w : CliffordAlgebra Q)) := by
      change (↑(omega * z) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
        -(CliffordAlgebra.ι Q v * (↑(omega * z) : CliffordAlgebra Q))
      simp only [Units.val_mul]
      calc
        (omega : CliffordAlgebra Q) * (z : CliffordAlgebra Q) *
            CliffordAlgebra.ι Q v =
          (omega : CliffordAlgebra Q) *
            ((z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v) := by
              simp only [mul_assoc]
        _ = (omega : CliffordAlgebra Q) *
            (-(CliffordAlgebra.ι Q v * (z : CliffordAlgebra Q))) := by
              rw [hzAnti]
        _ = -((omega : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
            (z : CliffordAlgebra Q)) := by noncomm_ring
        _ = -(CliffordAlgebra.ι Q v *
            ((omega : CliffordAlgebra Q) * (z : CliffordAlgebra Q))) := by
              rw [(homegaComm v).eq]
              simp only [mul_assoc]
    exact no_even_unit_anticommutes_iota hQ hodd hpos w hwEven hwAnti |>.elim
  have hcast : (vs.length : ZMod 2) = 0 := hvsEven.natCast_zmod_two
  have hzEven : (z : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
    rwa [hcast] at hzGrade
  have hsign : (-1 : k) ^ vs.length = 1 := Even.neg_one_pow hvsEven
  have hpSpec (v : V) :
      (p : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(p⁻¹) =
        (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹) := by
    rw [← cliffordVectorUnits_prod_conjugation vs v]
    simp only [hsign, one_smul]
    rw [← hfactor, hxSpec]
  have hzComm (v : V) :
      (z : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
        CliffordAlgebra.ι Q v * (z : CliffordAlgebra Q) := by
    change (↑(p⁻¹ * x) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
      CliffordAlgebra.ι Q v * (↑(p⁻¹ * x) : CliffordAlgebra Q)
    simp only [Units.val_mul]
    calc
      ↑(p⁻¹) * (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v =
          ↑(p⁻¹) *
            ((x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(x⁻¹)) *
              (x : CliffordAlgebra Q) := by simp [mul_assoc]
      _ = ↑(p⁻¹) *
            ((p : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * ↑(p⁻¹)) *
              (x : CliffordAlgebra Q) := by rw [← hpSpec]
      _ = CliffordAlgebra.ι Q v *
          (↑(p⁻¹) * (x : CliffordAlgebra Q)) := by simp [mul_assoc]
  obtain ⟨a, ha⟩ :=
    CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_even
      hQ hodd (z : CliffordAlgebra Q) hzEven
        (commutes_even_of_commutes_iota (Q := Q) (z : CliffordAlgebra Q) hzComm)
  have hzMem : z ∈ lipschitzGroup Q :=
    cliffordScalarUnit_mem_lipschitzGroup hQ hpos z a ha
  have hxp : x = p * z := by
    simp [z]
  rw [hxp]
  exact (lipschitzGroup Q).mul_mem hpMem hzMem

end Theory.AlgebraicGroup
