module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.UnitaryIntertwiner.FiniteStarNorm
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.TraceParameters
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Unitary correction of binary three-space intertwiners

A linear intertwiner between unitary matrices transports one invariant
Hermitian form to another. Their ratio `a = D†D`, for the adjoint relative
to the original Gram matrix, is self-adjoint and commutes with the actor.
The finite binary star-algebra norm theorem gives `a = b†b`, with `b`
still commuting with the actor. Thus `D b⁻¹` is a unitary intertwiner.

The field hypotheses supply a trace-one scalar: conjugation is nontrivial
because `X^(2^s) - X` cannot vanish on a field of order `(2^s)^2`.
The correction itself works for every unitary element, including repeated
factors and scalars, without assuming that the form ratio has odd order.
Odd order is needed only in the equal-trace consumer, which invokes the
published linear-intertwiner theorem.

This discharges the unitary-correction premise of
`BinaryPRegularClasses.isConj_of_trace_eq_of_unitary_corrections`.
Determinant correction is a separate step. Source context: GLS III, 2.8.2,
2.8.6(a), and the SU₃ family in 2.8.10(c), `refs/KGroup/GLS3/chapter2.tex`.
-/

open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses.UnitaryIntertwiner
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- A trace-one scalar corrects a linear intertwiner for the original Hermitian form. -/
public theorem correction_of_trace_one (J : HermitianForm 3 F)
    (t : F) (ht : J.conj t + t = 1)
    (g h : J.unitarySubgroup) (D : GL (Fin 3) F)
    (hD : D * g.val = h.val * D) :
    ∃ U : J.unitarySubgroup, U.val * g.val = h.val * U.val := by
  let : Star F := ⟨J.conj⟩
  let : InvolutiveStar F := ⟨J.conj_involutive⟩
  let : StarMul F := ⟨fun x y => by exact (map_mul J.conj x y).trans (mul_comm _ _)⟩
  let : StarRing F := ⟨fun x y => J.conj.map_add x y⟩
  let M := Matrix (Fin 3) (Fin 3) F
  let : CharP M 2 := charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F M) 2
  let f : GL (Fin 3) F := GeneralLinearGroup.mkOfDetNeZero J.form J.form_nondegenerate
  have hf : f.valᴴ = f.val := by ext i j; exact J.form_hermitian i j
  have hfi : (f⁻¹).valᴴ = (f⁻¹).val := by
    have he := congrArg Matrix.conjTranspose (Units.inv_mul f)
    rw [conjTranspose_mul, conjTranspose_one, hf] at he
    have he' := congrArg (fun A : M => (f⁻¹).val * A) he
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_one] using he'
  let adj : M → M := fun A => (f⁻¹).val * Aᴴ * f.val
  have adj_mul (A B : M) : adj (A * B) = adj B * adj A := by
    dsimp [adj]
    rw [conjTranspose_mul]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  have adj_involutive : Function.Involutive adj := by
    intro A
    dsimp [adj]
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hf, hfi]
    simp only [← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
  have adj_add (A B : M) : adj (A + B) = adj A + adj B := by
    dsimp [adj]
    rw [conjTranspose_add, mul_add, add_mul]
  let : Star M := ⟨adj⟩
  let : InvolutiveStar M := ⟨adj_involutive⟩
  let : StarMul M := ⟨adj_mul⟩
  let : StarRing M := ⟨adj_add⟩
  let : StarModule F M := ⟨fun c A => by
    change adj (c • A) = J.conj c • adj A
    dsimp [adj]
    rw [conjTranspose_smul, mul_smul_comm, smul_mul_assoc]
    rfl⟩
  have unitary_iff (A : GL (Fin 3) F) : A ∈ J.unitarySubgroup ↔ star A * A = 1 := by
    rw [J.mem_unitarySubgroup_iff]
    have he : (star A * A).val = (f⁻¹).val * (J.conjTranspose A.val * f.val * A.val) := by
      change ((f⁻¹).val * A.valᴴ * f.val) * A.val = _
      simp only [mul_assoc]
      rfl
    rw [← Units.val_inj, he]
    change A.valᴴ * f.val * A.val = f.val ↔
      (f⁻¹).val * (A.valᴴ * f.val * A.val) = 1
    constructor
    · intro ha
      change A.valᴴ * f.val * A.val = f.val at ha
      rw [ha, Units.inv_mul]
    · intro ha
      have he' := congrArg (fun X : M => f.val * X) ha
      simpa only [← mul_assoc, Units.mul_inv, one_mul, mul_one] using he'
  have hg : star g.val = g.val⁻¹ :=
    eq_inv_of_mul_eq_one_left ((unitary_iff g.val).mp g.property)
  have hh : star h.val = h.val⁻¹ :=
    eq_inv_of_mul_eq_one_left ((unitary_iff h.val).mp h.property)
  let a : Mˣ := star D * D
  have ha : star a = a := by simp only [a, star_mul, star_star]
  have hag : Commute (a : M) g.val.val := by
    have hs : star g.val * star D = star D * star h.val := by
      rw [← star_mul, hD, star_mul]
    rw [hg, hh] at hs
    have hs' := congrArg (fun X => g.val * X * h.val) hs
    have hsd : star D * h.val = g.val * star D := by
      simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hs'
    have hc : a * g.val = g.val * a := by
      dsimp [a]
      rw [mul_assoc, hD, ← mul_assoc, hsd, mul_assoc]
    exact congrArg Units.val hc
  obtain ⟨b, hb, hbg⟩ := norm_centralizer (A := M) t ht a ha
  change star b * b = star D * D at hb
  let U : GL (Fin 3) F := D * b⁻¹
  have hU : U ∈ J.unitarySubgroup := by
    apply (unitary_iff U).mpr
    change star (D * b⁻¹) * (D * b⁻¹) = 1
    rw [star_mul, star_inv, mul_assoc, ← mul_assoc (star D) D, ← hb]
    simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel]
  refine ⟨⟨U, hU⟩, ?_⟩
  have hc : Commute b g.val := Units.ext (hbg g.val.val hag)
  change (D * b⁻¹) * g.val = h.val * (D * b⁻¹)
  rw [mul_assoc, hc.inv_left.eq, ← mul_assoc, hD, mul_assoc]

/-- The quadratic finite-field hypotheses supply a scalar of Hermitian trace one. -/
public theorem exists_trace_one (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hpow : ∀ x : F, J.conj x = x^(2^s)) :
    ∃ t : F, J.conj t + t = 1 := by
  classical
  let := Fintype.ofFinite F
  have hq : 1 < 2^s := Nat.one_lt_two_pow (by omega)
  have hex : ∃ x : F, J.conj x ≠ x := by
    by_contra! hall
    have he : (Polynomial.X : Polynomial F)^(2^s) = Polynomial.X := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ Function.injective_id
      · intro x
        simpa only [id_eq, Polynomial.eval_pow, Polynomial.eval_X] using
          (hpow x).symm.trans (hall x)
      · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X,
          max_eq_left hq.le, ← Nat.card_eq_fintype_card, hcard]
        nlinarith
    have hd := congrArg Polynomial.natDegree he
    simp only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at hd
    omega
  obtain ⟨x, hx⟩ := hex
  have hd : J.conj x + x ≠ 0 := by
    intro hh
    have : J.conj x = x := by
      have he := congrArg (fun z : F => z + x) hh
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using he
    exact hx this
  refine ⟨x / (J.conj x + x), ?_⟩
  rw [map_div₀, map_add, J.conj_involutive, add_comm x (J.conj x),
    ← add_div, div_self hd]
end Theory.SpecificGroups.SU3.BinaryPRegularClasses.UnitaryIntertwiner

namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Linear intertwiners of odd-order binary SU₃ elements have a unitary correction. -/
public theorem exists_unitary_intertwiner_of_GL_intertwiner
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hpow : ∀ x : F, J.conj x = x^(2^s))
    (g h : J.specialSubgroup) (_hg : ¬ 2 ∣ orderOf g) (_hh : ¬ 2 ∣ orderOf h)
    (D : GL (Fin 3) F) (hD : D * g.val = h.val * D) :
    ∃ U : J.unitarySubgroup, U.val * g.val = h.val * U.val := by
  let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap (ZMod 2) F) (CharP.cast_eq_zero (ZMod 2) 2))
  obtain ⟨t, ht⟩ := UnitaryIntertwiner.exists_trace_one J s hs hcard hpow
  exact UnitaryIntertwiner.correction_of_trace_one J t ht
    ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩
    ⟨h.val, J.specialSubgroup_le_unitarySubgroup h.property⟩ D hD

/-- Equal traces of odd-order binary SU₃ elements give an actual unitary intertwiner. -/
public theorem exists_unitary_intertwiner_of_trace_eq
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2^s)^2) (hpow : ∀ x : F, J.conj x = x^(2^s))
    (g h : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (ht : g.val.val.trace = h.val.val.trace) :
    ∃ U : J.unitarySubgroup, U.val * g.val = h.val * U.val := by
  let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
    simpa only [map_natCast, map_zero] using
      congrArg (algebraMap (ZMod 2) F) (CharP.cast_eq_zero (ZMod 2) 2))
  obtain ⟨D, hD⟩ := exists_GL_intertwiner_of_trace_eq J g h hg hh ht
  exact exists_unitary_intertwiner_of_GL_intertwiner J s hs hcard hpow g h hg hh D hD

end Theory.SpecificGroups.SU3.BinaryPRegularClasses
