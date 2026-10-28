module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Instance.Diagonal
public import Theory.AlgebraicGroup.Isomorphism

universe u

/-! Basic definitions and point-coordinate facts for algebraic tori. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The one-dimensional multiplicative algebraic group, presented as the
diagonal group `D₁ = GL₁`. -/
public abbrev KMult (k : Type u) [Field k] := dVariety k 1

/-- An algebraic group is a torus when it is isomorphic to a finite direct
product of copies of `KMult`, represented by a diagonal group `D_n`. -/
@[expose]
public def IsTorus (T : Variety k) [AlgebraicGroup T] : Prop :=
  ∃ n : ℕ, Nonempty (AlgebraicGroup.Iso (dVariety k n) T)

/-- A subtorus is a closed subgroup which is a torus. -/
@[expose]
public def IsSubtorus {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) : Prop :=
  IsTorus T.carrierVariety

/-- A maximal torus is maximal among the subtori under inclusion. -/
@[expose]
public def IsMaximalTorus {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) : Prop :=
  IsSubtorus T ∧
    ∀ S : ClosedSubgroup G, IsSubtorus S → T ≤ S → S = T

/-- The diagonal algebraic group `D_n` is the standard rank-`n` torus. -/
public lemma dVariety_isTorus (n : ℕ) : IsTorus (dVariety k n) :=
  ⟨n, ⟨AlgebraicGroup.Iso.id (dVariety k n)⟩⟩

/-- `dPointEquiv` sends the transported identity to the pointwise unit. -/
public lemma dPointEquiv_one (n : ℕ) :
    dPointEquiv n (1 : Variety.Point (dVariety k n)) = 1 := by
  have h : (1 : Variety.Point (dVariety k n)) =
      (dPointEquiv n).symm 1 := by rfl
  rw [h, Equiv.apply_symm_apply]

/-- The entry coordinate of a point reconstructed by `dPointEquiv`. -/
public lemma dPointEquiv_symm_val_inl (n : ℕ) (a : Fin n → kˣ)
    (q : ULift.{u} (Fin n)) :
    ((dPointEquiv n).symm a).val (Sum.inl q) = (a q.down).val := rfl

/-- The inverse-entry coordinate of a point reconstructed by `dPointEquiv`. -/
public lemma dPointEquiv_symm_val_inr (n : ℕ) (a : Fin n → kˣ)
    (q : ULift.{u} (Fin n)) :
    ((dPointEquiv n).symm a).val (Sum.inr q) = (a q.down).inv := rfl

/-- Multiplication in `D_n` is componentwise under `dPointEquiv`. -/
public lemma dPointEquiv_mul (n : ℕ)
    (x y : Variety.Point (dVariety k n)) :
    dPointEquiv n (x * y) = dPointEquiv n x * dPointEquiv n y := by
  change dPointEquiv n
      ((dPointEquiv n).symm (dPointEquiv n x * dPointEquiv n y)) = _
  exact (dPointEquiv n).apply_symm_apply _

/-- Natural powers in `D_n` are componentwise under `dPointEquiv`. -/
public lemma dPointEquiv_pow (n m : ℕ)
    (x : Variety.Point (dVariety k n)) :
    dPointEquiv n (x ^ m) = (dPointEquiv n x) ^ m := by
  induction m with
  | zero => simpa only [pow_zero] using dPointEquiv_one (k := k) n
  | succ m ih => rw [pow_succ, dPointEquiv_mul, ih, pow_succ]

/-- Every ambient coordinate of a product in `D_n` is the product of the
corresponding coordinates. -/
public lemma dPoint_mul_apply (n : ℕ)
    (x y : Variety.Point (dVariety k n))
    (c : (dVariety k n).Coordinates) :
    (x * y).val c = x.val c * y.val c := by
  cases c with
  | inl i =>
      cases i with
      | up i =>
          change dPointEntry n (x * y) i =
            dPointEntry n x i * dPointEntry n y i
          exact congrArg Units.val (congrFun (dPointEquiv_mul n x y) i)
  | inr i =>
      cases i with
      | up i =>
          change dPointEntryInv n (x * y) i =
            dPointEntryInv n x i * dPointEntryInv n y i
          simpa [dPointEquiv, dPoint_unit_inv, mul_comm] using
            congrArg (fun z : kˣ ↦ z.inv)
              (congrFun (dPointEquiv_mul n x y) i)

/-- The diagonal algebraic group `D_n` has commutative point group. -/
public lemma dVariety_isMulCommutative (n : ℕ) :
    IsMulCommutative (Variety.Point (dVariety k n)) := by
  rw [isMulCommutative_iff]
  intro x y
  apply (dPointEquiv n).injective
  rw [dPointEquiv_mul, dPointEquiv_mul]
  exact mul_comm _ _

/-- Every torus has commutative point group. -/
public lemma IsTorus.isMulCommutative
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T) :
    IsMulCommutative (Variety.Point T) := by
  rw [isMulCommutative_iff]
  rcases hT with ⟨n, ⟨e⟩⟩
  intro x y
  have hdiag := dVariety_isMulCommutative (k := k) n
  rw [isMulCommutative_iff] at hdiag
  have h := congrArg e.hom.onPoints
    (hdiag (e.inv.onPoints x) (e.inv.onPoints y))
  simpa only [map_mul, e.inv_hom_id] using h

/-- Every subtorus has commutative point group. -/
public lemma IsSubtorus.isMulCommutative
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} (hT : IsSubtorus T) :
    IsMulCommutative (Variety.Point T.carrierVariety) :=
  IsTorus.isMulCommutative hT

/-- Every nonzero integral exponent is detected by some unit of an
algebraically closed field. -/
public lemma exists_unit_zpow_ne_one [IsAlgClosed k] {z : ℤ} (hz : z ≠ 0) :
    ∃ a : kˣ, a ^ z ≠ 1 := by
  classical
  let m := z.natAbs
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr hz
  let f : Polynomial k :=
    Polynomial.X * (Polynomial.X ^ m - (1 : Polynomial k))
  have hf : f ≠ 0 := by
    apply mul_ne_zero Polynomial.X_ne_zero
      (Polynomial.monic_X_pow_sub_C (1 : k) hm).ne_zero
  have hfcard : f.natDegree < Cardinal.mk k := by
    exact (Cardinal.natCast_lt_aleph0 :
      (f.natDegree : Cardinal) < Cardinal.aleph0).trans_le
        (Cardinal.aleph0_le_mk k)
  obtain ⟨a, ha⟩ :=
    Polynomial.exists_eval_ne_zero_of_natDegree_lt_card f hf hfcard
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    simp [f] at ha
  have hapow : a ^ m ≠ 1 := by
    intro h
    simp [f, h] at ha
  let aUnit : kˣ := Units.mk0 a ha0
  refine ⟨aUnit, ?_⟩
  intro huz
  have hum : aUnit ^ m = 1 :=
    (pow_natAbs_eq_one (a := aUnit) (n := z)).mpr huz
  apply hapow
  simpa [aUnit] using congrArg Units.val hum

end Theory.AlgebraicGroup
