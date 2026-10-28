module

public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Matrix lifts of elementary projective three-subgroups

The full preimage in GL₃ of a projective subgroup maps onto that subgroup,
with kernel exactly the scalar matrices. Thus its order is the projective
order times the order of the field's unit group. For an elementary abelian
three-subgroup in characteristic different from three, this order is nonzero
in the coefficient field. This supplies the semisimplicity input for the
commuting-lift argument. Injectivity under field extension ensures that
passing to an algebraic closure preserves the literal projective quotient.

Source: the dimension-three case in Aschbacher–Smith, *The Classification
of Quasithin Groups*, A.2.17 and Remark A.2.14, printed pp.37–39.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups IsMulCommutative
namespace Matrix.ProjectiveDimensionThree
variable {F E : Type*} [Field F] [Field E]

/-- Extension of the coefficient field is faithful on matrices. -/
lemma matrix_map_injective (f : F →+* E) :
    Function.Injective (GeneralLinearGroup.map (n := Fin 3) f) := by
  intro a b h
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun c : GL (Fin 3) E => c i j) h

/-- Extension of the coefficient field is faithful modulo scalar matrices. -/
lemma projective_map_injective (f : F →+* E) :
    Function.Injective (ProjGenLinGroup.map (n := Fin 3) f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  induction x using ProjGenLinGroup.induction_on with | mk g =>
    apply ProjGenLinGroup.mk_eq_one.mpr
    have hc := ProjGenLinGroup.mk_eq_one.mp hx
    apply Subgroup.mem_center_iff.mpr
    intro k
    apply matrix_map_injective f
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (GeneralLinearGroup.map f k)

/-- The full matrix preimage of a subgroup of the actual PGL₃. -/
abbrev matrixLift (A : Subgroup PGL(3,F)) : Subgroup (GL (Fin 3) F) :=
  A.comap ProjGenLinGroup.mk

/-- Restriction of the literal quotient map to the full preimage. -/
def liftProjection (A : Subgroup PGL(3,F)) : matrixLift A →* A :=
  (ProjGenLinGroup.mk.comp (matrixLift A).subtype).codRestrict A (fun g => g.property)

lemma liftProjection_surjective (A : Subgroup PGL(3,F)) :
    Function.Surjective (liftProjection A) := by
  rintro ⟨a, ha⟩
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective a
  exact ⟨⟨g, ha⟩, rfl⟩

lemma scalar_mem_lift (A : Subgroup PGL(3,F)) (u : Fˣ) :
    GeneralLinearGroup.scalar (Fin 3) u ∈ matrixLift A := by
  change ProjGenLinGroup.mk _ ∈ A
  simp

/-- The scalar kernel, identified with the field units using actual matrices. -/
noncomputable def liftKernelEquivUnits (A : Subgroup PGL(3,F)) :
    (liftProjection A).ker ≃* Fˣ := by
  let f : Fˣ →* (liftProjection A).ker := {
    toFun := fun u => ⟨⟨GeneralLinearGroup.scalar (Fin 3) u, scalar_mem_lift A u⟩, by
      apply Subtype.ext
      exact ProjGenLinGroup.mk_scalar u⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
    map_mul' := by intro u v; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _ }
  apply (MulEquiv.ofBijective f ?_).symm
  constructor
  · intro u v h
    apply Units.ext
    have hh := congrArg (fun g : (liftProjection A).ker => g.val.val 0 0) h
    simpa [f, GeneralLinearGroup.coe_scalar] using hh
  · rintro ⟨g, hg⟩
    have hc : g.val ∈ Subgroup.center (GL (Fin 3) F) :=
      ProjGenLinGroup.mk_eq_one.mp (congrArg Subtype.val hg)
    rw [GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨u, hu⟩ := hc
    exact ⟨u, Subtype.ext (Subtype.ext hu)⟩

/-- The order of the full matrix preimage. -/
lemma lift_card_eq (A : Subgroup PGL(3,F)) :
    Nat.card (matrixLift A) = Nat.card A * Nat.card Fˣ := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (liftProjection A).ker]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (liftProjection A) (liftProjection_surjective A)).toEquiv]
  rw [Nat.card_congr (liftKernelEquivUnits A).toEquiv]

/-- Nondefining characteristic makes the matrix lift a coprime representation group. -/
lemma lift_card_ne_zero [Finite F] (h3 : (3 : F) ≠ 0)
    (A : Subgroup PGL(3,F)) [IsElementaryAbelian 3 A] :
    (Nat.card (matrixLift A) : F) ≠ 0 := by
  classical
  let : Finite PGL(3,F) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let := Fintype.ofFinite F
  rw [lift_card_eq, Nat.cast_mul]
  apply mul_ne_zero
  · obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 A).exists_card_eq
    rw [hn, Nat.cast_pow]
    exact pow_ne_zero n h3
  · have h := FiniteField.card_cast_subgroup_card_ne_zero (K := F) (⊤ : Subgroup Fˣ)
    simpa only [← Nat.card_eq_fintype_card, Nat.card_congr (Subgroup.topEquiv.toEquiv)] using h
end Matrix.ProjectiveDimensionThree
