module

public import Theory.SpecificGroups.SU3.TorusWeightSpan
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.FirstField

/-!
# Recovering binary unitary field automorphisms from torus intertwining

In characteristic two the zero-first-coordinate subgroup of the Hermitian
root group is exactly the set of elements whose square is one. Thus every
root-group automorphism descends to an additive equivalence of the first
coordinate. Quadratic trace surjectivity supplies its representatives.
Torus intertwining and the prime-power torus-span theorem make this additive
equivalence a scalar multiple of a field automorphism.

The final theorem applies this construction to the literal projective root
and torus preserved by an ambient automorphism. Root-pair normalization and
the second-coordinate compatibility remain the coverage owner's obligations.
Source: Steinberg, Theorem36, steps(2)–(4), refs/KGroup/GLS3/Chapter2St1.tex;
the Hermitian root law is Huppert II.10.12.
-/

noncomputable section
public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryTorusField
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)

private theorem first_zero_of_square_one (z : hermitianUnipotentCoord J)
    (hz : z ^ 2 = 1) : z.val.1 = 0 := by
  have hs := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) hz
  rw [EvenInner.square_coordinates] at hs
  have hm : z.val.1 * J.conj z.val.1 = 0 := hs
  exact (mul_eq_zero.mp hm).elim id ((map_eq_zero J.conj).mp)

private theorem coordAut_first_zero (φ : MulAut (hermitianUnipotentCoord J))
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) : (φ z).val.1 = 0 := by
  have hs : z ^ 2 = 1 := by
    apply Subtype.ext
    rw [EvenInner.square_coordinates, hz, zero_mul]
    rfl
  apply first_zero_of_square_one J
  rw [← map_pow, hs, map_one]

private theorem coordAut_first_eq (φ : MulAut (hermitianUnipotentCoord J))
    (z w : hermitianUnipotentCoord J) (hzw : z.val.1 = w.val.1) :
    (φ z).val.1 = (φ w).val.1 := by
  have hh := coordAut_first_zero J φ (z * w⁻¹) (by
    change z.val.1 + -w.val.1 = 0
    rw [hzw, add_neg_cancel])
  rw [map_mul, map_inv] at hh
  change (φ z).val.1 + -(φ w).val.1 = 0 at hh
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)

variable [Finite E] {q : ℕ} (hcard : Nat.card E = q ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = q)

private def firstSection (a : E) : hermitianUnipotentCoord J :=
  let h := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a * J.conj a)) (by rw [map_neg, map_mul, J.conj_involutive, mul_comm])
  ⟨(a, Classical.choose h), by
    dsimp only
    rw [Classical.choose_spec h]
    ring⟩

omit [CharP E 2] in
private theorem firstSection_fst (a : E) : (firstSection J hcard hfixed a).val.1 = a := by
  rfl

private def firstAddHom (φ : MulAut (hermitianUnipotentCoord J)) : E →+ E where
  toFun a := (φ (firstSection J hcard hfixed a)).val.1
  map_zero' := coordAut_first_zero J φ _ (firstSection_fst J hcard hfixed 0)
  map_add' a b := by
    have h := coordAut_first_eq J φ (firstSection J hcard hfixed (a + b))
      (firstSection J hcard hfixed a * firstSection J hcard hfixed b) (by
        change (firstSection J hcard hfixed (a + b)).val.1 =
          (firstSection J hcard hfixed a).val.1 + (firstSection J hcard hfixed b).val.1
        simp only [firstSection_fst])
    exact h.trans (by rw [map_mul]; rfl)

private theorem firstAddHom_apply (φ : MulAut (hermitianUnipotentCoord J))
    (z : hermitianUnipotentCoord J) :
    firstAddHom J hcard hfixed φ z.val.1 = (φ z).val.1 :=
  coordAut_first_eq J φ _ z (firstSection_fst J hcard hfixed _)

private theorem firstAddHom_bijective (φ : MulAut (hermitianUnipotentCoord J)) :
    Function.Bijective (firstAddHom J hcard hfixed φ) := by
  constructor
  · intro a b hab
    have hh := coordAut_first_eq J φ.symm
      (φ (firstSection J hcard hfixed a)) (φ (firstSection J hcard hfixed b)) hab
    simpa only [φ.symm_apply_apply, firstSection_fst] using hh
  · intro a
    refine ⟨(φ.symm (firstSection J hcard hfixed a)).val.1, ?_⟩
    rw [firstAddHom_apply, φ.apply_symm_apply, firstSection_fst]

private def firstAddEquiv (φ : MulAut (hermitianUnipotentCoord J)) : E ≃+ E :=
  AddEquiv.ofBijective (firstAddHom J hcard hfixed φ) (firstAddHom_bijective J hcard hfixed φ)

private theorem firstAddEquiv_apply (φ : MulAut (hermitianUnipotentCoord J))
    (z : hermitianUnipotentCoord J) :
    firstAddEquiv J hcard hfixed φ z.val.1 = (φ z).val.1 :=
  firstAddHom_apply J hcard hfixed φ z

include hcard hfixed in
/-- On the genuine binary Hermitian root group, torus intertwining forces
a scalar field-automorphism formula on the first coordinate. -/
theorem first_field_of_torus_intertwining (hq : 2 < q)
    (φ : MulAut (hermitianUnipotentCoord J))
    (hact : ∀ k : Eˣ, ∃ l : Eˣ, ∀ z : hermitianUnipotentCoord J,
      φ (hermitianTorusAction J k z) = hermitianTorusAction J l (φ z)) :
    ∃ (σ : E ≃+* E) (t : Eˣ), ∀ z : hermitianUnipotentCoord J,
      (φ z).val.1 = (t : E) * σ z.val.1 := by
  let f₀ := firstAddEquiv J hcard hfixed φ
  have hnz : f₀ 1 ≠ 0 := by simp
  let t : Eˣ := Units.mk0 (f₀ 1) hnz
  let f : E ≃+ E :=
    { toFun := fun a => (t : E)⁻¹ * f₀ a
      invFun := fun a => f₀.symm ((t : E) * a)
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_add' := fun a b => by simp only [map_add, mul_add] }
  have hweight (k : Eˣ) : ∃ l : Eˣ, ∀ a : E,
      f₀ ((torusWeight J k : E) * a) = (torusWeight J l : E) * f₀ a := by
    obtain ⟨l, hl⟩ := hact k
    refine ⟨l, fun a => ?_⟩
    let z := firstSection J hcard hfixed a
    have he := congrArg (fun z : hermitianUnipotentCoord J => z.val.1) (hl z)
    rw [← firstAddEquiv_apply J hcard hfixed φ, hermitianTorusAction_fst,
      hermitianTorusAction_fst, ← firstAddEquiv_apply J hcard hfixed φ] at he
    have hz : z.val.1 = a := firstSection_fst J hcard hfixed a
    rw [hz] at he
    simpa only [f₀, torusWeight_val, div_eq_mul_inv, inv_pow,
      mul_comm, mul_left_comm, mul_assoc] using he
  have hfweight (k : Eˣ) (a : E) : f ((torusWeight J k : E) * a) =
      f (torusWeight J k : E) * f a := by
    obtain ⟨l, hl⟩ := hweight k
    have hl1 := hl 1
    rw [mul_one] at hl1
    change (t : E)⁻¹ * f₀ ((torusWeight J k : E) * a) =
      ((t : E)⁻¹ * f₀ (torusWeight J k : E)) * ((t : E)⁻¹ * f₀ a)
    rw [hl a, hl1]
    change _ = ((t : E)⁻¹ * ((torusWeight J l : E) * (t : E))) * _
    field_simp
  let σ : E ≃+* E :=
    { f with map_mul' := TorusWeightSpan.mul_eq_of_weights J hq hcard f hfweight }
  refine ⟨σ, t, fun z => ?_⟩
  change (φ z).val.1 = (t : E) * ((t : E)⁻¹ * f₀ z.val.1)
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero t), one_mul]
  exact (firstAddEquiv_apply J hcard hfixed φ z).symm

include hcard hfixed in
/-- Application to an ambient projective automorphism preserving the actual
root group and torus. No prime fixed-field assumption is used. -/
theorem root_first_field_of_torus_preserving
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hq : 2 < q)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hT : (rootTorus J hJ).map b.toMonoidHom = rootTorus J hJ) :
    ∃ (σ : E ≃+* E) (t : Eˣ), ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1 :=
  first_field_of_torus_intertwining J hcard hfixed hq (rootCoordinateAut J hJ b hU)
    (rootCoordinateAut_torus_intertwining J hJ b hU hT)

end BenderSuzuki.MatrixGroups.HermitianForm.BinaryTorusField
