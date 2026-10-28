module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Coordinates
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Diagonal

/-!
# Characteristic-two Hermitian coordinate rigidity

The square formula makes the zero-first-coordinate layer characteristic.
The trace gives a section of the first-coordinate map, so every automorphism
induces an additive field equivalence. Squares and the norm recover the
central layer without division by two. A norm-one torus element with
nontrivial cube eliminates the remaining central shear.

These are the binary Heisenberg calculations for Steinberg's Theorem 36,
steps (2), (4), and (7), `refs/KGroup/GLS3/Chapter2St1.tex`. The root and
diagonal conventions are those of Huppert II.10.12.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)

omit [CharP E 2] in
public theorem coord_first_surjective {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Function.Surjective (fun z : hermitianUnipotentCoord J => z.val.1) := by
  intro a
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a * J.conj a)) (by rw [map_neg, map_mul, J.conj_involutive, mul_comm])
  exact ⟨⟨(a, b), by dsimp only; rw [hb]; ring⟩, rfl⟩

private noncomputable def firstSection {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (a : E) :
    hermitianUnipotentCoord J := (coord_first_surjective J hcard hfixed a).choose

omit [CharP E 2] in
private theorem firstSection_spec {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (a : E) :
    (firstSection J hcard hfixed a).val.1 = a :=
  (coord_first_surjective J hcard hfixed a).choose_spec

omit [Finite E] [CharP E 2] in
private theorem fst_mul (z w : hermitianUnipotentCoord J) :
    (z * w).val.1 = z.val.1 + w.val.1 := rfl
omit [Finite E] [CharP E 2] in
private theorem fst_inv (z : hermitianUnipotentCoord J) :
    z⁻¹.val.1 = -z.val.1 := rfl

omit [Finite E] in
/-- The central coordinate layer consists exactly of elements of square one. -/
public theorem square_eq_one_iff_first_zero (z : hermitianUnipotentCoord J) :
    z ^ 2 = 1 ↔ z.val.1 = 0 := by
  constructor
  · intro h
    have hs := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) h
    rw [EvenInner.square_coordinates] at hs
    change z.val.1 * J.conj z.val.1 = 0 at hs
    exact (mul_eq_zero.mp hs).elim id ((map_eq_zero J.conj).mp)
  · intro hz
    apply Subtype.ext
    rw [EvenInner.square_coordinates, hz, zero_mul]
    rfl

omit [Finite E] in
public theorem coordAut_first_zero (φ : MulAut (hermitianUnipotentCoord J))
    (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    (φ z).val.1 = 0 := by
  apply (square_eq_one_iff_first_zero J (φ z)).mp
  rw [← map_pow, (square_eq_one_iff_first_zero J z).mpr hz, map_one]

omit [Finite E] in
public theorem coordAut_first_eq
    (φ : MulAut (hermitianUnipotentCoord J))
    (z w : hermitianUnipotentCoord J) (hzw : z.val.1 = w.val.1) :
    (φ z).val.1 = (φ w).val.1 := by
  have hh := coordAut_first_zero J φ (z * w⁻¹) (by
    rw [fst_mul, fst_inv, hzw, add_neg_cancel])
  rw [map_mul, map_inv, fst_mul, fst_inv] at hh
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)

public noncomputable def coordFirstAddHom {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J)) : E →+ E where
  toFun a := (φ (firstSection J hcard hfixed a)).val.1
  map_zero' := by
    exact coordAut_first_zero J φ _ (firstSection_spec J hcard hfixed 0)
  map_add' a b := by
    have hh := coordAut_first_eq J φ
      (firstSection J hcard hfixed (a + b)) (firstSection J hcard hfixed a * firstSection J hcard hfixed b) (by simp only [firstSection_spec, fst_mul])
    simpa only [map_mul, fst_mul] using hh

public theorem coordFirstAddHom_apply {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J)) (z : hermitianUnipotentCoord J) :
    coordFirstAddHom J hcard hfixed φ z.val.1 = (φ z).val.1 :=
  coordAut_first_eq J φ _ z (firstSection_spec J hcard hfixed z.val.1)

public theorem coordFirstAddHom_bijective {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J)) :
    Function.Bijective (coordFirstAddHom J hcard hfixed φ) := by
  constructor
  · intro a b hab
    have hh := coordAut_first_eq J φ.symm
      (φ (firstSection J hcard hfixed a)) (φ (firstSection J hcard hfixed b)) hab
    simpa only [φ.symm_apply_apply, firstSection_spec] using hh
  · intro a
    refine ⟨(φ.symm (firstSection J hcard hfixed a)).val.1, ?_⟩
    rw [coordFirstAddHom_apply, φ.apply_symm_apply, firstSection_spec]

public noncomputable def coordFirstAddEquiv {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J)) : E ≃+ E :=
  AddEquiv.ofBijective (coordFirstAddHom J hcard hfixed φ)
    (coordFirstAddHom_bijective J hcard hfixed φ)

public theorem coordFirstAddEquiv_apply {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J)) (z : hermitianUnipotentCoord J) :
    coordFirstAddEquiv J hcard hfixed φ z.val.1 = (φ z).val.1 :=
  coordFirstAddHom_apply J hcard hfixed φ z


end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
