module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Model
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinates for the Hermitian symplectic tensor

A nonidentity automorphism of a quadratic extension has a one-dimensional
fixed coefficient space, identified with the embedded base field. Four fixed
diagonal entries and six arbitrary upper entries give coordinates on the
literal Hermitian model. Transpose-fixed matrices instead have ten fixed
coefficients. These coordinates prove dimensions 16 and 10; rank-nullity
then gives displacement dimension 6.

The calculations only require a finite-dimensional quadratic extension;
characteristic two is needed later for the displacement/fixed quotient.
Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457, with the method of
H.4.4(6), printed p.381. Compare the three-dimensional coordinate calculation
in `Theory.Representation.HermitianTensorThree` and its `FieldInvolution` module.
-/

@[expose] public section

open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
noncomputable section
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (σ : F ≃ₐ[k] F) (hσ : Function.Involutive σ)

def fixedCoefficients : Submodule k F := LinearMap.ker (σ.toLinearMap - LinearMap.id)

lemma mem_fixedCoefficients (x : F) : x ∈ fixedCoefficients σ ↔ σ x = x := by
  change σ x - x = 0 ↔ _
  exact sub_eq_zero

lemma finrank_fixedCoefficients [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    Module.finrank k (fixedCoefficients σ) = 1 := by
  have hi : LinearMap.range (Algebra.linearMap k F) ≤ fixedCoefficients σ := by
    rintro x ⟨a, rfl⟩
    exact (mem_fixedCoefficients σ _).mpr (σ.commutes a)
  have hd : Module.finrank k (LinearMap.range (Algebra.linearMap k F)) = 1 := by
    rw [LinearMap.finrank_range_of_inj (FaithfulSMul.algebraMap_injective k F)]
    exact Module.finrank_self k
  have htop : fixedCoefficients σ ≠ ⊤ := by
    intro h
    apply hne
    ext x
    exact (mem_fixedCoefficients σ x).mp (h ▸ Submodule.mem_top)
  have hl := Submodule.finrank_mono hi
  have hu := Submodule.finrank_lt htop
  rw [hd] at hl
  rw [hdeg] at hu
  omega

/-- The base-field embedding, with codomain the actual fixed coefficients. -/
def coefficientMap : k →ₗ[k] fixedCoefficients σ :=
  (Algebra.linearMap k F).codRestrict (fixedCoefficients σ)
    (fun a => (mem_fixedCoefficients σ _).mpr (σ.commutes a))

@[simp] lemma coefficientMap_val (a : k) :
    (coefficientMap σ a).val = algebraMap k F a := rfl

/-- Quadraticity and nontriviality identify the base field with the fixed coefficients. -/
def coefficientEquiv [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    k ≃ₗ[k] fixedCoefficients σ := by
  have hi : Function.Injective (coefficientMap σ) := by
    intro a b hab
    exact (algebraMap k F).injective (congrArg Subtype.val hab)
  have hd : Module.finrank k k = Module.finrank k (fixedCoefficients σ) := by
    rw [Module.finrank_self, finrank_fixedCoefficients σ hdeg hne]
  exact LinearEquiv.ofBijective (coefficientMap σ)
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩

@[simp] lemma coefficientEquiv_val [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) (a : k) :
    (coefficientEquiv σ hdeg hne a).val = algebraMap k F a := rfl

lemma fixed_iff_exists_base [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) (x : F) :
    σ x = x ↔ ∃ a : k, algebraMap k F a = x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (coefficientEquiv σ hdeg hne).surjective
      ⟨x, (mem_fixedCoefficients σ x).mpr hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, rfl⟩
    exact σ.commutes a

abbrev Index := Fin 2 ⊕ Fin 2
abbrev indexOrder : Index ≃ Fin 4 := finSumFinEquiv
abbrev Upper := {p : Index × Index // indexOrder p.1 < indexOrder p.2}

lemma card_upper : Fintype.card Upper = 6 := by decide

def coordinates : Space σ hσ ≃ₗ[k]
    ((Index → fixedCoefficients σ) × (Upper → F)) where
  toFun X := (fun i => ⟨X.val i i, (mem_fixedCoefficients σ _).mpr (entry_conjugate σ hσ X i i)⟩,
    fun p => X.val p.val.1 p.val.2)
  invFun v := ⟨fun i j => if hij : i = j then (v.1 i).val
    else if hlt : indexOrder i < indexOrder j then v.2 ⟨(i,j), hlt⟩
    else σ (v.2 ⟨(j,i), lt_of_le_of_ne (le_of_not_gt hlt)
      (fun h => hij (indexOrder.injective h.symm))⟩), by
    ext i j
    change σ ((if _ : j = i then _ else if _ : indexOrder j < indexOrder i then _ else _)) = _
    by_cases hij : i = j
    · subst j
      simp only [dite_true]
      exact (mem_fixedCoefficients σ _).mp (v.1 i).property
    · have hji : j ≠ i := Ne.symm hij
      by_cases hlt : indexOrder i < indexOrder j
      · simp only [dif_neg hij, dif_neg hji, dif_pos hlt, dif_neg (not_lt_of_gt hlt)]
        exact hσ _
      · have hgt : indexOrder j < indexOrder i := lt_of_le_of_ne (le_of_not_gt hlt)
          (fun h => hij (indexOrder.injective h.symm))
        simp [hij, hji, hlt, hgt]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    dsimp
    split_ifs with hij hlt
    · subst j; rfl
    · rfl
    · exact entry_conjugate σ hσ X i j
  right_inv v := by
    apply Prod.ext
    · ext i
      simp
    · funext p
      have hne : p.val.1 ≠ p.val.2 := fun h => by simpa [h] using p.property
      simp [hne, p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_space [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    Module.finrank k (Space σ hσ) = 16 := by
  rw [(coordinates σ hσ).finrank_eq, Module.finrank_prod]
  simp [Module.finrank_pi_fintype, finrank_fixedCoefficients σ hdeg hne,
    card_upper, hdeg, Index]


lemma fieldFixed_entry (X : fieldFixed σ hσ) (i j : Index) :
    σ (X.val.val i j) = X.val.val i j := by
  have h := congrFun (congrFun ((mem_fieldFixed σ hσ X.val).mp X.property) i) j
  exact (entry_conjugate σ hσ X.val j i).trans h

def fixedCoordinates : fieldFixed σ hσ ≃ₗ[k]
    ((Index → fixedCoefficients σ) × (Upper → fixedCoefficients σ)) where
  toFun X := (fun i => ⟨X.val.val i i, (mem_fixedCoefficients σ _).mpr
      (fieldFixed_entry σ hσ X i i)⟩,
    fun p => ⟨X.val.val p.val.1 p.val.2, (mem_fixedCoefficients σ _).mpr
      (fieldFixed_entry σ hσ X p.val.1 p.val.2)⟩)
  invFun v := ⟨(coordinates σ hσ).symm (v.1, fun p => (v.2 p).val), by
    apply (mem_fieldFixed σ hσ _).mpr
    ext i j
    change (if _ : j = i then _ else if _ : indexOrder j < indexOrder i then _ else _) =
      (if _ : i = j then _ else if _ : indexOrder i < indexOrder j then _ else _)
    by_cases hij : i = j
    · subst j; simp
    · have hji : j ≠ i := Ne.symm hij
      by_cases hlt : indexOrder i < indexOrder j
      · simp only [dif_neg hij, dif_neg hji, dif_pos hlt,
          dif_neg (not_lt_of_gt hlt)]
        exact (mem_fixedCoefficients σ _).mp (v.2 _).property
      · have hgt : indexOrder j < indexOrder i := lt_of_le_of_ne (le_of_not_gt hlt)
          (fun h => hij (indexOrder.injective h.symm))
        simp only [dif_neg hij, dif_neg hji, dif_neg hlt, dif_pos hgt]
        exact ((mem_fixedCoefficients σ _).mp (v.2 _).property).symm⟩
  left_inv X := by
    apply Subtype.ext
    change (coordinates σ hσ).symm ((coordinates σ hσ) X.val) = X.val
    exact (coordinates σ hσ).symm_apply_apply X.val
  right_inv v := by
    apply Prod.ext
    · ext i; simp [coordinates]
    · ext p
      have hne : p.val.1 ≠ p.val.2 := fun h => by simpa [h] using p.property
      simp [coordinates, hne, p.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma finrank_fieldFixed [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    Module.finrank k (fieldFixed σ hσ) = 10 := by
  rw [(fixedCoordinates σ hσ).finrank_eq, Module.finrank_prod]
  simp [Module.finrank_pi_fintype, finrank_fixedCoefficients σ hdeg hne,
    card_upper, Index]

lemma finrank_fieldMoved [FiniteDimensional k F]
    (hdeg : Module.finrank k F = 2) (hne : σ ≠ AlgEquiv.refl) :
    Module.finrank k (fieldMoved σ hσ) = 6 := by
  have h := ((fieldSwap σ hσ).toLinearMap - LinearMap.id).finrank_range_add_finrank_ker
  change Module.finrank k (fieldMoved σ hσ) + Module.finrank k (fieldFixed σ hσ) =
    Module.finrank k (Space σ hσ) at h
  rw [finrank_space σ hσ hdeg hne, finrank_fieldFixed σ hσ hdeg hne] at h
  omega


end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Model.Geometry
