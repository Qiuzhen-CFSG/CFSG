module

public import Theory.SpecificGroups.G2.PRegularClasses.FieldExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Rational points and conjugator correction for the actual G₂ model

An octonion automorphism with entries in the base field descends by restricting
its coordinate matrix. Injectivity supplies an invertible linear map over the
base field, and the injective coefficient map reflects preservation of the
literal octonion multiplication.

Over the algebraic closure of a finite field F, the fixed scalars of the
|F|-power map are exactly F: use the split polynomial X^|F| - X. Consequently
the fixed group of coefficient Frobenius is the image of the actual model over F.
A Lang solution in the centralizer then corrects an algebraic conjugator to a
fixed conjugator, which descends through this identification. The centralizer
Lang equation remains an explicit hypothesis here.

Sources: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 10.1 and 12.5;
GLS III, Section 2.1 (`refs/KGroup/GLS3/chapter2.tex`). The octonion multiplication
and field-extension conventions are those of the licensed ATLAS port; see
`LICENSES/ATLAS.txt`.
-/

public section

namespace Atlas.G2.PRegularClasses.RationalFusion

open Atlas.SplitOctonion FieldExtension
open Polynomial

noncomputable section

variable {F K : Type*} [Field F] [Field K]

theorem coordinateMatrix_entry (g : Model F) (i j : Fin 8) :
    (coordinateMatrix g : Matrix (Fin 8) (Fin 8) F) i j =
      g.val (basisVector j) i := by
  have h := congrFun (coordinateMatrix_action g (basisVector j)) i
  simpa [Matrix.mulVec, dotProduct, basisVector, Pi.single_apply] using h

theorem fieldEmbedding_basis (f : F →+* K) (g : Model F) (j : Fin 8) :
    (fieldEmbedding f g).val (basisVector j) = coeffMap f (g.val (basisVector j)) := by
  rw [← coeffMap_basisVector f j, fieldEmbedding_action]

theorem fieldEmbedding_entry (f : F →+* K) (g : Model F) (i j : Fin 8) :
    (coordinateMatrix (fieldEmbedding f g) : Matrix (Fin 8) (Fin 8) K) i j =
      f ((coordinateMatrix g : Matrix (Fin 8) (Fin 8) F) i j) := by
  rw [coordinateMatrix_entry, coordinateMatrix_entry, fieldEmbedding_basis]
  rfl

private theorem coeffMap_injective (f : F →+* K) : Function.Injective (coeffMap f) := by
  intro x y h
  funext i
  exact f.injective (congrFun h i)

/-- An automorphism whose entries lie in the base field descends as an
octonion automorphism, including multiplication preservation. -/
theorem exists_preimage_of_entries (f : F →+* K) (g : Model K)
    (h : ∀ i j, (coordinateMatrix g : Matrix (Fin 8) (Fin 8) K) i j ∈ f.range) :
    ∃ d : Model F, fieldEmbedding f d = g := by
  classical
  choose A hA using h
  let d : Carrier F →ₗ[F] Carrier F := Matrix.toLin' A
  have hd (x : Carrier F) : coeffMap f (d x) = g.val (coeffMap f x) := by
    rw [← coordinateMatrix_action g]
    ext i
    change f (∑ j, A i j * x j) =
      ∑ j, (coordinateMatrix g : Matrix (Fin 8) (Fin 8) K) i j * f (x j)
    simp only [map_sum, map_mul, hA]
  have hi : Function.Injective d := by
    intro x y hxy
    apply coeffMap_injective f
    apply g.val.injective
    rw [← hd, ← hd, hxy]
  let e : Carrier F ≃ₗ[F] Carrier F :=
    LinearEquiv.ofBijective d ⟨hi, d.surjective_of_injective hi⟩
  have he (x y : Carrier F) : e (mul x y) = mul (e x) (e y) := by
    apply coeffMap_injective f
    change coeffMap f (d (mul x y)) = coeffMap f (mul (d x) (d y))
    rw [hd, coeffMap_mul, coeffMap_mul, automorphism_mul, hd, hd]
  refine ⟨⟨e, he⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f ⟨e, he⟩).val (basisVector j) = g.val (basisVector j)
  rw [fieldEmbedding_basis]
  change coeffMap f (d (basisVector j)) = _
  rw [hd, coeffMap_basisVector]

variable (F) [Finite F]

/-- The coefficientwise `|F|`-power endomorphism on actual octonion
automorphisms over the algebraic closure. -/
@[expose] def frobenius : Model (AlgebraicClosure F) →* Model (AlgebraicClosure F) :=
  let := Fintype.ofFinite F
  fieldEmbedding (FiniteField.frobeniusAlgHom F (AlgebraicClosure F)).toRingHom

theorem frobenius_entry (g : Model (AlgebraicClosure F)) (i j : Fin 8) :
    (coordinateMatrix (frobenius F g) : Matrix (Fin 8) (Fin 8) (AlgebraicClosure F)) i j =
      ((coordinateMatrix g : Matrix (Fin 8) (Fin 8) (AlgebraicClosure F)) i j) ^ Nat.card F := by
  let := Fintype.ofFinite F
  rw [frobenius, fieldEmbedding_entry]
  simp [Nat.card_eq_fintype_card]

theorem frobenius_embedding (g : Model F) :
    frobenius F (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g) =
      fieldEmbedding (algebraMap F (AlgebraicClosure F)) g := by
  let := Fintype.ofFinite F
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (AlgebraicClosure F) (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (frobenius F (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g)).val
    (basisVector j) = (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g).val (basisVector j)
  ext i
  rw [← coordinateMatrix_entry, ← coordinateMatrix_entry, frobenius_entry, fieldEmbedding_entry]
  rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

private theorem scalar_descent (x : AlgebraicClosure F) (hx : x ^ Nat.card F = x) :
    x ∈ (algebraMap F (AlgebraicClosure F)).range := by
  let := Fintype.ofFinite F
  let p : F[X] := X ^ Fintype.card F - X
  have hs : p.Splits := by
    apply Polynomial.splits_iff_card_roots.mpr
    rw [FiniteField.roots_X_pow_card_sub_X, ← Finset.card_def, Finset.card_univ]
    exact (FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card).symm
  apply hs.mem_range_of_isRoot
    (FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card)
  simpa [p, Polynomial.IsRoot, Nat.card_eq_fintype_card] using sub_eq_zero.mpr hx

/-- The fixed group of coefficient Frobenius is exactly the actual finite-field
octonion automorphism group. -/
theorem frobenius_fixed_iff (g : Model (AlgebraicClosure F)) :
    frobenius F g = g ↔
      ∃ d : Model F, fieldEmbedding (algebraMap F (AlgebraicClosure F)) d = g := by
  constructor
  · intro hg
    apply exists_preimage_of_entries
    intro i j
    apply scalar_descent
    rw [← frobenius_entry, hg]
  · rintro ⟨d, rfl⟩
    exact frobenius_embedding F d

private theorem exists_fixed_conjugator {G : Type*} [Group G] (σ : G →* G)
    (x y : G) (hx : σ x = x) (hy : σ y = y) (hc : IsConj x y)
    (hLang : ∀ z : G, Commute z x → ∃ u : G, Commute u x ∧ u * (σ u)⁻¹ = z) :
    ∃ c : G, σ c = c ∧ c * x * c⁻¹ = y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hσc : σ c * x * (σ c)⁻¹ = y := by
    simpa only [map_mul, map_inv, hx, hy] using congrArg σ hc
  have ht : Commute (c⁻¹ * σ c) x := by
    change c⁻¹ * σ c * x = x * (c⁻¹ * σ c)
    calc
      _ = c⁻¹ * (σ c * x * (σ c)⁻¹) * σ c := by group
      _ = c⁻¹ * (c * x * c⁻¹) * σ c := by rw [hσc, hc]
      _ = _ := by group
  obtain ⟨u, hu, hL⟩ := hLang (c⁻¹ * σ c) ht
  refine ⟨c * u, ?_, ?_⟩
  · rw [map_mul]
    calc
      _ = c * (c⁻¹ * σ c) * σ u := by group
      _ = c * (u * (σ u)⁻¹) * σ u := by rw [← hL]
      _ = _ := by group
  · calc
      _ = c * (u * x) * u⁻¹ * c⁻¹ := by group
      _ = c * (x * u) * u⁻¹ * c⁻¹ := by rw [hu.eq]
      _ = c * x * c⁻¹ := by group
      _ = y := hc

/-- Algebraic conjugacy descends once the centralizer Lang equation is solved. -/
theorem isConj_of_extension_of_centralizer_lang (g h : Model F)
    (hc : IsConj (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g)
      (fieldEmbedding (algebraMap F (AlgebraicClosure F)) h))
    (hLang : ∀ z : Model (AlgebraicClosure F),
      Commute z (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g) →
      ∃ u : Model (AlgebraicClosure F),
        Commute u (fieldEmbedding (algebraMap F (AlgebraicClosure F)) g) ∧
        u * (frobenius F u)⁻¹ = z) : IsConj g h := by
  obtain ⟨c, hfix, hconj⟩ := exists_fixed_conjugator (frobenius F) _ _
    (frobenius_embedding F g) (frobenius_embedding F h) hc hLang
  obtain ⟨d, rfl⟩ := (frobenius_fixed_iff F c).mp hfix
  apply isConj_iff.mpr
  refine ⟨d, fieldEmbedding_injective (algebraMap F (AlgebraicClosure F)) ?_⟩
  simpa only [map_mul, map_inv] using hconj

end
end Atlas.G2.PRegularClasses.RationalFusion
