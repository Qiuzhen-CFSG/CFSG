module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.HighestVector
public import Theory.Representation.InvariantsBaseChange
public import Mathlib.RingTheory.Flat.Basic

/-!
# Reducing G₂ tensor fixed lines to a Steinberg norm

A normalized unipotent embedding of each restricted factor in the level-two
Steinberg factor tensors through the actual Frobenius twists. For the full
Steinberg word, the carrier dimension is the order of the positive unipotent
group. A nonzero norm of the opposite highest vector then makes its orbit a
regular basis, by the modular p-group fixed-vector theorem. Its fixed space is
one-dimensional. Injectivity transfers this result to every word, and flat
scalar extension transfers the fixed line to every coefficient field.

The factor embeddings and the nonzero norm are separate concrete obligations;
this module proves the reduction without assuming tensor simplicity or cyclicity.
Source: GLS3, 2.8.6(a), 2.8.7, 2.8.9 and 2.8.10(g).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace Atlas.G2.TensorClassification.FixedLine
open Restricted Explicit

variable (F : Type*) [Field F] [CharP F 2]

/-- Tensor normalized maps into the actual Steinberg carrier, preserving the
published parenthesization and the terminal tensor unit. -/
def wordToSteinberg
    (j : (a : Factor) → Space F a →ₗ[F] Space F .steinberg) :
    (w : List Factor) → WordSpace F w →ₗ[F]
      WordSpace F (List.replicate w.length .steinberg)
  | [] => LinearMap.id
  | a :: w => TensorProduct.map (j a) (wordToSteinberg j w)

theorem wordToSteinberg_injective
    (j : (a : Factor) → Space F a →ₗ[F] Space F .steinberg)
    (hj : ∀ a, Function.Injective (j a)) (w : List Factor) :
    Function.Injective (wordToSteinberg F j w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons a w ih => exact TensorProduct.map_injective_of_flat_flat _ _ (hj a) ih

theorem wordToSteinberg_highestVector
    (j : (a : Factor) → Space F a →ₗ[F] Space F .steinberg)
    (hj : ∀ a, j a (highestVector F a) = highestVector F .steinberg)
    (w : List Factor) :
    wordToSteinberg F j w (wordHighestVector F w) =
      wordHighestVector F (List.replicate w.length .steinberg) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change TensorProduct.map (j a) (wordToSteinberg F j w)
      (highestVector F a ⊗ₜ[F] wordHighestVector F w) = _
    rw [TensorProduct.map_tmul, hj, ih]
    rfl

omit [CharP F 2] in
private theorem field_unipotent (σ : F ≃+* F) (g : Model F)
    (hg : g ∈ unipotent) : fieldEquiv σ g ∈ unipotent := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  have he : fieldEquiv σ (unipotentProduct t) = unipotentProduct (σ ∘ t) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    funext i
    fin_cases i <;> simp [fieldEquiv, Atlas.SplitOctonion.transportAutomorphism,
      Atlas.SplitOctonion.transportLinear, Atlas.SplitOctonion.mapCoefficients,
      unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
      rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
      rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
      rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply]
  rw [he]
  exact unipotentProduct_mem _

variable [Finite F]

theorem wordToSteinberg_intertwines
    (j : (a : Factor) → Space F a →ₗ[F] Space F .steinberg)
    (hj : ∀ a g, g ∈ (unipotent : Subgroup (Model F)) → ∀ v,
      j a (action F a g v) = action F .steinberg g (j a v))
    (r : ℕ) (w : List Factor) (g : Model F) (hg : g ∈ unipotent)
    (v : WordSpace F w) :
    wordToSteinberg F j w (wordRep F r w g v) =
      wordRep F r (List.replicate w.length .steinberg) g (wordToSteinberg F j w v) := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih =>
    suffices he : (wordToSteinberg F j (a :: w)).comp (wordRep F r (a :: w) g) =
        (wordRep F r (List.replicate (a :: w).length .steinberg) g).comp
          (wordToSteinberg F j (a :: w)) by
      exact LinearMap.congr_fun he v
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.map (j a) (wordToSteinberg F j w)
      (factorRep F r a g x ⊗ₜ[F] wordRep F (r + 1) w g y) = _
    simp only [TensorProduct.map_tmul]
    change j a (factorRep F r a g x) ⊗ₜ[F]
      wordToSteinberg F j w (wordRep F (r + 1) w g y) =
      factorRep F r .steinberg g (j a x) ⊗ₜ[F]
        wordRep F (r + 1) (List.replicate w.length .steinberg) g
          (wordToSteinberg F j w y)
    rw [ih]
    congr 1
    exact hj a _ (field_unipotent F _ g hg) x

/-- The literal positive-unipotent norm of the opposite highest vector in the
full Steinberg word. It uses every field-valued parameter in all six roots. -/
def steinbergNorm [Fintype F] (n : ℕ) : WordSpace F (List.replicate n .steinberg) :=
  ∑ t : Fin 6 → F, wordRep F 0 (List.replicate n .steinberg)
    (unipotentProduct t * Steinberg.longestWeyl F)
    (wordHighestVector F (List.replicate n .steinberg))

/-- The full Steinberg word has exactly the dimension of the unipotent group. -/
theorem finrank_steinbergWord {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Module.finrank F (WordSpace F (List.replicate n .steinberg)) =
      Nat.card (unipotent (K := F)) := by
  rw [finrank_wordSpace, card_unipotent, hF]
  simp only [wordDegree, List.map_replicate, List.prod_replicate, Factor.dimension]
  calc (64 : ℕ) ^ n = (2 ^ 6) ^ n := rfl
       _ = (2 ^ n) ^ 6 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Nonzero unipotent norm gives the highest line in the full Steinberg tensor.
The orbit basis is proved here, rather than assumed as a cyclicity premise. -/
theorem steinbergWord_fixed_of_norm [Fintype F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hnorm : steinbergNorm F n ≠ 0)
    (v : WordSpace F (List.replicate n .steinberg))
    (hv : ∀ g ∈ (unipotent : Subgroup (Model F)),
      wordRep F 0 (List.replicate n .steinberg) g v = v) :
    ∃ c : F, v = c • wordHighestVector F (List.replicate n .steinberg) := by
  classical
  let U := unipotent (K := F)
  let : Fintype U := Fintype.ofEquiv (Fin 6 → F) unipotentEquiv
  let ρ := (wordRep F 0 (List.replicate n .steinberg)).comp U.subtype
  let z := wordRep F 0 (List.replicate n .steinberg) (Steinberg.longestWeyl F)
    (wordHighestVector F (List.replicate n .steinberg))
  have hsum : (∑ g : U, ρ g z) = steinbergNorm F n := by
    symm
    apply Fintype.sum_equiv (unipotentEquiv (K := F))
    intro t
    exact LinearMap.congr_fun (map_mul _ _ _) _
  have hp : IsPGroup (ringChar F) U := by
    rw [ringChar.eq F 2]
    apply IsPGroup.of_card (n := n * 6)
    rw [card_unipotent, hF, pow_mul]
  have hc : ringChar F ≠ 0 := by rw [ringChar.eq F 2]; decide
  have hn : (∑ g : U, ρ g z) ≠ 0 := by rwa [hsum]
  have hi := Steinberg.BinaryOrbit.Regular.independent_orbit hc hp ρ z hn
  have hspan : Submodule.span F (Set.range fun g : U => ρ g z) = ⊤ := by
    apply hi.span_eq_top_of_card_eq_finrank'
    rw [finrank_steinbergWord F hF, Nat.card_eq_fintype_card]
  have hfixed (x : WordSpace F (List.replicate n .steinberg))
      (hx : ∀ g : U, ρ g x = x) : ∃ c : F, x = c • ∑ g : U, ρ g z :=
    Steinberg.BinaryOrbit.Regular.fixed_span_orbit hc hp ρ z hn x
      (by rw [hspan]; trivial) hx
  obtain ⟨a, ha⟩ := hfixed v (fun g => hv g.val g.property)
  obtain ⟨b, hb⟩ := hfixed (wordHighestVector F (List.replicate n .steinberg))
    (fun g => wordHighestVector_fixed_unipotent F 0 _ g.val g.property)
  have hb0 : b ≠ 0 := by
    intro h
    exact wordHighestVector_ne_zero F _ (by simpa only [h, zero_smul] using hb)
  refine ⟨a / b, ?_⟩
  rw [hb, smul_smul, div_mul_cancel₀ _ hb0]
  exact ha

/-- Tensoring normalized unipotent embeddings reduces every word to the full
Steinberg word of the same length. -/
theorem word_fixed_of_steinberg_data [Fintype F]
    (j : (a : Factor) → Space F a →ₗ[F] Space F .steinberg)
    (hinj : ∀ a, Function.Injective (j a))
    (hseed : ∀ a, j a (highestVector F a) = highestVector F .steinberg)
    (hact : ∀ a g, g ∈ (unipotent : Subgroup (Model F)) → ∀ v,
      j a (action F a g v) = action F .steinberg g (j a v))
    (w : List Factor) (hF : Nat.card F = 2 ^ w.length)
    (hnorm : steinbergNorm F w.length ≠ 0)
    (v : WordSpace F w)
    (hv : ∀ g ∈ (unipotent : Subgroup (Model F)), wordRep F 0 w g v = v) :
    ∃ c : F, v = c • wordHighestVector F w := by
  obtain ⟨c, hc⟩ := steinbergWord_fixed_of_norm F hF hnorm (wordToSteinberg F j w v) (by
    intro g hg
    rw [← wordToSteinberg_intertwines F j hact 0 w g hg, hv g hg])
  refine ⟨c, wordToSteinberg_injective F j hinj w ?_⟩
  rwa [map_smul, wordToSteinberg_highestVector F j hseed]

/-- Flat base change transports the actual unipotent highest line. This works
in defining characteristic, without averaging or algebraic closure. -/
theorem tensor_fixed_of_word_fixed (K : Type*) [Field K] [Algebra F K]
    {n : ℕ} (w : Fin n → Factor)
    (hfixed : ∀ v : WordSpace F (List.ofFn w),
      (∀ g ∈ (unipotent : Subgroup (Model F)), wordRep F 0 (List.ofFn w) g v = v) →
      ∃ c : F, v = c • wordHighestVector F (List.ofFn w))
    (v : TensorSpace F K w)
    (hv : ∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) :
    ∃ c : K, v = c • tensorHighestVector F K w := by
  let ρ : Representation F (unipotent (K := F)) (WordSpace F (List.ofFn w)) :=
    (wordRep F 0 (List.ofFn w)).comp (unipotent (K := F)).subtype
  have he : ρ.invariants = Submodule.span F {wordHighestVector F (List.ofFn w)} := by
    ext x
    constructor
    · intro hx
      obtain ⟨c, hc⟩ := hfixed x (fun g hg => hx ⟨g, hg⟩)
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
    · intro hx g
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      exact (map_smul _ _ _).trans
        (congrArg (fun z => c • z) (wordHighestVector_fixed_unipotent F 0 _ g.val g.property))
  let : Finite (unipotent (K := F)) := Finite.of_equiv (Fin 6 → F) unipotentEquiv
  have hv' : v ∈ (Representation.extendScalars K ρ).invariants :=
    fun g => hv g.val g.property
  rw [Representation.invariants_extendScalars_eq_baseChange_of_finite, he,
    Submodule.baseChange_span, Set.image_singleton] at hv'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv'
  exact ⟨c, hc.symm⟩

end Atlas.G2.TensorClassification.FixedLine
end
