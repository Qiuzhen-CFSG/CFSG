module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Reduction

/-!
# Conditional assembly of the actual paired normalizer

Two representation-theoretic inputs suffice: the derived pair has precisely the
independent coefficient scalars as its binary commutant, and the binary
normalizer of the derived natural image is scalar times inner-field. Restrict a
preserving paired operator to the first summand and remove its standard form.
The remaining operator fixes that coordinate pointwise, so faithfulness of the
natural action makes it centralize the pair; the commutant determines its other
coordinate. The projection argument handles exchanging operators.

The resulting conditional equality includes both containments. These explicit
inputs remain proof obligations; this module does not assert that they hold.
Both forward and inverse graph-swap formulas retain its Frobenius square.

Source: Aschbacher–Smith H.7, printed pp.388–389, and the paired setup on
printed p.696 of `refs/quasithin.pdf`.
-/

@[expose] public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair.Ambient.Normalizer
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

/-- The explicit summand-preserving operator in the proposed normalizer. -/
noncomputable def standardPair (a b : Fˣ) (g : Sp F) (σ : F ≃+* F) :
    Space F ≃ₗ[ZMod 2] Space F :=
  scalarPair a b * linearAction graphPair g * fieldPair σ

@[simp] lemma standardPair_apply (a b : Fˣ) (g : Sp F) (σ : F ≃+* F) (v : Space F) :
    standardPair a b g σ v =
      (a.val • innerFieldVector g σ v.1, b.val • innerFieldVector (graphAut g) σ v.2) := rfl

lemma standardPair_mem_standardAmbient (a b : Fˣ) (g : Sp F) (σ : F ≃+* F) :
    standardPair a b g σ ∈ standardAmbient := by
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨(a,b), rfl⟩)))
    · exact fullImage_le_standardAmbient ⟨g, rfl⟩
  · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨σ, rfl⟩))

lemma standardPair_preserves (a b : Fˣ) (g : Sp F) (σ : F ≃+* F) :
    PreservesCoordinates (standardPair a b g σ) := by
  constructor <;> intro v <;> simp

lemma normalizer_commutes_of_fst_eq (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) (hfst : ∀ v, (f v).1 = v.1) :
    ∀ (x : commutator (Sp F)) v, f (derivedPair graphAut x v) = derivedPair graphAut x (f v) := by
  intro x
  obtain ⟨y, hy⟩ := normalizer_intertwines graphAut f hf x
  have he (w : Vector F) : symplecticNatural 2 x.val w = symplecticNatural 2 y.val w := by
    have h := congrArg Prod.fst (hy (w, 0))
    rw [hfst] at h
    change symplecticNatural 2 x.val w = symplecticNatural 2 y.val (f (w, 0)).1 at h
    rw [hfst] at h
    exact h
  have hxy : x = y := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have h := congrArg (fun w : Vector F => w i) (he (Pi.single j 1))
    simpa [symplecticNatural_apply, Matrix.mulVec_single] using h
  rwa [← hxy] at hy

variable (hcomm : ∀ q : Space F →ₗ[ZMod 2] Space F,
  (∀ (x : commutator (Sp F)) v, q (derivedPair graphAut x v) = derivedPair graphAut x (q v)) →
  ∃ a b : F, q = blockScalar a b)

include hcomm in
lemma normalizer_scalar_of_fst_eq (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) (hfst : ∀ v, (f v).1 = v.1) :
    ∃ b : Fˣ, f = scalarPair 1 b := by
  obtain ⟨a, b, h⟩ := hcomm f.toLinearMap (normalizer_commutes_of_fst_eq f hf hfst)
  have ha : a = 1 := by
    have he := congrArg (fun v : Space F => v.1 (Sum.inl 0))
      (LinearMap.congr_fun h ((Pi.single (Sum.inl 0) 1 : Vector F), 0))
    change (f _).1 (Sum.inl 0) = _ at he
    rw [hfst] at he
    simpa using he.symm
  have hb : b ≠ 0 := by
    intro hb
    have hz : f (0, (Pi.single (Sum.inl 0) 1 : Vector F)) = 0 := by
      calc
        f _ = blockScalar a b _ := LinearMap.congr_fun h _
        _ = 0 := by simp [hb]
    have he := f.map_eq_zero_iff.mp hz
    have := congrArg (fun v : Space F => v.2 (Sum.inl 0)) he
    simp at this
  refine ⟨Units.mk0 b hb, ?_⟩
  apply LinearEquiv.ext
  intro v
  have he := LinearMap.congr_fun h v
  change f v = blockScalar a b v at he
  rw [ha] at he
  exact he

variable (hnatural : ∀ e : Vector F ≃ₗ[ZMod 2] Vector F, e ∈ naturalNormalizer →
  ∃ (a : Fˣ) (g : Sp F) (σ : F ≃+* F), ∀ v, e v = a.val • innerFieldVector g σ v)

include hcomm hnatural in
lemma preserving_eq_standardPair (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) (hp : PreservesCoordinates f) :
    ∃ (a b : Fˣ) (g : Sp F) (σ : F ≃+* F), f = standardPair a b g σ := by
  obtain ⟨a, g, σ, he⟩ := hnatural (firstBlockEquiv f hp)
    (firstBlock_mem_naturalNormalizer graphAut f hf hp)
  let s := standardPair a 1 g σ
  have hs : s ∈ pairedNormalizer graphAut :=
    standardAmbient_le_pairedNormalizer (standardPair_mem_standardAmbient a 1 g σ)
  have hfs (v : Space F) : (f v).1 = (s v).1 := by
    rw [← firstBlock_fst f hp]
    exact he v.1
  have hfst (v : Space F) : ((f * s⁻¹) v).1 = v.1 := by
    change (f (s.symm v)).1 = v.1
    rw [hfs, s.apply_symm_apply]
  obtain ⟨b, hb⟩ := normalizer_scalar_of_fst_eq hcomm (f * s⁻¹)
    ((pairedNormalizer graphAut).mul_mem hf ((pairedNormalizer graphAut).inv_mem hs)) hfst
  refine ⟨a, b, g, σ, ?_⟩
  have hmul : f = scalarPair 1 b * s := (mul_inv_eq_iff_eq_mul).mp hb
  rw [hmul]
  apply LinearEquiv.ext
  intro v
  change ((1 : F) • (s v).1, b.val • (s v).2) = _
  simp [s]

include hcomm hnatural in
lemma normalizer_forms (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) :
    ∃ (a b : Fˣ) (g : Sp F) (σ : F ≃+* F),
      f = standardPair a b g σ ∨ f = standardPair a b g σ * graphSwap⁻¹ := by
  rcases normalizer_summand_dichotomy hcomm f hf with hp | hp
  · obtain ⟨a,b,g,σ,h⟩ := preserving_eq_standardPair hcomm hnatural f hf hp
    exact ⟨a,b,g,σ,Or.inl h⟩
  · obtain ⟨a,b,g,σ,h⟩ := preserving_eq_standardPair hcomm hnatural (f * graphSwap)
      ((pairedNormalizer graphAut).mul_mem hf graphSwap_mem_pairedNormalizer) hp
    exact ⟨a,b,g,σ,Or.inr (eq_mul_inv_iff_mul_eq.mpr h)⟩

lemma graphSwap_symm_apply (v : Space F) :
    (graphSwap (F := F)).symm v =
      ((fieldVector (frobeniusEquiv F 2)).symm v.2, v.1) := by
  apply (graphSwap (F := F)).injective
  rw [LinearEquiv.apply_symm_apply, graphSwap_apply, LinearEquiv.apply_symm_apply]

lemma graphSwap_inv_eq_fieldPair_mul :
    (graphSwap (F := F))⁻¹ = fieldPair (frobeniusEquiv F 2).symm * graphSwap := by
  apply LinearEquiv.ext
  intro v
  change graphSwap.symm v = fieldPair (frobeniusEquiv F 2).symm (graphSwap v)
  rw [graphSwap_symm_apply, graphSwap_apply]
  apply Prod.ext
  · rfl
  · ext i
    exact ((frobeniusEquiv F 2).symm_apply_apply (v.1 i)).symm

lemma standardPair_mul_fieldPair (a b : Fˣ) (g : Sp F) (σ δ : F ≃+* F) :
    standardPair a b g σ * fieldPair δ = standardPair a b g (σ * δ) := by
  apply LinearEquiv.ext
  intro v
  rfl

include hcomm hnatural in
lemma normalizer_forms_forward (f : Space F ≃ₗ[ZMod 2] Space F)
    (hf : f ∈ pairedNormalizer graphAut) :
    ∃ (a b : Fˣ) (g : Sp F) (σ : F ≃+* F),
      f = standardPair a b g σ ∨ f = standardPair a b g σ * graphSwap := by
  obtain ⟨a,b,g,σ,h | h⟩ := normalizer_forms hcomm hnatural f hf
  · exact ⟨a,b,g,σ,Or.inl h⟩
  · refine ⟨a,b,g,σ * (frobeniusEquiv F 2).symm,Or.inr ?_⟩
    rw [h, graphSwap_inv_eq_fieldPair_mul, ← mul_assoc, standardPair_mul_fieldPair]

include hcomm hnatural in
/-- The normalizer equality, conditional on the two stated representation inputs. -/
theorem pairedNormalizer_eq_standardAmbient_of_inputs :
    pairedNormalizer (graphAut (F := F)) = standardAmbient := by
  apply le_antisymm _ standardAmbient_le_pairedNormalizer
  intro f hf
  obtain ⟨a,b,g,σ,h | h⟩ := normalizer_forms hcomm hnatural f hf
  · rw [h]
    exact standardPair_mem_standardAmbient a b g σ
  · rw [h]
    apply (standardAmbient (F := F)).mul_mem (standardPair_mem_standardAmbient a b g σ)
    apply Subgroup.inv_mem
    exact Subgroup.subset_closure (Or.inr (Set.mem_singleton _))

end SymplecticConjugatePair.Ambient.Normalizer
