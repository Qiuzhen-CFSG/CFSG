module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.Inputs
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.Representation.BinaryOffender.InnerInvolutions
public import Theory.Representation.BinaryOffender.CentralKernelImage


/-!
# Graph and half-turn forms for actual outer SL₃ involution lifts

Binary standard-automorphism coverage, including degrees one and two, gives a
literal GL₃–field–graph factorization on the central cover. We use inverse
transpose directly, rather than the opposition representative. Squaring cancels
the graph part; coefficient rigidity then forces the field part to have square
one. A nonidentity field involution is the half-degree Frobenius.

If both field and graph parts vanish, the diagonal class has exponent dividing
three, so an involutory linear actor is inner. Perfectness lifts that assertion
from PSL₃ to SL₃. On the actual irreducible binary image, the centralizer has no
involutions, so the original normalizer operator is then in the component image,
contradicting its outerness. This retains both the central cover and the scalar
centralizer kernel, with no faithful-action assumption.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
steps 2–5, manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
The underlying standard-automorphism description is GLS3, Theorem 2.5.12
and §2.7, as implemented in the imported PSL₃ modules.
-/

public section
open scoped MatrixGroups
open Matrix Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable {F : Type*} [Field F]

private theorem center_field (τ : F ≃+* F) :
    centerAction F (Atlas.fieldEquivSL 3 τ) = fieldAction F τ := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) y
  simp only [QuotientGroup.mk'_apply, centerAction_mk, fieldAction_mk]
  rfl

private theorem factorization (B : BinaryField) (α : MulAut SL(3,B.Carrier)) :
    ∃ (m : GL (Fin 3) B.Carrier) (τ : B.Carrier ≃+* B.Carrier) (ε : Bool),
      α = linearConjSL B.Carrier m * Atlas.fieldEquivSL 3 τ *
        (if ε then graphSL B.Carrier else 1) := by
  have hc := standard_eq_top_of_two_power_card B.Carrier B.degree_pos B.card_eq
  obtain ⟨m, τ, h | h⟩ := NormalizerForm.standard_factorization B.Carrier
    field_linearConj graph_linearConj_exists field_commute_graph
    (centerAction B.Carrier α) (by rw [hc]; trivial)
  · refine ⟨m, τ, false, ActorCoverage.centerAction_injective B.Carrier ?_⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, mul_one, map_mul, center_field,
      linearConj, MonoidHom.comp_apply] using h
  · refine ⟨m, τ, true, ActorCoverage.centerAction_injective B.Carrier ?_⟩
    simpa only [↓reduceIte, map_mul, center_field, linearConj, MonoidHom.comp_apply, graph] using h

private theorem graph_field_square (m : GL (Fin 3) F) (τ : F ≃+* F) :
    (linearConj F m * fieldAction F τ * graph F) ^ 2 =
      linearConj F (m * GeneralLinearGroup.map τ.toRingHom (inverseTransposeGL F m)) *
        fieldAction F (τ ^ 2) := by
  have hg : graph F * graph F = 1 := by simpa only [pow_two] using graph_sq F
  calc
    _ = linearConj F m * fieldAction F τ * (graph F * linearConj F m) *
        fieldAction F τ * graph F := by rw [pow_two]; group
    _ = linearConj F m * (fieldAction F τ * linearConj F (inverseTransposeGL F m)) *
        (graph F * fieldAction F τ) * graph F := by rw [graph_linearConj]; group
    _ = _ := by
      rw [field_linearConj, ← (field_commute_graph τ).eq]
      simp only [map_mul, pow_two, mul_assoc, hg, mul_one]

private theorem coefficient_square [CharP F 2] (m : GL (Fin 3) F) (τ : F ≃+* F)
    (ε : Bool) (h : (linearConj F m * fieldAction F τ *
      (if ε then graph F else 1)) ^ 2 = 1) : τ ^ 2 = 1 := by
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
    exact ResidualLinear.coefficient_pow_eq_one m τ h
  · simp only [↓reduceIte] at h
    rw [graph_field_square] at h
    simpa only [pow_one] using ResidualLinear.coefficient_pow_eq_one
      (m * GeneralLinearGroup.map τ.toRingHom (inverseTransposeGL F m)) (τ ^ 2)
      (j := 1) (by simpa only [pow_one] using h)


private theorem linear_involution_inner (m : GL (Fin 3) F)
    (hm : linearConjSL F m ^ 2 = 1) :
    ∃ x : SL(3,F), linearConjSL F m = MulAut.conj x := by
  have hproj : linearConj F m ^ 2 = 1 := by
    change centerAction F (linearConjSL F m) ^ 2 = 1
    rw [← map_pow, hm, map_one]
  obtain ⟨y, hy⟩ := Matrix.PSL3.OddInvolutionFixed.linearConj_involution_inner m hproj
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) y
  refine ⟨x, ActorCoverage.centerAction_injective F ?_⟩
  change linearConj F m = centerAction F (MulAut.conj x)
  rw [← hy]
  ext y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) y
  rfl

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

private theorem operator_mem_image_of_inner (t : linearNormalizer σ) (L : LiftedInvolution B σ t)
    (hi : ∃ x, L.automorphism = MulAut.conj x) : t.val ∈ actionImage σ := by
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp (actionImage σ).subtype) :=
    imageRepresentation_isIrreducible σ inferInstance
  apply involution_mem_of_inner (Units.coeHom (Module.End (ZMod 2) V)) (actionImage σ)
    (fun _ _ h => Units.ext h) t (congrArg Subtype.val L.actor_square)
  obtain ⟨x, hx⟩ := hi
  refine ⟨actionHom σ x, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨g, rfl⟩ := σ.asGroupHom.rangeRestrict_surjective y
  apply Subtype.ext
  have h : t.val * σ.asGroupHom g = σ.asGroupHom (L.automorphism g) * t.val :=
    Units.ext (L.intertwines g)
  change t.val * σ.asGroupHom g * t.val⁻¹ =
    σ.asGroupHom x * σ.asGroupHom g * (σ.asGroupHom x)⁻¹
  rw [h, mul_inv_cancel_right, hx, MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- Every supplied outer involution lift has the literal graph or half-degree
field–graph form. Once the lift is supplied, the reduction uses irreducibility
on the actual image; neither faithfulness of σ nor defining-field linearity
of the normalizer operator is assumed. -/
theorem outer_involution_forms (_hk : σ.ker ≤ Subgroup.center SL(3,B.Carrier)) :
    OuterInvolutionForms B σ := by
  intro t hout _ht L
  obtain ⟨m, τ, ε, he⟩ := factorization B L.automorphism
  have hs : (linearConj B.Carrier m * fieldAction B.Carrier τ *
      (if ε then graph B.Carrier else 1)) ^ 2 = 1 := by
    have h := congrArg (centerAction B.Carrier) L.square
    rw [he, map_pow, map_mul, map_mul, center_field] at h
    cases ε <;> simpa only [↓reduceIte, Bool.false_eq_true, map_one,
      linearConj, MonoidHom.comp_apply, graph] using h
  have hτ := coefficient_square m τ ε hs
  by_cases hτ1 : τ = 1
  · have hf : Atlas.fieldEquivSL 3 τ = 1 := by
      rw [hτ1]
      rfl
    cases ε
    · have he' : L.automorphism = linearConjSL B.Carrier m := by
        simpa only [hf, Bool.false_eq_true, ↓reduceIte, mul_one] using he
      exact (hout (operator_mem_image_of_inner B σ t L (by
        rw [he']
        exact linear_involution_inner m (he' ▸ L.square)))).elim
    · exact Or.inl ⟨m, by simpa only [hf, ↓reduceIte, mul_one] using he⟩
  · obtain ⟨d, hd, hdeg, hfield⟩ :=
      FiniteField.BinaryTorusTwoPower.involution_eq_half_frobenius B.card_eq τ hτ hτ1
    have hτd : τ = iterateFrobeniusEquiv B.Carrier 2 d := by
      ext x
      exact (hfield x).trans (iterateFrobeniusEquiv_def B.Carrier 2 d x).symm
    refine Or.inr ⟨⟨d, hd, hdeg, m, ε, ?_⟩⟩
    simpa only [Words.fieldGraph, ← mul_assoc, ← hτd] using he


end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
