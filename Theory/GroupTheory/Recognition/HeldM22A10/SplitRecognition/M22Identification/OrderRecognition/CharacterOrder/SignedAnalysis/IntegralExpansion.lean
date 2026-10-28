module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.Character.OrthonormalColumnGram
public import Theory.Character.ScalarProductMultiplicity

/-!
# Integral coordinates for Janko's actual exceptional inductions

The complete ordinary irreducible-character basis expands each of the five
actual induced functions. The reciprocity coefficients supplied by
`SpecialInductionData.columns` are integers, and orthogonality transports the
exact Gram matrix to their integer dot products. This constructs the expansion
interface used in the norm and signed-support arguments; it assumes no ambient
order and no multiplicity bound.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), p.12, the reciprocity calculation preceding Lemma 11.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Simultaneous integral expansions in a complete family of actual irreducibles. -/
public structure IntegralExpansion {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) where
  Index : Type
  finite : Fintype Index
  character : Index → ClassFunction G
  irreducible : ∀ j, IsIrreducibleCharacter (character j)
  injective : Function.Injective character
  complete : ∀ χ, IsIrreducibleCharacter χ → ∃ j, character j = χ
  coefficient : Fin 5 → Index → ℤ
  multiplicity : ∀ i j, scalarProduct G (I.induced i) (character j) = (coefficient i j : ℂ)
  expansion : ∀ i, I.induced i = ∑ j, (coefficient i j : ℂ) • character j
  gram : ∀ i l, ∑ j, coefficient i j * coefficient l j = exceptionalGram i l
  columns : ∀ j r, character j (CaseII.into D k (specialRepresentative r)) =
    (columnValue (fun i => coefficient i j) r : ℂ)

attribute [instance] IntegralExpansion.finite

public theorem exists_integralExpansion {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) : Nonempty (IntegralExpansion I) := by
  classical
  obtain ⟨J, hJ, χ, hχ, _⟩ := irreducible_characters_form_basis (G := G)
  let : Fintype J := hJ
  let f : J → ClassFunction G := fun j => ofConjClassFunction (χ j)
  have hf (j) : IsIrreducibleCharacter (f j) := by
    obtain ⟨n, ρ, hρ⟩ := (hχ.1 j).1
    refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
    · simpa [hρ] using (hχ.1 j).2
    · simp [f, hρ, ofConjClassFunction_characterClassFunction]
  have hinj : Function.Injective f := by
    intro i j hij
    apply hχ.2.2
    ext c
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
    exact congrFun hij g
  have hcomplete : ∀ θ, IsIrreducibleCharacter θ → ∃ j, f j = θ := by
    rintro θ ⟨n, ρ, hρ, rfl⟩
    obtain ⟨j, hj⟩ := hχ.2.1 (characterClassFunction ρ)
      ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
    exact ⟨j, by simp [f, hj, ofConjClassFunction_characterClassFunction]⟩
  choose c hc hv using fun j => I.columns (f j) (hf j)
  have hc' (j i) : scalarProduct G (I.induced i) (ofConjClassFunction (χ j)) =
      (c j i : ℂ) := hc j i
  have he (i) : I.induced i = ∑ j, (c j i : ℂ) • f j := by
    have hi : IsClassFunction (I.induced i) := inducedClassFunction_isClassFunction _ _
    have hh := completeFamily_sum_inner_smul_eq hχ (toConjClassFunction (I.induced i) hi)
    ext g
    have heval := congrFun hh (ConjClasses.mk g)
    simpa only [Finset.sum_apply, Pi.smul_apply, toConjClassFunction_apply,
      classFunctionInner_toConjClassFunction_right, hc', f, ofConjClassFunction_apply] using heval.symm
  have ho (i j : J) : scalarProduct G (f i) (f j) = if i = j then 1 else 0 := by
    simpa [f, scalarProduct_ofConjClassFunction] using completeFamily_orthonormal hχ i j
  refine ⟨⟨J, hJ, f, hf, hinj, hcomplete, fun i j => c j i, ?_, he, ?_, hv⟩⟩
  · exact fun i j => hc j i
  · intro i l
    have hh := I.gram i l
    change scalarProduct G (I.induced i) (I.induced l) = _ at hh
    rw [he i, he l, scalarProduct_integer_columns f ho] at hh
    exact_mod_cast hh


namespace IntegralExpansion
variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} (E : IntegralExpansion I)

/-- The coordinate of the principal character in the complete family. -/
@[expose] public def principalIndex : E.Index :=
  Classical.choose (E.complete 1 isIrreducibleCharacter_one)

public theorem principal_character : E.character E.principalIndex = 1 :=
  Classical.choose_spec (E.complete 1 isIrreducibleCharacter_one)

public theorem principal_coefficient (i : Fin 5) :
    E.coefficient i E.principalIndex = exceptionalCoefficients i 0 := by
  have h := E.multiplicity i E.principalIndex
  rw [E.principal_character] at h
  exact_mod_cast h.symm.trans (I.principal_multiplicity i)

public theorem norm_sq (i : Fin 5) :
    ∑ j, E.coefficient i j ^ 2 = exceptionalGram i i := by
  simpa only [pow_two] using E.gram i i

public theorem coefficient_sq_le (i : Fin 5) (j : E.Index) :
    E.coefficient i j ^ 2 ≤ exceptionalGram i i := by
  rw [← E.norm_sq]
  exact Finset.single_le_sum (fun l _ => sq_nonneg (E.coefficient i l)) (Finset.mem_univ j)

/-- Restrict a complete expansion to two constituents once its other coordinates vanish. -/
public theorem expansion_two (i : Fin 5) (p q : E.Index) (hpq : p ≠ q)
    (hz : ∀ j, j ≠ p → j ≠ q → E.coefficient i j = 0) :
    I.induced i = (E.coefficient i p : ℂ) • E.character p +
      (E.coefficient i q : ℂ) • E.character q := by
  classical
  rw [E.expansion]
  have hs : (∑ j ∈ ({p, q} : Finset E.Index), (E.coefficient i j : ℂ) • E.character j) =
      ∑ j, (E.coefficient i j : ℂ) • E.character j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [hz j hj.1 hj.2]
  rw [← hs]
  simp [hpq]

end IntegralExpansion

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
