module

public import Stellmacher.Recognition.LyonsU3Four.BrauerColumnInduction
public import Theory.Character.Inflation
public import Theory.Character.InvolutionRootInduction
public import Theory.Character.OrthonormalColumnGram

/-!
# Full Gram matrix of the genuine local section columns

Signs in each quartic row cancel in pairwise products. Ordinary row
orthogonality therefore gives diagonal 16 and off-diagonal 12. Inflation
through the actual odd core preserves these products, and cyclic-root support
makes induction to the ambient group an isometry.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381.
-/

public section
noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}
theorem localFiveSectionRow_gram (h : SylowStructure S) (w : QuarticCentralIndex S)
    (j k : FiveLinearIndex) :
    ∑ i : LocalFiveRowIndex S, localFiveSectionRow S w i j * localFiveSectionRow S w i k =
      (4 : ℤ) * (3 + if j = k then 1 else 0) := by
  have he (i : LocalFiveRowIndex S) :
      localFiveSectionRow S w i j * localFiveSectionRow S w i k =
      (localFiveDecompositionRow S i j : ℤ) * localFiveDecompositionRow S i k := by
    rcases i with χ | (⟨z, χ⟩ | i)
    · simp only [localFiveSectionRow, localFiveDecompositionRow, Sum.elim_inl,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    · by_cases hz : z = w <;> by_cases hj : χ = j <;> by_cases hk : χ = k <;>
        simp [localFiveSectionRow, localFiveDecompositionRow, hz, hj, hk]
    · simp [localFiveSectionRow, localFiveDecompositionRow]
  simp_rw [he]
  exact_mod_cast localFiveDecompositionRow_gram S h j k

theorem LocalFiveCharacterTable.sectionClassFunction_gram (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (w : QuarticCentralIndex S) (j k : FiveLinearIndex) :
    scalarProduct (LocalFiveGroup S α) (T.sectionClassFunction w j)
      (T.sectionClassFunction w k) = 4 * (3 + if j = k then 1 else 0) := by
  have hp := scalarProduct_integer_columns
    (fun i => ofConjClassFunction (T.row i))
    (fun i l => completeFamily_orthonormal T.row_complete i l)
    (fun i => localFiveSectionRow S w i j) (fun i => localFiveSectionRow S w i k)
  have he (j : FiveLinearIndex) : T.sectionClassFunction w j =
      ∑ i : LocalFiveRowIndex S, (localFiveSectionRow S w i j : ℂ) •
        ofConjClassFunction (T.row i) := by
    funext x
    simp only [LocalFiveCharacterTable.sectionClassFunction_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, ofConjClassFunction_apply]
    apply Finset.sum_congr
    · exact congrArg (@Fintype.elems (LocalFiveRowIndex S)) (Subsingleton.elim _ _)
    · intro i _; rfl
  rw [he j, he k, hp, localFiveSectionRow_gram h w j k]
  push_cast
  rfl

theorem LocalFiveCharacterTable.inflatedSectionClassFunction_isClassFunction (T : LocalFiveCharacterTable S α)
    (w : QuarticCentralIndex S) {H : Type*} [Group H]
    (N : Subgroup H) [N.Normal] (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (j : FiveLinearIndex) : IsClassFunction (T.inflatedSectionClassFunction w N e j) := by
  intro x g
  simp only [LocalFiveCharacterTable.inflatedSectionClassFunction,
    LocalFiveCharacterTable.sectionClassFunction_apply, map_mul, map_inv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact ofConjClassFunction_isClassFunction (T.row i) _ _

theorem LocalFiveCharacterTable.inflatedSectionClassFunction_gram (T : LocalFiveCharacterTable S α) (h : SylowStructure S)
    (w : QuarticCentralIndex S) {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (e : (H ⧸ N) ≃* LocalFiveGroup S α)
    (j k : FiveLinearIndex) :
    scalarProduct H (T.inflatedSectionClassFunction w N e j)
      (T.inflatedSectionClassFunction w N e k) = 4 * (3 + if j = k then 1 else 0) := by
  rw [show scalarProduct H (T.inflatedSectionClassFunction w N e j)
      (T.inflatedSectionClassFunction w N e k) =
      scalarProduct (LocalFiveGroup S α) (T.sectionClassFunction w j)
        (T.sectionClassFunction w k) from
    scalarProduct_comp_surjective (e.toMonoidHom.comp (QuotientGroup.mk' N))
      (e.surjective.comp (QuotientGroup.mk'_surjective N)) _ _]
  exact LocalFiveCharacterTable.sectionClassFunction_gram T h w j k
end Stellmacher.Recognition.LyonsU3Four
namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}
theorem LocalFiveCharacterTable.inducedSectionClassFunction_gram (T : LocalFiveCharacterTable S α)
    (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    {z : G} (hz : z ∈ centerImage S) (hz2 : orderOf z = 2)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (he : ∀ s : S, e (involutionCentralizerQuotientMap S hz s) = SemidirectProduct.inl s)
    (w : QuarticCentralIndex S) (hw : (w.1.1 : G) = z) (j k : FiveLinearIndex) :
    scalarProduct G
      (inducedClassFunction (centralizer ({z} : Set G))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e j))
      (inducedClassFunction (centralizer ({z} : Set G))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) e k)) =
      4 * (3 + if j = k then 1 else 0) := by
  rw [scalarProduct_inducedClassFunction_involutionRoots z hz2 _ _
    (LocalFiveCharacterTable.inflatedSectionClassFunction_isClassFunction T w _ e k)
    (T.inflatedSectionClassFunction_eq_zero_of_not_root h β hβ hα hz e he w hw j)
    (T.inflatedSectionClassFunction_eq_zero_of_not_root h β hβ hα hz e he w hw k)]
  convert LocalFiveCharacterTable.inflatedSectionClassFunction_gram T h w _ e j k using 1
  congr 1
  exact Subsingleton.elim _ _
end Stellmacher.Recognition.LyonsU3Four
