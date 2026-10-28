module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.Action
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Blocks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.ClassConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InflatedCharacters
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters

/-!
# Assembly of the actual normalizer character table

The actual marked conjugacy classes, seven inflated A6 characters and five
inertia-induced characters are constructed from the local analysis. Joining
the two character families gives twelve irreducibles of degrees
1,9,10,8,8,5,5,45,45,30,15,15, with principal character at index zero.
Their full table distinguishes the rows. Internal conjugacy-class coverage
and cancellation on each nonspecial column prove the support clause needed
by exceptional induction.

`normalizerCharacterData_of_blocks` retains the conditional assembly API.
`nonempty_normalizerCharacterData` discharges all three construction inputs
and supplies the actual normalizer character record from local analysis alone.
It requires neither ambient simplicity nor an ambient order or identification.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–12.
-/

open scoped BigOperators
open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer}

private theorem irreducible_eq_of_isConj {H : Type*} [Group H]
    {χ : ClassFunction H} (hχ : IsIrreducibleCharacter χ) {x y : H}
    (hxy : IsConj x y) : χ x = χ y := by
  obtain ⟨n, ρ, _, rfl⟩ := hχ
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  rw [← hg]
  exact (Representation.char_conj (ρ := ρ) x g).symm

/-- Assemble the source normalizer record from actual class coverage and the
two separately constructed blocks of irreducible characters. -/
public def normalizerCharacterData_of_blocks
    (Q : NormalizerClassData D k) (A : NormalizerInflatedBlock Q)
    (B : NormalizerInducedBlock Q) : NormalizerCharacterData D k := by
  let χ : Fin 12 → ClassFunction (normalizer (CaseII.E D k : Set G)) :=
    Fin.append A.character B.character
  have hirr : ∀ j, IsIrreducibleCharacter (χ j) := by
    intro j
    refine Fin.addCases (m := 7) (n := 5) (fun j => ?_) (fun j => ?_) j
    · simpa only [χ, Fin.append_left] using A.irreducible j
    · simpa only [χ, Fin.append_right] using B.irreducible j
  have hv : ∀ j r, χ j (Q.representative r) = normalizerFullValues A.parameter j r := by
    intro j
    refine Fin.addCases (m := 7) (n := 5)
      (motive := fun j => ∀ r, χ j (Q.representative r) =
        normalizerFullValues A.parameter j r) (fun j r => ?_) (fun j r => ?_) j
    · simpa only [χ, Fin.append_left] using A.values j r
    · simpa only [χ, Fin.append_right] using
        (B.values j r).trans (normalizerFullValues_induced A.parameter j r).symm
  refine {
    character := χ
    irreducible := hirr
    injective := ?_
    principal := A.principal
    values := ?_
    support := ?_ }
  · intro i j hij
    apply normalizerFullValues_injective A.parameter A.parameter_equation
    funext r
    rw [← hv i r, ← hv j r, hij]
  · intro j r
    have h := hv j (Fin.castAdd 7 r)
    simpa only [Q.representative_special, normalizerFullValues, Fin.append_left] using h
  · intro i x hx
    obtain ⟨r, hr⟩ := Q.nonspecial_covers x hx
    have hval (j : Fin 12) : χ j x =
        normalizerNonspecialValues A.parameter j r := by
      rw [irreducible_eq_of_isConj (hirr j) hr, hv]
      exact Fin.append_right _ _ r
    simpa only [normalizerCombination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hval]
      using normalizerNonspecialValues_cancel A.parameter i r

/-- Janko's twelve actual irreducible normalizer characters, with the five
marked columns and vanishing of every prescribed combination off their
special support. All class and character witnesses are constructed from
the given local analysis. -/
public theorem nonempty_normalizerCharacterData [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k) :
    Nonempty (NormalizerCharacterData D k) := by
  obtain ⟨Q⟩ := nonempty_normalizerClassData D k L
  obtain ⟨A⟩ := normalizerInflatedBlock_nonempty D k L Q
  obtain ⟨B⟩ := nonempty_normalizerInducedBlock D k L Q
  exact ⟨normalizerCharacterData_of_blocks Q A B⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
