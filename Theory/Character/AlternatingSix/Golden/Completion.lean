module

public import Theory.Character.AlternatingSix.Golden.Interfaces
public import Theory.Character.Orthogonality

/-!
# Completing the rational character rows of A₆

The principal character and the four supplied rational rows embed into the
complete family of genuine irreducible characters. Their values at the identity
and at the marked element distinguish all five. The seven conjugacy classes
leave exactly two complementary indices. Subtracting the five known terms from
second orthogonality constructs `RationalCompletion`, without prescribing the
degrees or values of either complementary character.

Source: ordinary character completeness and second orthogonality; Janko,
*A characterization of the Mathieu simple groups, I* (1968), §6, pp.10–11.
-/

noncomputable section
open scoped BigOperators
namespace Theory.Character.AlternatingSix

private theorem completion_family_contains {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] {χ : ι → ConjClassFunction G}
    (hχ : IsCompleteIrreducibleCharacterFamily χ) {φ : ClassFunction G}
    (hφ : IsIrreducibleCharacter φ) :
    ∃ i, ofConjClassFunction (χ i) = φ := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hφ
  obtain ⟨i, hi⟩ := hχ.2.1 (characterClassFunction ρ)
    ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
  exact ⟨i, by rw [hi]; rfl⟩

private theorem completion_irreducible {G : Type*} [Group G] [Finite G]
    {χ : ConjClassFunction G} (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

private def completion_known {c : alternatingGroup (Fin 6)} (R : RationalBlock c) :
    Fin 5 → ClassFunction (alternatingGroup (Fin 6)) :=
  Fin.cases 1 R.character

private theorem completion_known_irreducible {c : alternatingGroup (Fin 6)}
    (R : RationalBlock c) (j : Fin 5) :
    IsIrreducibleCharacter (completion_known R j) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact isIrreducibleCharacter_one
  · exact R.irreducible k

private theorem completion_known_injective {c : alternatingGroup (Fin 6)}
    (R : RationalBlock c) : Function.Injective (completion_known R) := by
  have hfirst : Fin.cases (1 : ClassFunction (alternatingGroup (Fin 6)))
      R.character (1 : Fin 5) = R.character 0 := rfl
  intro i j hij
  have hv := congrArg (fun φ => (φ 1, φ c)) hij
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | norm_num [completion_known, hfirst, R.one, R.three, rationalValues,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four] at hv

/-- With seven conjugacy classes, the four rational rows and the principal
character have two genuine irreducible complements satisfying the full residual
second-orthogonality identity. The class count is the only construction input
beyond the supplied rational block. -/
public theorem rationalCompletion_of_class_count (c : alternatingGroup (Fin 6))
    (_hc : orderOf c = 3) (R : RationalBlock c)
    (hclasses : Nat.card (ConjClasses (alternatingGroup (Fin 6))) = 7) :
    Nonempty (RationalCompletion R) := by
  classical
  obtain ⟨ι, hι, χ, hχ, horth⟩ := second_orthogonality (G := alternatingGroup (Fin 6))
  let : Fintype ι := hι
  have hcard : Fintype.card ι = 7 := by
    obtain ⟨b, _hb⟩ := completeFamily_form_basis hχ
    calc
      Fintype.card ι = Module.finrank ℂ (ConjClassFunction (alternatingGroup (Fin 6))) :=
        (Module.finrank_eq_card_basis b).symm
      _ = Fintype.card (ConjClasses (alternatingGroup (Fin 6))) :=
        Module.finrank_fintype_fun_eq_card ℂ
      _ = 7 := by simpa only [Nat.card_eq_fintype_card] using hclasses
  choose f hf using fun j =>
    completion_family_contains hχ (completion_known_irreducible R j)
  have hfinj : Function.Injective f := by
    intro i j hij
    apply completion_known_injective R
    rw [← hf i, ← hf j, hij]
  let s : Finset ι := Finset.univ.image f
  have hs : s.card = 5 := by
    simp [s, Finset.card_image_of_injective _ hfinj]
  have hsc : sᶜ.card = 2 := by
    rw [Finset.card_compl, hcard, hs]
  let e : Fin 2 ≃ {i // i ∈ sᶜ} := (Finset.equivFinOfCardEq hsc).symm
  refine ⟨{
    character := fun j => ofConjClassFunction (χ (e j).val)
    irreducible := fun j => completion_irreducible (hχ.1 (e j).val)
    column := ?_ }⟩
  intro x y
  let t : ι → ℂ := fun i => χ i (ConjClasses.mk x) * star (χ i (ConjClasses.mk y))
  have hknown : ∑ i ∈ s, t i = rationalColumn R x y := by
    rw [Finset.sum_image (fun i _ j _ hij => hfinj hij)]
    simp only [t, ← ofConjClassFunction_apply, hf]
    simp [completion_known, Fin.sum_univ_succ, rationalColumn]
  have hremaining :
      ofConjClassFunction (χ (e 0).val) x * star (ofConjClassFunction (χ (e 0).val) y) +
      ofConjClassFunction (χ (e 1).val) x * star (ofConjClassFunction (χ (e 1).val) y) =
      ∑ i ∈ sᶜ, t i := by
    rw [← Finset.sum_coe_sort, ← e.sum_comp (fun i => t i.val)]
    simp [Fin.sum_univ_two, t, ofConjClassFunction]
  have hcentralizer : Nat.card {a : alternatingGroup (Fin 6) // a * x = x * a} =
      Nat.card (Subgroup.centralizer ({x} : Set _)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun a => Subgroup.mem_centralizer_singleton_iff.symm)
  have htotal : ∑ i, t i =
      if IsConj x y then (Nat.card (Subgroup.centralizer ({x} : Set _)) : ℂ) else 0 := by
    by_cases hxy : IsConj x y
    · rw [if_pos hxy]
      exact ((horth x y).1 (ConjClasses.mk_eq_mk_iff_isConj.mpr hxy)).trans
        (congrArg (fun n : ℕ => (n : ℂ)) hcentralizer)
    · rw [if_neg hxy]
      exact (horth x y).2 (fun h => hxy (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  rw [hremaining]
  have hsplit := Finset.sum_add_sum_compl s t
  rw [hknown, htotal] at hsplit
  exact eq_sub_of_add_eq' hsplit

end Theory.Character.AlternatingSix
