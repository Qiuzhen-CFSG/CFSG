module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.Checked
public import Theory.GroupTheory.DihedralPresentation

/-!
# A concrete presentation bounding the literal M₁ₐ subgroup

Every defining relation has been proved in Universal by Schreier telescoping.
The evaluation image contains all three literal M₁ₐ generators, so a finite
bound for this separate presentation bounds M₁ₐ. Its first and third generators
already generate a finite dihedral quotient of order at most ten, providing a
base for a subsequent local coset certificate.

Source: ATLAS HSG1-P1.M and Reidemeister–Schreier rewriting of the retained
100-row table. See `source/README.md` for conventions and the remaining input.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
open Subgroup.CosetWordCertificate

/-- Every original relation is rewritten at every representative. -/
def rels : Set (FreeGroup (Fin 101)) :=
  Set.range (fun p : Fin 100 × Fin 13 => FreeGroup.mk (relatorWord p.1 p.2))

/-- A separate presented group on the non-tree Schreier edges. -/
abbrev Carrier := PresentedGroup rels

def localGenerator : Fin 101 → Carrier := PresentedGroup.of

theorem localGenerator_generates : Subgroup.closure (Set.range localGenerator) = ⊤ :=
  PresentedGroup.closure_range_of rels

theorem local_relator (i : Fin 100) (r : Fin 13) :
    eval localGenerator (relatorWord i r) = 1 := by
  rw [eval, ← FreeGroup.lift_unique (f := localGenerator) (PresentedGroup.mk rels) (fun _ => rfl)]
  exact PresentedGroup.one_of_mem ⟨(i, r), rfl⟩

/-- Each abstract edge is evaluated at its literal word in the HS presentation. -/
def toUniversal : Carrier →* Universal :=
  PresentedGroup.toGroup (f := edgeGenerator) (by
    rintro _ ⟨⟨i, r⟩, rfl⟩
    exact relator_valid i r)

@[simp] theorem toUniversal_generator (k : Fin 101) :
    toUniversal (localGenerator k) = edgeGenerator k := PresentedGroup.toGroup.of _

/-- The three specified M₁ₐ generators occur in the image in their source order. -/
theorem marked_images (i : Fin 3) :
    toUniversal (localGenerator (![0, 2, 1] i)) = m1aGenerator i := by
  rw [toUniversal_generator]
  fin_cases i <;> simp [edgeGenerator, edgeWord, eval_cons, m1aGenerator, mul_assoc]

/-- The image contains exactly the generating words required for the M₁ₐ bound. -/
theorem m1a_le_range : M1a ≤ toUniversal.range := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨localGenerator (![0, 2, 1] i), marked_images i⟩

/-- A finite bound for this presentation bounds the actual subgroup of Universal. -/
theorem m1a_finite_card_of_bound {n : Nat}
    (h : Finite Carrier ∧ Nat.card Carrier ≤ n) :
    Finite M1a ∧ Nat.card M1a ≤ n := by
  let : Finite Carrier := h.1
  have hs := toUniversal.rangeRestrict_surjective
  let : Finite toUniversal.range := Finite.of_surjective _ hs
  let f := Subgroup.inclusion m1a_le_range
  have hf : Function.Injective f := Subgroup.inclusion_injective m1a_le_range
  exact ⟨Finite.of_injective f hf,
    (Nat.card_le_card_of_injective f hf).trans
      ((Nat.card_le_card_of_surjective _ hs).trans h.2)⟩

/-- A small finite subgroup available to a subsequent local coset enumeration. -/
def dihedralSubgroup : Subgroup Carrier :=
  Subgroup.closure ({localGenerator 2, localGenerator 0} : Set Carrier)

theorem first_square : localGenerator 0 ^ 2 = 1 := by
  have hw : relatorWord 0 0 = [(0, true), (0, true)] := by decide +kernel
  have h := local_relator 0 0
  rw [hw] at h
  simpa [eval_cons, pow_two] using h

theorem third_square : localGenerator 2 ^ 2 = 1 := by
  have hw : relatorWord 2 0 = [(2, true), (2, true)] := by decide +kernel
  have h := local_relator 2 0
  rw [hw] at h
  simpa [eval_cons, pow_two] using h

theorem first_third_fifth : (localGenerator 0 * localGenerator 2) ^ 5 = 1 := by
  have hw : relatorWord 0 4 =
      [(0, false), (2, true), (0, false), (2, true), (0, false), (2, true),
       (0, false), (2, true), (0, false), (2, true)] := by decide +kernel
  have h := local_relator 0 4
  have hi : (localGenerator 0)⁻¹ = localGenerator 0 :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using first_square)
  rw [hw] at h
  simpa [eval_cons, hi, pow_succ, mul_assoc] using h

/-- The first and third edge generators generate a quotient of the dihedral group of order 10. -/
theorem dihedralSubgroup_finite_card :
    Finite dihedralSubgroup ∧ Nat.card dihedralSubgroup ≤ 10 :=
  Subgroup.closure_pair_finite_card_le_of_involutions (by decide : 0 < 5)
    (localGenerator 2) (localGenerator 0) third_square first_square first_third_fifth

/-- One possible certificate interface for the outstanding numerical bound. -/
theorem finite_card_of_cover
    (C : Subgroup.GeneratorCosetCover dihedralSubgroup localGenerator (Fin 44352)) :
    Finite Carrier ∧ Nat.card Carrier ≤ 443520 := by
  let : Finite dihedralSubgroup := dihedralSubgroup_finite_card.1
  obtain ⟨hf, hc⟩ := C.finite_card_le localGenerator_generates
  refine ⟨hf, hc.trans ?_⟩
  simpa using Nat.mul_le_mul_right 44352 dihedralSubgroup_finite_card.2

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier
