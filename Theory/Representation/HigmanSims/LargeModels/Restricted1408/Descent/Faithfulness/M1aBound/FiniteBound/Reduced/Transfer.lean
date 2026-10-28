module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.M1aBound.FiniteBound.Reduced.Presentation

/-!
# The two independent inputs for the ten-generator route

Actual relator identities construct a homomorphism into the original carrier.
The three additional marked identities, together with the checked generation
theorem, make it surjective. Only then does an independent finite bound for
the separate presentation bound the original group. Neither input is asserted
here. Source and exact remaining contracts: `source/README.md`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced
open Subgroup.CosetWordCertificate

def toOriginal
    (hr : ∀ r : Fin 597, eval candidateGenerator (relatorWord r) = 1) :
    Carrier →* Schreier.Carrier :=
  PresentedGroup.toGroup (f := candidateGenerator) (by
    rintro _ ⟨r, rfl⟩
    exact hr r)

theorem toOriginal_generator
    (hr : ∀ r : Fin 597, eval candidateGenerator (relatorWord r) = 1) (i : Fin 10) :
    toOriginal hr (generator i) = candidateGenerator i := PresentedGroup.toGroup.of _

theorem toOriginal_eval
    (hr : ∀ r : Fin 597, eval candidateGenerator (relatorWord r) = 1) (w : Word (Fin 10)) :
    toOriginal hr (eval generator w) = eval candidateGenerator w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    simp only [eval_cons, map_mul, ih]
    cases a with
    | mk i sign => cases sign <;> simp [toOriginal_generator]

theorem toOriginal_surjective
    (hr : ∀ r : Fin 597, eval candidateGenerator (relatorWord r) = 1)
    (hm : ∀ i : Fin 3, eval candidateGenerator (markedWord i) = threeGenerator i) :
    Function.Surjective (toOriginal hr) := by
  have h : Subgroup.closure (Set.range threeGenerator) ≤ (toOriginal hr).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨eval generator (markedWord i), (toOriginal_eval hr _).trans (hm i)⟩
  rw [threeGenerator_generates] at h
  exact MonoidHom.range_eq_top.mp (top_le_iff.mp h)

/-- Final cardinal transfer, with both independent proof obligations explicit. -/
theorem original_finite_card_of_inputs
    (hr : ∀ r : Fin 597, eval candidateGenerator (relatorWord r) = 1)
    (hm : ∀ i : Fin 3, eval candidateGenerator (markedWord i) = threeGenerator i)
    (hb : Finite Carrier ∧ Nat.card Carrier ≤ 443520) :
    Finite Schreier.Carrier ∧ Nat.card Schreier.Carrier ≤ 443520 := by
  let : Finite Carrier := hb.1
  have hs := toOriginal_surjective hr hm
  exact ⟨Finite.of_surjective _ hs, (Nat.card_le_card_of_surjective _ hs).trans hb.2⟩

/-- Literal source-subgroup consumer; no unproved comparison is hidden. -/
theorem m1a_finite_card_of_inputs
    (hr : ∀ r : Fin 597, eval candidateGenerator (relatorWord r) = 1)
    (hm : ∀ i : Fin 3, eval candidateGenerator (markedWord i) = threeGenerator i)
    (hb : Finite Carrier ∧ Nat.card Carrier ≤ 443520) :
    Finite M1a ∧ Nat.card M1a ≤ 443520 :=
  m1a_finite_card_of_bound (original_finite_card_of_inputs hr hm hb)

end Sporadic.LeechRelated.HS.AtlasPresentation.Faithfulness.M1aBound.Schreier.Reduced
