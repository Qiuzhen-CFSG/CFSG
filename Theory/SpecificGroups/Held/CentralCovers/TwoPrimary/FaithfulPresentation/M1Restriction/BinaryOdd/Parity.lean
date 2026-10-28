module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.RelatorLifts.Even.Schreier
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
# Binary parity in the literal source M₁

Two equations in the checked Schreier--Tietze certificate force the product
of the three marked generator images to be one in every abelian group of
exponent two. The symbols remain elements of the abstract source subgroup.
The equations are certificate entries 28759 and 29234; no faithfulness or
model multiplier is used. This is the obstruction to a common nontrivial
central twist in the binary odd-word argument.

Source: John Bray's ATLAS `Held/Model/Source/HeG1-P1.M` and the checked
`M1Cosets/TietzeTransfer` certificate, with its original symbol numbering.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
open M1Cosets Theory.GroupTheory.CosetEnumeration

private theorem symbol_mem (n : Nat) : Schreier.symbol n ∈ m1 := by
  by_cases hz : n = 0
  · subst n
    exact m1.one_mem
  by_cases hn : n < 2063
  · have he : n - 1 + 1 = n := by omega
    simpa only [he] using schreier_symbol_mem ⟨n - 1, by omega⟩
  · have h4 : ¬ n < 4 := by omega
    simpa only [Schreier.symbol, Schreier.symbolWord, if_neg hz, if_neg h4,
      if_neg hn, Subgroup.CosetWordCertificate.eval_nil] using m1.one_mem

private def symbolLift (n : Nat) : m1 := ⟨Schreier.symbol n, symbol_mem n⟩

private theorem map_eval {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : Nat → G) (w : Word Nat) :
    f (eval g w) = eval (fun n => f (g n)) w := by
  induction w with
  | nil => exact map_one f
  | cons a w ih =>
    simp only [eval, List.map_cons, List.prod_cons, map_mul] at *
    rw [ih]
    rcases a with ⟨a, b⟩
    cases b <;> simp [letterValue]

private theorem initialLift (r : Fin 14409) :
    eval symbolLift (Schreier.initialRelator r) = 1 := by
  apply Subtype.ext
  change m1.subtype (eval symbolLift _) = m1.subtype 1
  rw [map_eval, map_one]
  exact Schreier.initialRelator_eval r

/-- Binary abelian images of the three marked generators have product one. -/
theorem marked_binary_parity {A : Type*} [CommGroup A]
    (hs : ∀ a : A, a ^ 2 = 1) (χ : m1 →* A) :
    χ ⟨liftedGenerator 0, liftedGenerator_mem 0⟩ *
      χ ⟨liftedGenerator 1, liftedGenerator_mem 1⟩ *
      χ ⟨liftedGenerator 2, liftedGenerator_mem 2⟩ = 1 := by
  let g : Nat → A := fun n => χ (symbolLift n)
  have hi (r : Fin 14409) : eval g (Schreier.initialRelator r) = 1 := by
    rw [← map_eval, initialLift, map_one]
  have hv := TietzeTransfer.Certificate.valid (TietzeTransfer.Initials.valid hi)
  have ha : (g 688)⁻¹ * (g 273)⁻¹ * g 3 * g 422 * g 1 * g 2 * (g 422)⁻¹ * (g 273)⁻¹ = 1 := by
    have hh := hv 28759 (by decide)
    change eval g [(688,false),(273,false),(3,true),(422,true),(1,true),
      (2,true),(422,false),(273,false)] = 1 at hh
    simpa [eval, letterValue, mul_assoc] using hh
  have hb : (g 688)⁻¹ * (g 688)⁻¹ * (g 273)⁻¹ * g 1 * (g 688)⁻¹ *
      (g 273)⁻¹ * (g 480)⁻¹ * (g 480)⁻¹ * g 1 = 1 := by
    have hh := hv 29234 (by decide)
    change eval g [(688,false),(688,false),(273,false),(1,true),(688,false),
      (273,false),(480,false),(480,false),(1,true)] = 1 at hh
    simpa [eval, letterValue, mul_assoc] using hh
  have hinv (a : A) : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs a)
  simp only [hinv] at ha hb
  have hg688 : g 688 = 1 := by
    calc
      g 688 = g 688 * (g 688 ^ 2 * g 273 ^ 2 * g 1 ^ 2 * g 480 ^ 2) := by simp [hs]
      _ = g 688 * g 688 * g 273 * g 1 * g 688 * g 273 * g 480 * g 480 * g 1 := by simp only [pow_two]; ac_rfl
      _ = 1 := hb
  have hprod : g 1 * g 2 * g 3 = 1 := by
    calc
      _ = g 688 * g 273 * g 3 * g 422 * g 1 * g 2 * g 422 * g 273 := by
        rw [hg688, one_mul]
        calc
          _ = g 1 * g 2 * g 3 * (g 273 ^ 2 * g 422 ^ 2) := by simp [hs]
          _ = _ := by simp only [pow_two]; ac_rfl
      _ = 1 := ha
  have hg (i : Fin 3) : g (i.val + 1) = χ ⟨liftedGenerator i, liftedGenerator_mem i⟩ := by
    apply congrArg χ
    apply Subtype.ext
    exact schreierSymbol_eq_liftedGenerator i
  have h0 : g 1 = χ ⟨liftedGenerator 0, liftedGenerator_mem 0⟩ := hg 0
  have h1 : g 2 = χ ⟨liftedGenerator 1, liftedGenerator_mem 1⟩ := hg 1
  have h2 : g 3 = χ ⟨liftedGenerator 2, liftedGenerator_mem 2⟩ := hg 2
  rw [← h0, ← h1, ← h2]
  exact hprod
end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryOdd
