module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven.Concrete
import Mathlib.Tactic.Group

/-!
# Three even marked relations and the segment involutions

The source word v centralizes x. The concrete element a*v(a,b)^2 is
conjugate to a. Hence in a binary central cover its lift squares to one;
commutation with the normalized lift of x forces the square of v's square
to be one as well. Concrete conjugacy then gives square-one lifts for all
nine segments needed below. Entries 4 and 6 are squares of two segments.
Entry 10 is a commutator with a factor whose image has order three, so
central-kernel coprimality lifts its concrete commutation.

All conclusions use the original presentation map and frozen marking.
Source: John Bray's `Held/Model/Source/HeG1-P1.M` and
`M1Restriction/Data.lean`. Entry 11 is assembled in `Eleven`.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
open PerfectCentralCovering Subgroup.CosetWordCertificate
variable {E : Type*} [Group E]

private theorem hx_sq (h : Presentation →* E) : h x ^ 2 = 1 := by
  rw [← map_pow, show x ^ 2 = 1 from presentation_relations 0, map_one]

theorem image_sourceV (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap) :
    f.toMonoidHom (h (sourceV x y)) = sourceV a b := by
  rw [← MonoidHom.comp_apply, ht, presentationMap_sourceV]

/-- The source commutation proves that the second seed also has square-one lifts. -/
theorem second_seed_square (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap) :
    (h (sourceV x y) ^ 2) ^ 2 = 1 := by
  have he : f.toMonoidHom (h x * h (sourceV x y) ^ 2) =
      (testConjugator 0)⁻¹ * f.toMonoidHom (h x) * testConjugator 0 := by
    rw [map_mul, map_pow, image_x f h ht, image_sourceV f h ht]
    exact test_conjugacy 0
  have hs := square_eq_one_of_image_conjugate f hc _ (h x) (hx_sq h) _ he
  have hcomm := (sourceV_commute.map h).pow_right 2
  rw [hcomm.mul_pow, hx_sq h, one_mul] at hs
  exact hs

theorem image_positive (f : Cover E He) (h : Presentation →* E)
    (ht : f.toMonoidHom.comp h = presentationMap) (w : List (Fin 3)) :
    f.toMonoidHom (positive (h ∘ liftedGenerator) w) = positive (marked a b) w := by
  rw [map_positive]
  congr 1
  funext i
  change f.toMonoidHom (h (liftedGenerator i)) = marked a b i
  rw [← MonoidHom.comp_apply, ht]
  exact (marked_concrete i).symm

/-- All nine segment involutions used in entries 4, 6 and 11 have square-one lifts. -/
theorem test_square (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap)
    (i : Fin 9) : positive (h ∘ liftedGenerator) (testLetters i) ^ 2 = 1 := by
  let j : Fin 10 := ⟨i.val + 1, by omega⟩
  let t : E := if secondClass j then h (sourceV x y) ^ 2 else h x
  have hp : t ^ 2 = 1 := by
    dsimp [t]
    split
    · exact second_seed_square f hc h ht
    · exact hx_sq h
  apply square_eq_one_of_image_conjugate f hc _ t hp (testConjugator j)
  rw [image_positive f h ht]
  have he : f.toMonoidHom t = testSeed j := by
    dsimp [t, testSeed]
    split
    · rw [map_pow, image_sourceV f h ht]
    · exact image_x f h ht
  rw [he]
  have hg : positive (marked a b) (testLetters i) = testElement j := by
    fin_cases i <;> rfl
  rw [hg]
  exact test_conjugacy j

theorem image_relation (h : Presentation →* E) (i : Fin 12) :
    h (eval liftedGenerator (relationLetters i)) =
      positive (h ∘ liftedGenerator) (relationIndices i) := by
  rw [relationLetters, ← positive_eval, map_positive]

theorem relation_four (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap) :
    h (eval liftedGenerator (relationLetters 4)) = 1 := by
  rw [image_relation]
  simpa only [positive, relationIndices, testLetters, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, pow_two, mul_one, mul_assoc] using test_square f hc h ht 0

theorem relation_six (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap) :
    h (eval liftedGenerator (relationLetters 6)) = 1 := by
  rw [image_relation]
  simpa only [positive, relationIndices, testLetters, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, pow_two, mul_one, mul_assoc] using test_square f hc h ht 1

theorem relation_ten (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap) :
    h (eval liftedGenerator (relationLetters 10)) = 1 := by
  let g := h ∘ liftedGenerator
  have hi (i : Fin 3) : (g i)⁻¹ = g i := by
    apply inv_eq_of_mul_eq_one_left
    change h (liftedGenerator i) * h (liftedGenerator i) = 1
    rw [← map_mul, ← pow_two, liftedGenerator_sq, map_one]
  have hcomm : Commute (positive g tenthRight) (positive g tenthLeft) := by
    apply commute_of_image_cube f hc
    · rw [image_positive f h ht]
      exact tenth_right_cube
    · rw [image_positive f h ht, image_positive f h ht]
      exact tenth_commute
  rw [image_relation]
  have he : positive g (relationIndices 10) = positive g tenthLeft *
      positive g tenthRight * (positive g tenthLeft)⁻¹ * (positive g tenthRight)⁻¹ := by
    simp only [positive, relationIndices, tenthLeft, tenthRight, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_inv_rev, hi, mul_assoc]
  change positive g (relationIndices 10) = 1
  rw [he, hcomm.symm.eq]
  simp only [mul_assoc, mul_inv_cancel, one_mul]

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
