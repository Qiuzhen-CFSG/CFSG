module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedQuotients.Coordinates
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointExtension.Generators

/-!
# Generation by the two native M₁₂ tensor actors

The saved candidate words in `../source/generator-words.json` are checked as
literal permutations of the twelve points. They recover the two embedded M₁₁
actors, so their closure contains the whole point stabilizer. The first M₁₂
actor moves the marked point, and maximality of its stabilizer gives generation.

This supplies the all-elements invariance step for the induced-heart flag,
used in the degree calculation of James, J. Algebra 27 (1973), 57–111,
and Aschbacher–Smith Chapter K, printed pp.451 and 457.
-/

public noncomputable section
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients.Flag
open M12Recognition M12Recognition.PointExtension

private def word : List (Fin 2) → M12
  | [] => 1
  | j :: l => actor j * word l

private def permWord : List (Fin 2) → Equiv.Perm (Fin 12)
  | [] => 1
  | j :: l => actorPerm j * permWord l

private theorem word_perm (l : List (Fin 2)) : (word l).val = permWord l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change (actor j).val * (word l).val = _
    rw [ih]
    have hj : (actor j).val = actorPerm j := by fin_cases j <;> rfl
    rw [hj]
    rfl

private def pointAWord : List (Fin 2) :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]

private theorem word_a : word pointAWord = a := by
  apply Subtype.ext
  rw [word_perm, a_perm]
  decide +kernel

private def pointBWord : List (Fin 2) :=
  [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0,
    1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1]

private theorem word_b : word pointBWord = b := by
  apply Subtype.ext
  rw [word_perm, b_perm]
  decide +kernel

private theorem word_mem (H : Subgroup M12) (hH : ∀ j, actor j ∈ H)
    (l : List (Fin 2)) : word l ∈ H := by
  induction l with
  | nil => exact H.one_mem
  | cons j l ih => exact H.mul_mem (hH j) ih

/-- The literal two actors generate all of native M₁₂. -/
theorem actors_closure_eq_top : Subgroup.closure (Set.range actor) = ⊤ := by
  let H := Subgroup.closure (Set.range actor)
  have hH (j : Fin 2) : actor j ∈ H := Subgroup.subset_closure ⟨j, rfl⟩
  have ha : a ∈ H := by rw [← word_a]; exact word_mem H hH _
  have hb : b ∈ H := by rw [← word_b]; exact word_mem H hH _
  have hp : (⊤ : Subgroup M11) ≤ H.comap pointEmbedding := by
    rw [← m11_generators_closure_eq_top, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact ha
    · rcases hg with rfl
      exact hb
  have hle : MulAction.stabilizer M12 (12 : Fin 12) ≤ H := by
    have hs : Function.Surjective m11ToM12PointStabilizer :=
      (m11ToM12PointStabilizer_injective.bijective_of_nat_card_le
        (by exact (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).ge)).surjective
    intro g hg
    obtain ⟨x, hx⟩ := hs ⟨g, hg⟩
    have he : pointEmbedding x = g := congrArg Subtype.val hx
    rw [← he]
    exact hp (Subgroup.mem_top x)
  exact m12PointStabilizerTwelve_isCoatom.lt_iff.mp
    (lt_of_le_of_ne hle (by
      intro he
      apply t_not_mem
      rw [he]
      exact hH 0))

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients.Flag
