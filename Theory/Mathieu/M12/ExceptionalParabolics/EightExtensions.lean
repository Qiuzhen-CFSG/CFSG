module
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions.Coverage
public import Theory.Mathieu.M12.ExceptionalParabolics.TwistObstruction
public import Theory.GroupTheory.Amalgam.TwistTransport

/-!
# Extending eight-preserving automorphisms of the M₁₂ overlap

Every automorphism of the literal marked Sylow subgroup preserving the normal
elementary eight of the first parabolic extends to that parabolic. The proof
constructs four endpoint automorphisms from certified permutations of its
192 coordinates. Words in these automorphisms realize all generator-image
triples satisfying the necessary order tests and the eight-preservation test.
Equality on the three overlap generators then proves the literal inclusion
square commutes.

This is the subgroup-preserving extension calculation used in the M₁₂ case
of Aschbacher--Smith F.1.11--12, printed pp.262--263. The marked permutations
retain the attribution of `SmallParabolicPair.Seeds` (14.2.21, printed p.988).
The argument uses neither a uniqueness theorem nor a faithfulness premise.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
open Theory.GroupTheory.RankTwoAmalgam SylowAutomorphismGroup
set_option maxRecDepth 1000000

theorem mem_overlapEight_iff : ∀ i : Fin 64,
    SylowAutomorphismGroup.element i ∈ TwistObstruction.overlapEight ↔ inEight i := by
  change ∀ i : Fin 64,
    (∃ a : ElementaryCoordinates,
      TwistObstruction.leftEightEmbedding a = (SylowAutomorphismGroup.element i : M12)) ↔ _
  decide +kernel



private theorem powerTest_iff (i : Fin 64) (n : ℕ) :
    powerTest i n ↔ element i ^ n = 1 ∧ element i ^ (n / 2) ≠ 1 := by
  have he (k : ℕ) : power i k = 0 ↔ element i ^ k = 1 := by
    rw [← element_injective.eq_iff, element_power, element_zero]
  exact and_congr (he n) (not_congr (he (n / 2)))

private theorem powerTest_map (d : MulAut sylowCandidate) {i j : Fin 64}
    (h : element i = d (element j)) (n : ℕ) : powerTest i n ↔ powerTest j n := by
  rw [powerTest_iff, powerTest_iff]
  have he (k : ℕ) : element i ^ k = 1 ↔ element j ^ k = 1 := by
    rw [h, ← map_pow, d.map_eq_one_iff]
  exact and_congr (he n) (not_congr (he (n / 2)))

private theorem admissible_of_aut (d : MulAut sylowCandidate) (a b c : Fin 64)
    (ha : element a = d (element 1)) (hb : element b = d (element 2))
    (hc : element c = d (element 3)) : admissible a b c := by
  have hbase : admissible 1 2 3 := by decide +kernel
  rcases hbase with ⟨h1,h2,h3,h12,h13,h23,h133⟩
  refine ⟨(powerTest_map d ha 4).mpr h1, (powerTest_map d hb 4).mpr h2,
    (powerTest_map d hc 8).mpr h3, ?_, ?_, ?_, ?_⟩
  · apply (powerTest_map d (i := multiply a b) (j := multiply 1 2) ?_ 2).mpr h12
    simp only [element_multiply, ha, hb, map_mul]
  · apply (powerTest_map d (i := multiply a c) (j := multiply 1 3) ?_ 4).mpr h13
    simp only [element_multiply, ha, hc, map_mul]
  · apply (powerTest_map d (i := multiply b c) (j := multiply 2 3) ?_ 2).mpr h23
    simp only [element_multiply, hb, hc, map_mul]
  · apply (powerTest_map d (i := multiply (multiply a c) c)
      (j := multiply (multiply 1 3) 3) ?_ 2).mpr h133
    simp only [element_multiply, ha, hc, map_mul]

/-- An automorphism preserving the specified normal eight extends across the
literal inclusion of the overlap into the first marked parabolic. -/
theorem extendsAcross_of_preserves_overlapEight (d : MulAut sylowCandidate)
    (hE : TwistObstruction.overlapEight.map d.toMonoidHom =
      TwistObstruction.overlapEight) :
    ExtendsAcross amalgam.left d := by
  obtain ⟨a, ha⟩ := element_surjective (d (element 1))
  obtain ⟨b, hb⟩ := element_surjective (d (element 2))
  obtain ⟨c, hc⟩ := element_surjective (d (element 3))
  have himages : ∀ j : Fin 3, element (![a,b,c] j) = d (generator j) := by
    intro j
    fin_cases j
    · exact ha.trans (congrArg d (element_generator 0))
    · exact hb.trans (congrArg d (element_generator 1))
    · exact hc.trans (congrArg d (element_generator 2))
  have he : inEight (multiply a b) := by
    apply (mem_overlapEight_iff _).mp
    have heq : element (multiply a b) = d (element (multiply 1 2)) := by
      simp only [element_multiply, ha, hb, map_mul]
    rw [heq, ← hE]
    exact Subgroup.mem_map_of_mem d.toMonoidHom
      ((mem_overlapEight_iff _).mpr (by decide +kernel))
  obtain ⟨k, hk⟩ := covers a b c (admissible_of_aut d a b c ha hb hc) he
  refine ⟨wordAutomorphism (candidateWord k), ?_⟩
  have hhom : (wordAutomorphism (candidateWord k)).toMonoidHom.comp amalgam.left =
      amalgam.left.comp d.toMonoidHom := by
    apply hom_ext
    intro j
    change wordAutomorphism (candidateWord k) (amalgam.left (generator j)) =
      amalgam.left (d (generator j))
    calc
      wordAutomorphism (candidateWord k) (amalgam.left (generator j)) =
          wordAutomorphism (candidateWord k)
            (Coordinates.element (Coordinates.overlapIndex ⟨j.val + 1, by omega⟩)) := by
        rw [Coordinates.element_overlap, element_generator]
        rfl
      _ = Coordinates.element
          (candidateImage k (Coordinates.overlapIndex ⟨j.val + 1, by omega⟩)) :=
        wordAutomorphism_element _ _
      _ = Coordinates.element (Coordinates.overlapIndex (![a,b,c] j)) := congrArg _ (hk j)
      _ = amalgam.left (element (![a,b,c] j)) := Coordinates.element_overlap _
      _ = amalgam.left (d (generator j)) := congrArg amalgam.left (himages j)
  exact fun x => congrArg (fun f : sylowCandidate →* firstParabolic => f x) hhom

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
