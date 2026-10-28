module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.UniformWords
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.WeylDuality

/-!
# Descent for fixed Weyl words over every Ree field

Exceptional duality pairs the simple right descents. The longest word in that
pair decreases Weyl length and is itself a fixed matrix. Induction therefore
writes every fixed simple word as a product of the two fixed orbit words.
`UniformWords` supplies the faithful matrix comparison over the present field.

This extends the binary descent of `BruhatCoverage/FixedWeyl.lean`.
Source: GLS3 2.3.2–4, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair.QuotientGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

private theorem rootWord_duality (l : List (Fin 4)) (r : F4Chevalley.Root) :
    exceptionalRootPermutation (typeF4RootPairing.weylGroupToPerm (rootWord l) r) =
      typeF4RootPairing.weylGroupToPerm (rootWord (l.map Fin.revPerm))
        (exceptionalRootPermutation r) := by
  simpa only [rootWord, List.map_map, Function.comp_def,
    WordRelations.simplePermutation_numbered] using
      WordRelations.exceptionalRootPermutation_wordProd
        (l.map typeF4RootPairing_baseEquiv) r

private theorem descent_rev {l : List (Fin 4)}
    (hl : reeTwist m (simpleWord m l) = simpleWord m l) (i : Fin 4)
    (hi : ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l) (typeF4RootPairing_baseEquiv i))) :
    ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm (rootWord l)
        (typeF4RootPairing_baseEquiv (Fin.revPerm i))) := by
  rw [reeTwist_simpleWord] at hl
  have hw := (simpleWord_eq_iff m _ _).mp hl
  have he := rootWord_duality l (typeF4SimpleRootIndex i)
  rw [hw, exceptionalRootPermutation_simple] at he
  simp only [← typeF4RootPairing_baseEquiv_val] at he
  intro hpos
  apply hi
  apply (WordRelations.exceptionalRootPermutation_isPos _).mp
  rwa [he]

private theorem exists_descent (w : typeF4RootPairing.weylGroup) (hw : w ≠ 1) :
    ∃ i : Fin 4, ¬ typeF4RootPairing_base.IsPos
      (typeF4RootPairing.weylGroupToPerm w (typeF4RootPairing_baseEquiv i)) := by
  classical
  obtain ⟨l, hlen, he⟩ := typeF4RootPairing_base.wordLength_spec w
  have hl : l ≠ [] := by
    intro hl
    apply hw
    rw [← he, hl]
    rfl
  let i := l.getLast hl
  obtain ⟨j, hj⟩ := typeF4RootPairing_baseEquiv.surjective i
  refine ⟨j, ?_⟩
  rw [hj]
  have hprod : typeF4RootPairing_base.wordProd l.dropLast *
      typeF4RootPairing_base.simpleReflection i = w := by
    rw [← he, ← List.dropLast_append_getLast hl]
    simp [i]
  have hlength : l.dropLast.length + 1 = typeF4RootPairing_base.wordLength w := by
    simpa [hlen] using congrArg List.length (List.dropLast_append_getLast hl)
  intro hp
  have hup := typeF4RootPairing_base.wordLength_mul_simpleReflection_of_isPos w i hp
  have hlo := typeF4RootPairing_base.wordLength_le
    (w * typeF4RootPairing_base.simpleReflection i) l.dropLast (by
      rw [← hprod]
      simp [mul_assoc])
  omega

private theorem side_drop (l : List (Fin 4))
    (hl : reeTwist m (simpleWord m l) = simpleWord m l)
    (hw : rootWord l ≠ 1) :
    ∃ s : LargeLocalSeeds.Side,
      typeF4RootPairing_base.wordLength (rootWord (l ++ sideWord s)) <
        typeF4RootPairing_base.wordLength (rootWord l) := by
  obtain ⟨i, hi⟩ := exists_descent (rootWord l) hw
  have hj := descent_rev hl i hi
  obtain ⟨C, _, hC, _⟩ := typeF4RootPairing_base.weylGroup_coxeterPresentation
  have h03 : C (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 3) = 2 := by
    rw [hC]
    apply simpleReflection_mul_order_eq_two_of_cartan_zero
    norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]; decide
  have h12 : C (typeF4RootPairing_baseEquiv 1) (typeF4RootPairing_baseEquiv 2) = 4 := by
    rw [hC]
    apply simpleReflection_mul_order_eq_four_of_cartan_neg_two_neg_one
    · norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]; decide
    · norm_num [typeF4RootPairing_base_cartan_apply, typeF4CartanMatrix]; decide
  have hlinear
      (h0 : ¬ typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm
        (rootWord l) (typeF4RootPairing_baseEquiv 0)))
      (h3 : ¬ typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm
        (rootWord l) (typeF4RootPairing_baseEquiv 3))) :
      typeF4RootPairing_base.wordLength (rootWord (l ++ sideWord .linear)) <
        typeF4RootPairing_base.wordLength (rootWord l) := by
    have h := typeF4RootPairing_base.wordLength_mul_braidWord_add_eq_of_two_descents
      C hC (rootWord l) (typeF4RootPairing_baseEquiv 0) (typeF4RootPairing_baseEquiv 3) h0 h3
    simp only [CoxeterSystem.braidWord, h03, CoxeterSystem.alternatingWord,
      List.concat_eq_append, List.nil_append, List.cons_append] at h
    change typeF4RootPairing_base.wordLength
      (rootWord l * rootWord (sideWord .linear)) + 2 = _ at h
    rw [← rootWord_append] at h
    omega
  have hsuzuki
      (h1 : ¬ typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm
        (rootWord l) (typeF4RootPairing_baseEquiv 1)))
      (h2 : ¬ typeF4RootPairing_base.IsPos (typeF4RootPairing.weylGroupToPerm
        (rootWord l) (typeF4RootPairing_baseEquiv 2))) :
      typeF4RootPairing_base.wordLength (rootWord (l ++ sideWord .suzuki)) <
        typeF4RootPairing_base.wordLength (rootWord l) := by
    have h := typeF4RootPairing_base.wordLength_mul_braidWord_add_eq_of_two_descents
      C hC (rootWord l) (typeF4RootPairing_baseEquiv 1) (typeF4RootPairing_baseEquiv 2) h1 h2
    simp only [CoxeterSystem.braidWord, h12, CoxeterSystem.alternatingWord,
      List.concat_eq_append, List.nil_append, List.cons_append] at h
    change typeF4RootPairing_base.wordLength
      (rootWord l * rootWord (sideWord .suzuki)) + 4 = _ at h
    rw [← rootWord_append] at h
    omega
  fin_cases i
  · exact ⟨.linear, hlinear hi hj⟩
  · exact ⟨.suzuki, hsuzuki hi hj⟩
  · exact ⟨.suzuki, hsuzuki hj hi⟩
  · exact ⟨.linear, hlinear hj hi⟩

/-- A twist-fixed Weyl word is generated by the two fixed orbit words. -/
theorem fixed_simpleWord_mem_map (m : ℕ) (l : List (Fin 4))
    (hl : reeTwist m (simpleWord m l) = simpleWord m l) :
    simpleWord m l ∈ (weylSubgroup m).map (toSplitGroup m) := by
  have aux : ∀ n : ℕ, ∀ l : List (Fin 4),
      typeF4RootPairing_base.wordLength (rootWord l) = n →
      reeTwist m (simpleWord m l) = simpleWord m l →
      simpleWord m l ∈ (weylSubgroup m).map (toSplitGroup m) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlen hfixed
      by_cases hw : rootWord l = 1
      · have he : simpleWord m l = 1 := by
          change simpleWord m l = simpleWord m []
          apply (simpleWord_eq_iff m _ _).mpr
          simpa [rootWord] using hw
        rw [he]
        exact Subgroup.one_mem _
      obtain ⟨s, hs⟩ := side_drop l hfixed hw
      have hs' : typeF4RootPairing_base.wordLength (rootWord (l ++ sideWord s)) < n := by
        rwa [hlen] at hs
      have hp := ih _ hs' (l ++ sideWord s) rfl (by
        rw [simpleWord_append, map_mul, hfixed, sideWord_fixed])
      have hside : simpleWord m (sideWord s) ∈ (weylSubgroup m).map (toSplitGroup m) := by
        simpa only [toSplitGroup_weylLift] using
          Subgroup.mem_map_of_mem (toSplitGroup m) (weylLift_mem_weylSubgroup m s)
      rw [simpleWord_append] at hp
      simpa only [mul_inv_cancel_right] using
        ((weylSubgroup m).map (toSplitGroup m)).mul_mem hp
          (((weylSubgroup m).map (toSplitGroup m)).inv_mem hside)
  exact aux _ l rfl hl

end ReeF4.SectionGeometry.BNPair.QuotientGeometry
