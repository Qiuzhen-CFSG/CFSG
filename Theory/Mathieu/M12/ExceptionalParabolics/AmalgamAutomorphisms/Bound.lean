module

public import Theory.Mathieu.M12.ExceptionalParabolics.AmalgamAutomorphisms.Certificate
public import Theory.Mathieu.M12.ExceptionalParabolics.AmalgamAutomorphisms.FirstRestriction
public import Theory.Mathieu.M12.ExceptionalParabolics.AmalgamAutomorphisms.SecondGenerators

/-!
# The M₁₂ marked-amalgam automorphism bound

A compatible automorphism is determined by its second endpoint, and that
endpoint is determined by the images of its two marked quaternion elements
and moving cubic. Compatibility puts the first two images in the original
Sylow overlap. The cubic certificate gives 32 possible cubic images; for
each one the five preserved order tests leave four possible pairs of Sylow
images. Thus there are at most 128 compatible automorphisms.

Every test is applied to the actual endpoint automorphism and original
inclusion maps. This is the finite automorphism bound in Goldschmidt,
Automorphisms of trivalent graphs, §3.8, used for the M₁₂ branch of
Aschbacher--Smith F.1.12, printed p.263.
-/

public section
noncomputable section

namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms
open Theory.GroupTheory SylowAutomorphismGroup
set_option maxRecDepth 1000000

private theorem powerTests_map (f : secondParabolic →* M12) (hf : Function.Injective f)
    (x : secondParabolic) (n : ℕ) (hx : x ^ n = 1 ∧ x ^ (n / 2) ≠ 1) :
    (f x) ^ n = 1 ∧ (f x) ^ (n / 2) ≠ 1 := by
  constructor
  · rw [← map_pow, hx.1, map_one]
  · intro h
    apply hx.2
    apply hf
    rw [map_pow, h, map_one]

private theorem second_eq_iff (x y : secondParabolic) : x = y ↔ (x : M12) = (y : M12) :=
  Subtype.ext_iff

private theorem marked_order_tests :
    ((secondGenerator 0) ^ 4 = 1 ∧ (secondGenerator 0) ^ 2 ≠ 1) ∧
    ((secondGenerator 1) ^ 4 = 1 ∧ (secondGenerator 1) ^ 2 ≠ 1) ∧
    ((secondGenerator 0 * secondGenerator 1) ^ 2 = 1 ∧
      secondGenerator 0 * secondGenerator 1 ≠ 1) ∧
    ((secondGenerator 2 * secondGenerator 0 * secondGenerator 2) ^ 8 = 1 ∧
      (secondGenerator 2 * secondGenerator 0 * secondGenerator 2) ^ 4 ≠ 1) ∧
    ((secondGenerator 2 * secondGenerator 1) ^ 4 = 1 ∧
      (secondGenerator 2 * secondGenerator 1) ^ 2 ≠ 1) := by
  have ambient :
      (leftI ^ 4 = 1 ∧ leftI ^ 2 ≠ 1) ∧
      (rightI ^ 4 = 1 ∧ rightI ^ 2 ≠ 1) ∧
      ((leftI * rightI) ^ 2 = 1 ∧ leftI * rightI ≠ 1) ∧
      ((movingActor * leftI * movingActor) ^ 8 = 1 ∧
        (movingActor * leftI * movingActor) ^ 4 ≠ 1) ∧
      ((movingActor * rightI) ^ 4 = 1 ∧ (movingActor * rightI) ^ 2 ≠ 1) := by
    decide +kernel
  obtain ⟨h0, h1, h01, h202, h21⟩ := ambient
  have not_coe {x y : secondParabolic} (h : (x : M12) ≠ (y : M12)) : x ≠ y := by
    intro he
    apply h
    exact congrArg Subtype.val he
  have h0' : secondGenerator 0 ^ 2 ≠ (1 : secondParabolic) :=
    not_coe (by simpa only [Subgroup.coe_pow, Subgroup.coe_one, secondGenerator_zero]
      using h0.2)
  have h1' : secondGenerator 1 ^ 2 ≠ (1 : secondParabolic) :=
    not_coe (by simpa only [Subgroup.coe_pow, Subgroup.coe_one, secondGenerator_one]
      using h1.2)
  have h01' : secondGenerator 0 * secondGenerator 1 ≠ (1 : secondParabolic) :=
    not_coe (by simpa only [Subgroup.coe_mul, Subgroup.coe_one,
      secondGenerator_zero, secondGenerator_one] using h01.2)
  have h202' : (secondGenerator 2 * secondGenerator 0 * secondGenerator 2) ^ 4 ≠
      (1 : secondParabolic) :=
    not_coe (by simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one,
      secondGenerator_zero, secondGenerator_two] using h202.2)
  have h21' : (secondGenerator 2 * secondGenerator 1) ^ 2 ≠ (1 : secondParabolic) :=
    not_coe (by simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one,
      secondGenerator_one, secondGenerator_two] using h21.2)
  refine ⟨⟨Subtype.ext h0.1, h0'⟩, ⟨Subtype.ext h1.1, h1'⟩,
    ⟨Subtype.ext h01.1, h01'⟩, ⟨Subtype.ext h202.1, h202'⟩,
    ⟨Subtype.ext h21.1, h21'⟩⟩

private theorem cubic_cube : (secondGenerator 2) ^ 3 = 1 := by
  apply Subtype.ext
  change movingActor ^ 3 = 1
  simpa only [movingActor_order] using pow_orderOf_eq_one movingActor

private theorem cubic_ne_one : secondGenerator 2 ≠ 1 := by
  decide +kernel

private def HasCode (e : RankTwoAmalgam.Iso amalgam amalgam)
    (c : Fin 32 × Fin 4) : Prop :=
  (e.right (secondGenerator 0) : M12) =
      (element (Certificate.images c.1 c.2).1 : M12) ∧
  (e.right (secondGenerator 1) : M12) =
      (element (Certificate.images c.1 c.2).2 : M12) ∧
  (e.right (secondGenerator 2) : M12) = Certificate.cubic c.1

private theorem exists_code (e : RankTwoAmalgam.Iso amalgam amalgam) :
    ∃ c : Fin 32 × Fin 4, HasCode e c := by
  let f : secondParabolic →* M12 := secondParabolic.subtype.comp e.right.toMonoidHom
  have hf : Function.Injective f := secondParabolic.subtype_injective.comp e.right.injective
  obtain ⟨a, ha⟩ := element_surjective (e.middle (generator 0))
  obtain ⟨b, hb⟩ := element_surjective (e.middle (generator 1))
  have hA : f (secondGenerator 0) = (element a : M12) := by
    have h := congrArg (fun x : secondParabolic => (x : M12)) (e.right_commutes (generator 0))
    exact h.trans (congrArg Subtype.val ha).symm
  have hB : f (secondGenerator 1) = (element b : M12) := by
    have h := congrArg (fun x : secondParabolic => (x : M12)) (e.right_commutes (generator 1))
    exact h.trans (congrArg Subtype.val hb).symm
  have hcube : (e.right (secondGenerator 2)) ^ 3 = 1 := by
    rw [← map_pow, cubic_cube, map_one]
  have hne : e.right (secondGenerator 2) ≠ 1 := by
    intro h
    exact cubic_ne_one (e.right.injective (h.trans (map_one e.right).symm))
  obtain ⟨y, hy⟩ := Certificate.cubic_surjective (e.right (secondGenerator 2)) hcube hne
  have hY : f (secondGenerator 2) = Certificate.cubic y := hy.symm
  obtain ⟨h0, h1, h01, h202, h21⟩ := marked_order_tests
  have ha' : (element a : M12) ^ 4 = 1 ∧ (element a : M12) ^ 2 ≠ 1 := by
    simpa only [hA] using powerTests_map f hf (secondGenerator 0) 4 h0
  have hb' : (element b : M12) ^ 4 = 1 ∧ (element b : M12) ^ 2 ≠ 1 := by
    simpa only [hB] using powerTests_map f hf (secondGenerator 1) 4 h1
  have hab : ((element a : M12) * (element b : M12)) ^ 2 = 1 ∧
      (element a : M12) * (element b : M12) ≠ 1 := by
    have h01' : (secondGenerator 0 * secondGenerator 1) ^ 2 = 1 ∧
        (secondGenerator 0 * secondGenerator 1) ^ (2 / 2) ≠ 1 := by
      simpa only [Nat.reduceDiv, pow_one] using h01
    simpa only [map_mul, hA, hB, Nat.reduceDiv, pow_one] using
      powerTests_map f hf (secondGenerator 0 * secondGenerator 1) 2 h01'
  have hay : (Certificate.cubic y * (element a : M12) * Certificate.cubic y) ^ 8 = 1 ∧
      (Certificate.cubic y * (element a : M12) * Certificate.cubic y) ^ 4 ≠ 1 := by
    simpa only [map_mul, hA, hY] using
      powerTests_map f hf (secondGenerator 2 * secondGenerator 0 * secondGenerator 2) 8 h202
  have hby : (Certificate.cubic y * (element b : M12)) ^ 4 = 1 ∧
      (Certificate.cubic y * (element b : M12)) ^ 2 ≠ 1 := by
    simpa only [map_mul, hB, hY] using
      powerTests_map f hf (secondGenerator 2 * secondGenerator 1) 4 h21
  obtain ⟨k, hk⟩ := Certificate.covers y a b ha' hb' hab hay hby
  refine ⟨(y, k), ?_⟩
  change (e.right (secondGenerator 0) : M12) = (element (Certificate.images y k).1 : M12) ∧
    (e.right (secondGenerator 1) : M12) = (element (Certificate.images y k).2 : M12) ∧
    (e.right (secondGenerator 2) : M12) = Certificate.cubic y
  rw [hk]
  exact ⟨hA, hB, hY⟩

private def code (e : RankTwoAmalgam.Iso amalgam amalgam) : Fin 32 × Fin 4 :=
  Classical.choose (exists_code e)

private theorem code_spec (e : RankTwoAmalgam.Iso amalgam amalgam) : HasCode e (code e) :=
  Classical.choose_spec (exists_code e)

private theorem code_injective : Function.Injective code := by
  intro e f h
  apply iso_right_injective
  apply MulEquiv.toMonoidHom_injective
  apply second_hom_ext
  intro i
  have he := code_spec e
  have hf := code_spec f
  rw [← h] at hf
  apply Subtype.ext
  fin_cases i
  · exact he.1.trans hf.1.symm
  · exact he.2.1.trans hf.2.1.symm
  · exact he.2.2.trans hf.2.2.symm

instance : Finite (RankTwoAmalgam.Iso amalgam amalgam) :=
  Finite.of_injective code code_injective

/-- At most 128 compatible automorphisms of the actual marked M₁₂ amalgam exist. -/
theorem card_amalgamAut_le : Nat.card (RankTwoAmalgam.Iso amalgam amalgam) ≤ 128 := by
  have h := Nat.card_le_card_of_injective code code_injective
  simpa only [Nat.card_prod, Nat.card_fin] using h

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms
