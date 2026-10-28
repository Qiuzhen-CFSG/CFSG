module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Coordinates
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.RootDuality.Negation
public import Theory.SpecificGroups.ReeF4.Field
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation

/-!
# Root geometry for the short F4 operators

Weyl reflections preserve the short-root class. If a short root and another
root sum to a long root, both summands are short and orthogonal, so the root
string coefficient is exactly two. Together with the even long-to-short
Cartan entries, this is the parity input for the short ideal in characteristic
two. The conventions are those of the standard F4 pairing and Geck's integral
Cartan-plus-root construction; see Steinberg, *Lectures on Chevalley Groups*.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix

namespace ReeF4.WordRelations.ShortOperators
local notation "P" => typeF4RootPairing
local notation "b" => typeF4RootPairing_base

lemma isShortRoot_reflection (r s : typeF4Roots) :
    IsShortRoot (typeF4RootPairing.reflectionPerm r s) ↔ IsShortRoot s := by
  simp only [isShortRoot_iff_longIndex, RootPairing.isLongIndex_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t, rfl⟩ := (typeF4RootPairing.reflectionPerm r).surjective t
    exact ⟨t, by simpa only [RootPairing.pairingIn_reflectionPerm, RootPairing.reflectionPerm_self] using ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨typeF4RootPairing.reflectionPerm r t, by
      simpa only [RootPairing.pairingIn_reflectionPerm, RootPairing.reflectionPerm_self] using ht⟩

lemma isShortRoot_reflectionWord (w : List typeF4RootPairing_base.support) (s : typeF4Roots) :
    IsShortRoot (reflectionWord w s) ↔ IsShortRoot s := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [reflectionWord, isShortRoot_reflection] using ih

lemma isShortRoot_simple (i : Fin 4) :
    IsShortRoot (typeF4RootPairing_baseEquiv i).val ↔ 2 ≤ i.val := by
  change (¬ (typeF4SimpleRootIndex i).val ∈ pairRoots 4) ↔ _
  rw [typeF4SimpleRootIndex_mem_pair_iff]
  omega

lemma long_short_cartan
    (i j : typeF4RootPairing_base.support) (hi : ¬IsShortRoot i.val) (hj : IsShortRoot j.val) :
    (|typeF4RootPairing_base.cartanMatrix i j| : ℤ) = 0 ∨ (|typeF4RootPairing_base.cartanMatrix i j| : ℤ) = 2 := by
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
  obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  rw [isShortRoot_simple] at hi hj
  rw [typeF4RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases j <;> norm_num [typeF4CartanMatrix] at *

private lemma dot_add_self (x y : Vec 4) :
    dot (x + y) (x + y) = dot x x + 2 * dot x y + dot y y := by
  change (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x]
  ring

lemma short_add_long (i j k : typeF4Roots) (hi : IsShortRoot i)
    (hk : IsLongRoot k) (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    IsShortRoot j ∧ dot i.val j.val = 0 := by
  have hn : 2 = 1 + 2 * dot i.val j.val + dot j.val j.val := by
    have hn := dot_add_self i.val j.val
    change k.val = i.val + j.val at h
    rw [← h, isLongRoot_norm k hk, isShortRoot_norm i hi] at hn
    exact hn
  have hj : IsShortRoot j := by
    by_contra hj
    have hj' : IsLongRoot j := not_not.mp hj
    rw [isLongRoot_norm j hj'] at hn
    have hp : (typeF4RootPairing.pairingIn ℤ i j : ℝ) = dot i.val j.val := by
      change algebraMap ℤ ℝ _ = _
      rw [typeF4RootPairing.algebraMap_pairingIn,
        typeF4RootPairing_pairing, typeF4CorootScale_of_pair j hj', one_mul]
    have he : (2 : ℤ) * typeF4RootPairing.pairingIn ℤ i j = -1 := by
      exact_mod_cast (show (2 : ℝ) * (typeF4RootPairing.pairingIn ℤ i j : ℝ) = -1 by linarith)
    omega
  exact ⟨hj, by rw [isShortRoot_norm j hj] at hn; linarith⟩

lemma short_add_long_chainBot (i j k : typeF4Roots) (hi : IsShortRoot i)
    (hk : IsLongRoot k) (h : typeF4RootPairing.root k = typeF4RootPairing.root i + typeF4RootPairing.root j) :
    typeF4RootPairing.chainBotCoeff i j = 1 := by
  obtain ⟨hj, hd⟩ := short_add_long i j k hi hk h
  have hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j] := by
    apply RootPairing.IsReduced.linearIndependent P
    · intro he
      rw [he, isShortRoot_norm j hj] at hd
      norm_num at hd
    · intro he
      have he' : typeF4RootPairing.root k = 0 := by rw [h, he]; abel
      exact typeF4RootPairing.ne_zero k he'
  have hp : typeF4RootPairing.pairingIn ℤ j i = 0 := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_zero]
    change algebraMap ℤ ℝ _ = _
    rw [typeF4RootPairing.algebraMap_pairingIn, typeF4RootPairing_pairing,
      typeF4CorootScale_of_not_pair i hi]
    have hd' : dot j.val i.val = 0 := by simpa only [dot, mul_comm] using hd
    rw [hd', mul_zero]
  have hdiff := typeF4RootPairing.chainBotCoeff_sub_chainTopCoeff hlin
  have hbound := typeF4RootPairing.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  have htop : 1 ≤ typeF4RootPairing.chainTopCoeff i j := by
    apply (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mp
    exact ⟨k, by simpa only [one_smul, add_comm] using h⟩
  rw [hp] at hdiff
  omega
end ReeF4.WordRelations.ShortOperators
