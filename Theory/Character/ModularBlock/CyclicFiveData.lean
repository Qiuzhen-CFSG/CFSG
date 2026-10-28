module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.ConstantRestriction
public import Mathlib.GroupTheory.Sylow

/-!
# Rows of a cyclic five-block with full automizer

For automizer order four the cyclic block has four nonexceptional rows and
one exceptional row. The exceptional multiplicity is one, so its period is
the sum of all four nontrivial fifth roots, namely minus one. Thus every
row is a constant sign on the punctured Sylow subgroup. We enumerate all
five rows together; the first row is principal. There is no intrinsic need
to distinguish the singleton exceptional row in this multiplicity-one case.

This module specifies the output of the row construction and derives its
degree congruences by restriction averaging. It does not assert existence.
Source: Fong (1967), printed p.75, citing Brauer (1942).
-/

public section
noncomputable section
namespace ModularBlock.CyclicFive
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The five actual principal-block rows in the full-automizer case. -/
structure FullAutomizerRows (d : PrimeCongruenceBlockData 5 G) (P : Sylow 5 G) where
  rows : Fin 5 ≃ {i : d.I // i ∈ d.block}
  principal_row : (rows 0).val = d.principal
  sign : Fin 5 → ℤ
  sign_unit : ∀ j, sign j = 1 ∨ sign j = -1
  value : ∀ (j : Fin 5) (u : P), u ≠ 1 →
    d.chi (rows j).val (ConjClasses.mk (u : G)) = (sign j : ℂ)

/-- The row signs imply the degree congruences; these are not extra fields
of the cyclic-block interface. -/
theorem FullAutomizerRows.degree_congruence
    {d : PrimeCongruenceBlockData 5 G} {P : Sylow 5 G}
    (r : FullAutomizerRows d P) (hP : Nat.card P = 5)
    (i : d.I) (hi : i ∈ d.block) (n : ℤ)
    (hn : d.chi i (ConjClasses.mk 1) = (n : ℂ)) :
    (5 : ℤ) ∣ n - 1 ∨ (5 : ℤ) ∣ n + 1 := by
  obtain ⟨j, hj⟩ := r.rows.surjective ⟨i, hi⟩
  have hji : (r.rows j).val = i := congrArg Subtype.val hj
  obtain ⟨m, ρ, hρ⟩ := (d.complete.1 i).1
  have hchar : IsCharacter (ofConjClassFunction (d.chi i)) :=
    ⟨m, ρ, by rw [hρ]; rfl⟩
  have hv (g : G) (hg : g ∈ (P : Subgroup G)) (hne : g ≠ 1) :
      ofConjClassFunction (d.chi i) g = (r.sign j : ℂ) := by
    have hh := r.value j ⟨g, hg⟩ (fun he => hne (congrArg Subtype.val he))
    simpa only [hji, ofConjClassFunction_apply] using hh
  have hd := hchar.card_dvd_degree_sub_of_constant (P : Subgroup G) n
    (r.sign j) hn hv
  change (Nat.card P : ℤ) ∣ n - r.sign j at hd
  rw [hP] at hd
  rcases r.sign_unit j with hs | hs
  · exact Or.inl (by simpa [hs] using hd)
  · exact Or.inr (by simpa [hs] using hd)

/-- No row of degree congruent to two modulo five occurs in these rows. -/
theorem FullAutomizerRows.degree_not_two_mod_five
    {d : PrimeCongruenceBlockData 5 G} {P : Sylow 5 G}
    (r : FullAutomizerRows d P) (hP : Nat.card P = 5)
    (i : d.I) (hi : i ∈ d.block) (n : ℤ)
    (hn : d.chi i (ConjClasses.mk 1) = (n : ℂ)) : n % 5 ≠ 2 := by
  have h := r.degree_congruence hP i hi n hn
  omega

end ModularBlock.CyclicFive
