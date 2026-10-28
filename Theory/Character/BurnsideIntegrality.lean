module

public import Theory.Character.Divisibility

/-!
# Integrality of normalized character values on coprime classes

For an irreducible character of degree `n`, both its value `χ(x)` and the
central-character value `|xᴳ| χ(x) / n` are algebraic integers. When `n` and
`|xᴳ|` are coprime, Bézout's identity expresses `χ(x) / n` as an integer
linear combination of these two integral values.

This is the algebraic input to Burnside's scalar-or-zero argument used in
Brauer--Tuan, *On simple groups of finite order I*, Bull. AMS 51 (1945),
Lemma 2, pp.763--764 (citing Burnside, p.322, Theorem I).
-/

public section
noncomputable section

namespace Representation
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]

/-- The normalized character value is integral when the degree and class size
are coprime. -/
theorem isIntegral_character_div_finrank_of_coprime_class_card
    (ρ : Representation ℂ G V) [IsIrreducible ρ] (x : G)
    (hc : (Module.finrank ℂ V).Coprime (Nat.card (ConjClasses.mk x).carrier)) :
    IsIntegral ℤ (ρ.character x / (Module.finrank ℂ V : ℂ)) := by
  let n := Module.finrank ℂ V
  let c := Nat.card (ConjClasses.mk x).carrier
  let a := Nat.gcdA n c
  let b := Nat.gcdB n c
  have hbez : (1 : ℂ) = (n : ℂ) * (a : ℂ) + (c : ℂ) * (b : ℂ) := by
    have h := Nat.gcd_eq_gcd_ab n c
    rw [hc.gcd_eq_one] at h
    exact_mod_cast h
  have hnontriv : Nontrivial V := irreducible_nontrivial ρ
  let := hnontriv
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hscalar : classSumScalar ρ (ConjClasses.mk x) =
      (c : ℂ) * ρ.character x / (n : ℂ) := by
    rw [classSumScalar_eq_card_mul_character_div ρ _
      (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl), char_one]
  have he : ρ.character x / (n : ℂ) =
      (a : ℂ) * ρ.character x + (b : ℂ) * classSumScalar ρ (ConjClasses.mk x) := by
    rw [hscalar]
    apply (div_eq_iff hn).mpr
    calc
      ρ.character x = 1 * ρ.character x := (one_mul _).symm
      _ = ((n : ℂ) * a + (c : ℂ) * b) * ρ.character x := by rw [← hbez]
      _ = _ := by field_simp
  rw [he]
  exact ((isIntegral_intCast (R := ℤ) (B := ℂ) a).mul
    (representation_character_isIntegral ρ x)).add
      ((isIntegral_intCast (R := ℤ) (B := ℂ) b).mul (classSumScalar_isIntegral ρ _))
end Representation
