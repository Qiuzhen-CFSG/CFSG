module

public import ABG.Recognition.ThreeLinearCharacters
public import Theory.Character.Integrality
public import Theory.Character.UniqueDegreeRationality
public import Theory.Character.SimpleFaithful
public import Theory.Character.FiniteOrderTrace

/-!
# Values of Wong's degree-twelve character

The character throughout is the original catalog entry `χ 5`. Its actual
irreducible representation supplies algebraic integrality and, for a simple
group, faithfulness. Uniqueness in degree twelve gives rationality under Galois
conjugation, hence integer-valuedness at every element. At order thirteen the value is `-1`:
prime-order traces are congruent to the dimension modulo thirteen and have
absolute value at most twelve; faithfulness excludes the endpoint twelve.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix (b), p.109, before equation (14).
-/

namespace ABG
open BenderGlauberman
noncomputable section

namespace ThreeGlobalDegreeData

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- The original catalog degree-twelve character has algebraic-integer values. -/
public theorem sixth_value_isIntegral (hG : Nat.card G = 5616) (g : G) :
    IsIntegral ℤ (c.decomposition.χ 5 g) := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨ρ, _hρ, hχ⟩ := c.exists_sixth_representation hG
  rw [hχ]
  exact character_value_isIntegral ρ g

/-- Degree uniqueness forces every value of the original sixth character to be rational. -/
public theorem sixth_value_rational (hG : Nat.card G = 5616) (g : G) :
    ∃ q : ℚ, c.decomposition.χ 5 g = (q : ℂ) := by
  apply (c.decomposition.irreducible 5).rational_of_unique_degree
  intro θ hθ hdegree
  exact c.degree_twelve_unique hG hθ (hdegree.trans (c.sixth_degree_twelve hG))

/-- The original sixth character is integer-valued everywhere, in particular
on elements of order three used in Wong's orthogonality calculation. -/
public theorem sixth_value_integer (hG : Nat.card G = 5616) (g : G) :
    ∃ a : ℤ, c.decomposition.χ 5 g = (a : ℂ) := by
  apply (c.decomposition.irreducible 5).integer_of_unique_degree
  intro θ hθ hdegree
  exact c.degree_twelve_unique hG hθ (hdegree.trans (c.sixth_degree_twelve hG))

/-- The representation of the original sixth character can be chosen faithful. -/
public theorem exists_faithful_sixth_representation [IsSimpleGroup G]
    (hG : Nat.card G = 5616) :
    ∃ ρ : Representation ℂ G (Fin 12 → ℂ),
      Representation.IsIrreducible ρ ∧ Function.Injective ρ ∧
      c.decomposition.χ 5 = ρ.character := by
  obtain ⟨ρ, hρ, hχ⟩ := c.exists_sixth_representation hG
  let : Representation.IsIrreducible ρ := hρ
  exact ⟨ρ, hρ, ρ.injective_of_isSimpleGroup_of_one_lt_finrank (by simp), hχ⟩

/-- The order-thirteen value calculation needs only integer-valuedness at
that element, independently of any conjugacy-class census. -/
public theorem sixth_order_thirteen_value_of_integer [IsSimpleGroup G]
    (hG : Nat.card G = 5616) {g : G} (hg : orderOf g = 13)
    (hint : ∃ a : ℤ, c.decomposition.χ 5 g = (a : ℂ)) :
    c.decomposition.χ 5 g = -1 := by
  obtain ⟨ρ, _, hinj, hχ⟩ := c.exists_faithful_sixth_representation hG
  rw [hχ] at hint ⊢
  have hpow : (ρ g) ^ 13 = 1 := by
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hne : ρ g ≠ 1 := by
    intro h
    have hg1 : g = 1 := hinj (h.trans ρ.map_one.symm)
    simp [hg1] at hg
  exact prime_order_integer_trace_eq_neg_one (ρ g) (by norm_num) hpow
    (by simp) hne hint

/-- Wong's original degree-twelve character has value `-1` at every element
of order thirteen, without any assumption about the conjugacy-class census. -/
public theorem sixth_order_thirteen_value [IsSimpleGroup G]
    (hG : Nat.card G = 5616) {g : G} (hg : orderOf g = 13) :
    c.decomposition.χ 5 g = -1 :=
  c.sixth_order_thirteen_value_of_integer hG hg (c.sixth_value_integer hG g)

end ThreeGlobalDegreeData
end
end ABG
