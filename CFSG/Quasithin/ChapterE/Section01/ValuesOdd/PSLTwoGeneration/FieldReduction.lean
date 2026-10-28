module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SL2.DefiningRank
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# The defining fields in the odd PSL₂ generation problem

The projective upper transvections embed the additive field in the ambient
strongly quasithin group. Its defining-prime rank therefore bounds the field
degree by two. We retain both the prime and prime-square possibilities, with
an actual matrix-group isomorphism in each case. Perfectness supplies the
nonabelianness required by the simple-socle E2 construction.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.3(2), A.2.17 and E.1.14(6), printed pp.33, 38--39 and 214.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration

open Matrix

variable {G : Type*} [Group G] [Finite G]

/-- The transvection subgroup rules out defining-field degree greater than two.
This only uses strong quasithinness, not the K-group clause or a classification. -/
theorem card_eq_prime_or_prime_sq_of_embedding {F : Type*} [Field F] [Finite F]
    (hG : IsStronglyQuasithin G) (hodd : Odd (Nat.card F))
    (j : ProjectiveSpecialLinearGroup (Fin 2) F →* G) (hj : Function.Injective j) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (Nat.card F = p ∨ Nat.card F = p ^ 2) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hc, n, hp, hn⟩ := FiniteField.card' F
  let : CharP F p := hc
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card F = p ^ (n : ℕ) := by simpa using hn
  have hpo : Odd p := (Nat.odd_pow_iff n.ne_zero).mp (hcard ▸ hodd)
  have hr : (n : ℕ) ≤ 2 :=
    (SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective hcard j hj).trans
      (hG p hp hpo)
  have hn12 : (n : ℕ) = 1 ∨ (n : ℕ) = 2 := by have := n.pos; omega
  refine ⟨p, hp, hpo, ?_⟩
  rcases hn12 with h | h
  · exact Or.inl (by simpa [h] using hcard)
  · exact Or.inr (by simpa [h] using hcard)

/-- Apply the field restriction to the literal subgroup model used in E.1.14(6). -/
theorem parameter_eq_prime_or_prime_sq (hG : IsStronglyQuasithin G)
    (L : Subgroup G) {q : ℕ} (hodd : Odd q) (hL : ClassicalGroup.IsPSL L 2 q) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (q = p ∨ q = p ^ 2) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL
  simpa only [hcard] using card_eq_prime_or_prime_sq_of_embedding hG
    (hcard ▸ hodd) (L.subtype.comp e.symm.toMonoidHom)
    (L.subtype_injective.comp e.symm.injective)

omit [Finite G] in
/-- The concrete model supplies nonabelianness for the simple-socle producer. -/
theorem nonabelian_of_model (L : Subgroup G) {q : ℕ} (hq : 5 < q)
    (hL : ClassicalGroup.IsPSL L 2 q) : ¬ IsMulCommutative L := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hL
  let : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Nontrivial L := e.symm.injective.nontrivial
  exact Group.IsPerfect.not_isMulCommutative L

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration
