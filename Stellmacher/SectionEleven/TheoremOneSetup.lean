module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.SectionEleven.TheoremOneNoStrongEmbedding

/-!
# The theorem-one setup for Sections 5–10

The original Baumann-local hypothesis and two distinct maximal two-locals
containing the prescribed Sylow subgroup imply all of Section 5's Hypothesis 1.
The existence of a two-local forces even ambient order. A nontrivial ambient
two-core would make the whole group two-local, forcing the two maximal locals
to coincide. The Baumann subgroup lies in its defining Sylow subgroup, so the
local solvability and characteristic-two condition restricts to its overgroups.

The imported strong-embedding exclusion supplies the remaining field using
the actual local characteristic-two condition and multiple-maximal hypothesis.
It obtains a four-group from the maximal locals, eliminates the odd core via
involution fusion and coprime fixed-point generation, and applies the proved
Bender–Suzuki theorem to force a strongly embedded subgroup to be two-local.
This proves the initial reduction for case (i) in Section 11 of
`refs/latex/stellmacher-n-group.tex`, using exactly Theorem 1's hypotheses.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

universe u

variable {H : Type u} [Group H] [Finite H]

private theorem even_of_two_local (P : Subgroup H) (hP : IsTwoLocal P) :
    Even (Nat.card H) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨Q, hQne, hQp, _⟩ := hP
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  obtain ⟨n, hn, hcard⟩ := hQp.nontrivial_iff_card.mp inferInstance
  apply even_iff_two_dvd.mpr
  apply dvd_trans (b := Nat.card Q) _ Q.card_subgroup_dvd_card
  rw [hcard]
  exact dvd_pow_self 2 hn.ne'

omit [Finite H] in
private theorem twoCore_eq_bot_of_multiple_maximal
    (P1 P2 : Subgroup H) (hne : P1 ≠ P2)
    (hP1 : IsMaximalTwoLocal P1) (hP2 : IsMaximalTwoLocal P2) :
    pCore 2 H = ⊥ := by
  by_contra hcore
  have htop : IsTwoLocal (⊤ : Subgroup H) :=
    ⟨pCore 2 H, hcore, pCore_isPGroup, (Subgroup.normalizer_eq_top (pCore 2 H)).symm⟩
  have hP1top : P1 = ⊤ := le_top.antisymm (hP1.2 htop le_top)
  have hP2top : P2 = ⊤ := le_top.antisymm (hP2.2 htop le_top)
  exact hne (hP1top.trans hP2top.symm)

private theorem setup_fields_of_theorem_one_hypotheses
    (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U → baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧ IsMaximalTwoLocal P1 ∧ IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧ (S0 : Subgroup H) ≤ P2) :
    Even (Nat.card H) ∧ pCore 2 H = ⊥ ∧
      ∀ U : Subgroup H, IsTwoLocal U → (S0 : Subgroup H) ≤ U →
        Group.IsSolvable U ∧ IsCharacteristicTwoType U := by
  obtain ⟨P1, P2, hne, hP1, hP2, _, _⟩ := hmax
  refine ⟨even_of_two_local P1 hP1.prop,
    twoCore_eq_bot_of_multiple_maximal P1 P2 hne hP1 hP2, ?_⟩
  intro U hU hS
  exact hlocal U hU ((show baumannSubgroup S0 ≤ (S0 : Subgroup H) from inf_le_left).trans hS)

/-- The original hypotheses of Theorem 1 supply Hypothesis 1 for the same Sylow. -/
public theorem hypothesis_one_of_theorem_one_hypotheses
    (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U → baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧ IsMaximalTwoLocal P1 ∧ IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧ (S0 : Subgroup H) ≤ P2) :
    HypothesisOne H S0 := by
  obtain ⟨heven, hcore, hSlocal⟩ :=
    setup_fields_of_theorem_one_hypotheses S0 hlocal hmax
  exact ⟨heven, hSlocal, hcore,
    no_strongly_embedded_of_theorem_one_hypotheses S0 hlocal hmax⟩

end Stellmacher.SectionEleven
