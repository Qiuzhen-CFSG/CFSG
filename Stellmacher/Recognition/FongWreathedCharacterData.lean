module

public import Stellmacher.Recognition.FongWreathedOrder
public import Stellmacher.Recognition.FongWreathedBorelData
public import Theory.Character.DefectZeroVanishing

/-!
# Fong's complete character data

The genuine eight-character packet, its classified rational rows, and the
order-6048 theorem supply the character input of the Borel construction.
The first four rows remain those of the exceptional packet; the distinguished
row has degree and values (27, 3, -1, 3). All eight entries at F are retained.
Since a Sylow three subgroup has order 27, ordinary defect-zero vanishing
proves vanishing of the degree-27 character on every three-singular element.

The final existence theorem discharges all character and order assumptions
from a height-two wreathed Sylow subgroup and one solvable involution
centralizer in a finite simple group. The imported order theorem also
supplies the self-centralizing subgroup of order seven.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed pp.69–75, especially equation (10)
and the degree-27 vanishing argument on p.75; the numerical completion is
refs/original/n-group-global/sylow32-source-audit/fong-degree-calculation-audit.md.
-/

public section
open ModularBlock.PrincipalBlockConstruction

namespace Stellmacher.Recognition.FongWreathedExceptional.Characters
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
  {d : PrincipalCongruenceBlockData G} (c : Characters S P d)

/-- The actual exceptional packet supplies every field of the Borel character
contract. The Sylow-three order is 27, so ordinary defect-zero vanishing
applies to the distinguished degree-27 irreducible. -/
noncomputable def characterData (hG : Nat.card G = 6048) : FongWreathed.CharacterData P := by
  have hj : FongWreathed.J P = ((FongWreathedIntrinsic.J P : S) : G) := by
    rw [FongWreathed.J_eq_x]
    rfl
  have hrow := c.conditions.classification.1
  refine {
    chi := c.eight.chi
    irreducible := c.eight.irreducible
    injective := c.eight.injective
    principal := c.eight.first_four.1
    degree := by rw [c.eight.first_four.2.1]; exact c.degree_twenty_seven
    integer_values := by rw [c.eight.first_four.2.1]; exact c.rational.integer_values.1
    at_J := ?_
    at_X_mul_F_sq := ?_
    at_F_sq := ?_
    vanishes := ?_
    at_F := c.eight.F_values }
  · rw [c.eight.first_four.2.1, hj, c.rational.row₂_values.2.1, hrow]
    norm_num
  · change c.eight.chi 1 ((FongWreathedIntrinsic.X P *
        FongWreathedIntrinsic.F P ^ 2 : S) : G) = -1
    rw [c.eight.first_four.2.1, c.rational.row₂_values.2.2.1, hrow]
    norm_num
  · change c.eight.chi 1 ((FongWreathedIntrinsic.F P ^ 2 : S) : G) = 3
    rw [c.eight.first_four.2.1, c.rational.row₂_values.2.2.2, hrow]
    norm_num
  · intro g hg
    rw [c.eight.first_four.2.1]
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let T : Sylow 3 G := Classical.choice inferInstance
    have hT : Nat.card T = 27 := by
      rw [T.card_eq_multiplicity, hG, show (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 by norm_num]
      simp only [Nat.factorization_mul (by norm_num : 2 ^ 5 * 3 ^ 3 ≠ 0)
        (by norm_num : 7 ≠ 0), Nat.factorization_mul (by norm_num : 2 ^ 5 ≠ 0)
        (by norm_num : 3 ^ 3 ≠ 0), Nat.prime_two.factorization_pow,
        Nat.prime_three.factorization_pow, (by norm_num : Nat.Prime 7).factorization]
      norm_num [Finsupp.single_apply]
    exact OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree T
      c.rational.irreducible.1 (n := 27) c.degree_twenty_seven (by rw [hT]) g hg

/-- The conversion retains the original eight genuine principal-block
characters, in their original order. -/
theorem characterData_chi (hG : Nat.card G = 6048) :
    (c.characterData hG).chi = c.eight.chi := by
  exact Eq.trans rfl rfl

end Stellmacher.Recognition.FongWreathedExceptional.Characters

namespace Stellmacher.Recognition.FongWreathed
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The complete character input of the Borel construction, together with
Fong's order, under the original local group hypotheses. -/
theorem exists_characterData_and_card_eq_6048
    (S : Sylow 2 G) (hS : ABG.IsWreathedOfHeight S 2) (x : G)
    (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] :
    ∃ P : ABG.Wreathed.Presentation S 2,
      Nonempty (CharacterData P) ∧ Nat.card G = 6048 := by
  obtain ⟨P, d, ⟨c⟩⟩ := FongWreathedExceptional.exists_characters S hS x hx
  have hG := card_eq_6048 S hS x hx
  exact ⟨P, ⟨c.characterData hG⟩, hG⟩

end Stellmacher.Recognition.FongWreathed
