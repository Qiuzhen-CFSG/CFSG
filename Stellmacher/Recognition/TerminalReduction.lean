module

public import Stellmacher.Recognition.LargeTerminalContext
public import Stellmacher.Recognition.CatalogueReduction

/-!
# A simple N2 reduction retaining the large terminal context

The original Section11 reduction first separates strongly embedded groups
and two-local odd cores. In the remaining case it supplies HypothesisOne
and the ambient two-local solvability and characteristic-two conditions.
The multiple-maximal branch now retains its actual large SectionTen
terminal context, including the derived absence of transvections. This
keeps the data needed for subsequent involution-centralizer recognition.

Bender--Suzuki and Gorenstein--Walter give actual catalogue models in the
recognized branches; the local Sp4 configuration is impossible. The
unique-maximal branch gives the same semidihedral and order32 alternatives
as before. All unresolved local branches retain the proved triviality of
every two-local odd core. The G2 type and global odd-core branch remain explicit.
No existing local-classification theorem is changed and no missing
recognition premise is added. Source: Stellmacher, Theorem2 and Section11.
-/

namespace Stellmacher.Recognition
open SectionEleven SectionsFiveToSeven
universe u

private theorem model_of_dihedral
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S0 : Sylow 2 G) (hd : IsDihedralGroup S0) :
    IsNTwoGroupModel G := by
  rcases simple_dihedral_recognition hns S0 hd with hA | hPSL
  · obtain ⟨e⟩ := hA
    exact Or.inl (.alternatingSeven e)
  · obtain ⟨K, hK, hfinite, hodd, ⟨e⟩⟩ := hPSL
    let _ := hK
    let _ := hfinite
    exact isNTwoGroupModel_of_odd_psl2 hns K hodd e

/-- The actual large terminal context is retained in the simple N2 case split. -/
public theorem simple_nTwo_terminal_reduction
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S0 : Sylow 2 G) :
    IsNTwoGroupModel G ∨
    ((∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) ∧
      (IsOfGTwoTwoDerivedType G ∨ Nonempty (LargeTerminalContext S0) ∨
        IsSemidihedralGroup S0 ∨
        (Nat.card S0 = 2 ^ 5 ∧ ∃ U : Subgroup G, IsMaximalTwoLocal U ∧
          Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  obtain ⟨heven, hcore, _⟩ := simple_nonsolvable_inputs hns
  by_cases hStrong : ∃ M : Subgroup G, IsStronglyEmbedded M
  · obtain ⟨M, hM⟩ := hStrong
    exact Or.inl (isNTwoGroupModel_of_bender (bender_suzuki M hM))
  by_cases hOdd : ∃ U : Subgroup G, IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥
  · exact Or.inr (Or.inr (exists_involution_bad_oddCore hN hOdd))
  have hOddFree : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥ := by
    intro U hU
    by_contra hbad
    exact hOdd ⟨U, hU, hbad⟩
  have hHyp : HypothesisOne G S0 :=
    hypothesis_one_of_nTwo hN heven hcore S0 hStrong hOdd
  have hLocal : ∀ U : Subgroup G, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U :=
    two_local_solvable_characteristicTwo_of_nTwo hN hOdd
  by_cases hMax : ∃ P1 P2 : Subgroup G, P1 ≠ P2 ∧
      IsMaximalTwoLocal P1 ∧ IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup G) ≤ P1 ∧ (S0 : Subgroup G) ≤ P2
  · rcases multiple_maximal_rich_terminal S0 hHyp hLocal hMax with
      hL3 | hSp4 | hG2 | hRich
    · exact Or.inl (model_of_dihedral hns S0 (dihedral_sylow_of_l3Two_type S0 hL3))
    · exact (not_sp4Two_type_of_simple_nonsolvable hns hSp4).elim
    · exact Or.inr (Or.inl ⟨hOddFree, Or.inl hG2⟩)
    · obtain ⟨P1, P2, ctx, hcomm, hlength, hno⟩ := hRich
      exact Or.inr (Or.inl ⟨hOddFree, Or.inr (Or.inl ⟨{
        first := P1
        second := P2
        terminal := ctx
        localStructure := hLocal
        commuting := hcomm
        length_three := hlength
        noTransvections := hno }⟩)⟩)
  have hS0ne : (S0 : Subgroup G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S0 heven.two_dvd
  obtain ⟨M, hM⟩ := exists_uniqueMaximalTwoLocalContaining_of_not_two S0 hS0ne (by
    rintro ⟨M1, M2, hne, ⟨hM1, hS1⟩, ⟨hM2, hS2⟩⟩
    exact hMax ⟨M1, M2, hne, hM1, hM2, hS1, hS2⟩)
  rcases unique_maximal_branch S0 hHyp hLocal M hM with hShape | h32
  · rcases hShape with hdihedral | hsemidihedral
    · exact Or.inl (model_of_dihedral hns S0 hdihedral)
    · exact Or.inr (Or.inl ⟨hOddFree, Or.inr (Or.inr (Or.inl hsemidihedral))⟩)
  · exact Or.inr (Or.inl ⟨hOddFree, Or.inr (Or.inr (Or.inr h32))⟩)

end Stellmacher.Recognition
