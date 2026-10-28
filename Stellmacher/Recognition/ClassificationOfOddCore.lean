module

public import Stellmacher.Recognition.TerminalResidualReduction
public import Stellmacher.Recognition.GTwoRecognition
public import Stellmacher.Recognition.LargeTerminalSylowOrder
public import Stellmacher.Recognition.LargeTerminalParrott
public import Stellmacher.Recognition.Parrott.Recognition
public import Stellmacher.Recognition.NGroupReduction

/-!
# Explicit recognition from the odd-core branch

The terminal residual reduction leaves one genuine global input: recognition of
an involution centralizer with nontrivial two-core.  Once that input is supplied,
the order-32 G₂ branch is recognized by Fong and the large terminal branch by
Parrott.  This module keeps that input explicit and assembles the N₂ model;
the all-prime N model is obtained by the established even-unitary exclusion.

Source: Stellmacher Theorem 2 and Section 11, Fong (1967), and Parrott (1972).
-/

namespace Stellmacher.Recognition
universe u

/-- Assemble the simple N₂ model from the explicit odd-core recognition input.
The supplied Sylow subgroup is retained so the terminal reduction can pass its
local data to the G₂ and Parrott recognition theorems. -/
public theorem isNTwoGroupModel_of_oddCore
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hOdd : ∀ t : G, orderOf t = 2 →
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ →
      IsNTwoGroupModel G) :
    IsNTwoGroupModel G := by
  rcases simple_nTwo_terminal_residual_reduction hns hN S with
    hModel | ⟨hcore, hlocal⟩ | ⟨t, ht, hcore⟩
  · exact hModel
  · rcases hlocal with hGTwo | hLarge
    · exact Or.inl (.unitaryThree
        (by
          obtain ⟨e⟩ := nonempty_equiv_psu3_of_gTwo_card32
            hns hN S hcore hGTwo.1 hGTwo.2
          refine ⟨3, 1, by decide, by decide, ?_, ?_⟩
          · norm_num
          · exact ⟨e⟩))
    · obtain ⟨hctx, _hcard⟩ := hLarge
      obtain ⟨ctx⟩ := hctx
      have h2048 : Nat.card S = 2048 :=
        simple_nTwo_large_terminal_branch_sylow_card hns hN S hcore ⟨ctx⟩
      obtain ⟨z, _, hz⟩ := ctx.parrott_hypotheses_of_sylow_card h2048
      obtain ⟨e⟩ := nonempty_equiv_tits_of_parrott hns hN hz
      exact Or.inl (.tits e)
  · exact hOdd t ht hcore

/-- The same assembly while choosing the Sylow subgroup internally. -/
public theorem isNTwoGroupModel_of_oddCore'
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (hOdd : ∀ t : G, orderOf t = 2 →
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ →
      IsNTwoGroupModel G) :
    IsNTwoGroupModel G := by
  let S : Sylow 2 G := default
  exact isNTwoGroupModel_of_oddCore hns hN S hOdd

/-- Assemble the all-prime N model from the explicit odd-core recognition
input, retaining the supplied Sylow for the N₂ reduction. -/
public theorem isNGroupModel_of_oddCore
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNGroup G) (S : Sylow 2 G)
    (hOdd : ∀ t : G, orderOf t = 2 →
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ →
      IsNTwoGroupModel G) :
    IsNGroupModel G :=
  isNGroupModel_of_isNTwoGroupModel hN
    (isNTwoGroupModel_of_oddCore hns (isNTwoGroup_of_isNGroup hN) S hOdd)

/-- The all-prime N assembly while choosing the Sylow subgroup internally. -/
public theorem isNGroupModel_of_oddCore'
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNGroup G)
    (hOdd : ∀ t : G, orderOf t = 2 →
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ →
      IsNTwoGroupModel G) :
    IsNGroupModel G := by
  let S : Sylow 2 G := default
  exact isNGroupModel_of_oddCore hns hN S hOdd

end Stellmacher.Recognition
