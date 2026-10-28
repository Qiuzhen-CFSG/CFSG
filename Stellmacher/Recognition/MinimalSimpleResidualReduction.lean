module

public import Stellmacher.Recognition.MinimalSimpleReduction
public import Stellmacher.Recognition.NGroupReduction
public import Stellmacher.Recognition.TerminalReduction
public import Stellmacher.Recognition.Sylow32Exclusion
public import Stellmacher.Recognition.TerminalResidualReduction

/-!
# Residual recognition inputs for minimal simple groups

The order-32 maximal C₂ × S₄ configuration is impossible by the proved
affine transfer theorem. Separating the genuine odd-core alternative first
also retains trivial odd cores in every two-local subgroup on the remaining
local branches. These hypotheses are needed by the characteristic-three
recognition results; they cannot be inferred from minimal simplicity alone.

The second reduction retains the original large Section Ten terminal context
instead of replacing it by the weaker twisted-F₄ local type. Its already
recognized alternatives lie in the all-prime N catalogue because minimal
simplicity supplies the all-prime N condition. Excluding the nonminimal
catalogue models and recognizing the remaining branches are subsequent work.

The final reduction also recognizes the semidihedral branch and excludes
the order-64 G₂ case. It retains G₂ with Sylow order 32 and the large terminal
context with the proved Sylow orders 2048 or 4096, alongside the genuine
global odd-core alternative.

Source: Stellmacher Theorem 2 and Section 11; the order-32 transfer exclusion
and retained terminal context are documented in the imported modules.
-/

namespace Stellmacher.Recognition

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact minimal-simple local reduction with the order-32 alternative
excluded and the two-local odd-core hypotheses retained. -/
public theorem minimalSimple_coreFree_local_reduction
    (hG : IsMinimalSimple G) (S : Sylow 2 G) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL2Model n)) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SzModel n)) ∨
    (∃ (K : Type u) (instK : Field K) (_ : Finite K),
      let : Field K := instK
      Odd (Nat.card K) ∧ 3 < Nat.card K ∧
        Nonempty (G ≃* GorensteinWalter.PSL2 K)) ∨
    ((∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) ∧
      (IsOfGTwoTwoDerivedType G ∨ IsOfTwistedF4TwoDerivedType G ∨
        IsSemidihedralGroup S)) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  classical
  let _ := hG.isSimpleGroup
  by_cases hOdd : ∃ U : Subgroup G, IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (exists_involution_bad_oddCore hG.isNTwoGroup hOdd))))
  have hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥ := by
    intro U hU
    by_contra hbad
    exact hOdd ⟨U, hU, hbad⟩
  rcases minimalSimple_local_reduction hG S with
    hPSL | hSz | hOddPSL | hType | hSemi | h32 | hInvolution
  · exact Or.inl hPSL
  · exact Or.inr (Or.inl hSz)
  · exact Or.inr (Or.inr (Or.inl hOddPSL))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hcore, ?_⟩)))
    rcases hType with hGTwo | hTwisted
    · exact Or.inl hGTwo
    · exact Or.inr (Or.inl hTwisted)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcore, Or.inr (Or.inr hSemi)⟩)))
  · obtain ⟨hOrder, P, hP, hModel⟩ := h32
    exact (not_sylow32_maximal_c2s4 hG.not_isSolvable hG.isNTwoGroup
      S hOrder P hP hModel).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr hInvolution)))

/-- Minimal-simple specialization retaining the actual large terminal context.
The N catalogue here is an intermediate recognition interface, not the
minimal-simple classification. -/
public theorem minimalSimple_terminal_reduction
    (hG : IsMinimalSimple G) (S : Sylow 2 G) :
    IsNGroupModel G ∨
    ((∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) ∧
      (IsOfGTwoTwoDerivedType G ∨ Nonempty (LargeTerminalContext S) ∨
        IsSemidihedralGroup S)) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  let _ := hG.isSimpleGroup
  rcases simple_nTwo_terminal_reduction hG.not_isSolvable hG.isNTwoGroup S with
    hModel | ⟨hcore, hGTwo | hLarge | hSemi | h32⟩ | hOdd
  · exact Or.inl (isNGroupModel_of_isNTwoGroupModel hG.isNGroup hModel)
  · exact Or.inr (Or.inl ⟨hcore, Or.inl hGTwo⟩)
  · exact Or.inr (Or.inl ⟨hcore, Or.inr (Or.inl hLarge)⟩)
  · exact Or.inr (Or.inl ⟨hcore, Or.inr (Or.inr hSemi)⟩)
  · obtain ⟨hOrder, P, hP, hModel⟩ := h32
    exact (not_sylow32_maximal_c2s4 hG.not_isSolvable hG.isNTwoGroup
      S hOrder P hP hModel).elim
  · exact Or.inr (Or.inr hOdd)

/-- The refined unconditional minimal-simple reduction after the completed
semidihedral recognition and both transfer exclusions. -/
public theorem minimalSimple_terminal_residual_reduction
    (hG : IsMinimalSimple G) (S : Sylow 2 G) :
    IsNGroupModel G ∨
    ((∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) ∧
      ((IsOfGTwoTwoDerivedType G ∧ Nat.card S = 32) ∨
        (Nonempty (LargeTerminalContext S) ∧
          (Nat.card S = 2048 ∨ Nat.card S = 4096)))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  let _ := hG.isSimpleGroup
  rcases simple_nTwo_terminal_residual_reduction hG.not_isSolvable hG.isNTwoGroup S with
    hModel | hLocal | hOdd
  · exact Or.inl (isNGroupModel_of_isNTwoGroupModel hG.isNGroup hModel)
  · exact Or.inr (Or.inl hLocal)
  · exact Or.inr (Or.inr hOdd)

end Stellmacher.Recognition
