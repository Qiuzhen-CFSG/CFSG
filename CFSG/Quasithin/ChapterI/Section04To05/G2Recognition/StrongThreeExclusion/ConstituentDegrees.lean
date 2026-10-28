module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.ThreeRegular
public import Theory.Character.Multiplicity

/-!
# Degrees of the two constituents in each induced identity

Ordinary orthogonality gives the coefficients of the two distinct
nonprincipal constituents. Their nonzero coefficients exclude defect zero
at three through the original singular support.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour LocalCharacters
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem scalarProduct_irreducible_self {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) : scalarProduct G χ χ = 1 := by
  obtain ⟨n,ρ,hρ,rfl⟩ := hχ
  simpa only [scalarProduct, characterProduct,
    Representation.representation_character_inv_eq_star_character] using
    irreducibleCharacter_self (show IsIrreducibleCharacter ρ.character from ⟨n,ρ,hρ,rfl⟩)

private theorem scalarProduct_irreducible_distinct {χ ψ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) (hψ : IsIrreducibleCharacter ψ) (hne : χ ≠ ψ) :
    scalarProduct G χ ψ = 0 := by
  have hh := irreducibleCharacters_orthogonal hχ hψ hne
  obtain ⟨n,ρ,_,rfl⟩ := hψ
  simpa only [scalarProduct, characterProduct,
    Representation.representation_character_inv_eq_star_character] using hh

/-- The actual two nonprincipal constituents in an induced-row identity
have degrees not divisible by the Sylow order nine. -/
theorem original_constituent_degrees_not_nine
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) (i : Fin 4)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (ψ μ : ClassFunction G) (hψ : IsIrreducibleCharacter ψ)
    (hμ : IsIrreducibleCharacter μ) (hne : ψ ≠ μ) (hψ1 : ψ ≠ 1) (hμ1 : μ ≠ 1)
    (hid : inducedClassFunction c.H (localAlpha c i) = 1 + (ε : ℂ) • (ψ - μ)) :
    ¬ 9 ∣ hψ.degree ∧ ¬ 9 ∣ hμ.degree := by
  have h1ψ : scalarProduct G 1 ψ = 0 := by
    rw [←scalarProduct_conj, hψ.scalarProduct_principal_eq_zero hψ1, star_zero]
  have h1μ : scalarProduct G 1 μ = 0 := by
    rw [←scalarProduct_conj, hμ.scalarProduct_principal_eq_zero hμ1, star_zero]
  have hψψ := scalarProduct_irreducible_self hψ
  have hμμ := scalarProduct_irreducible_self hμ
  have hψμ := scalarProduct_irreducible_distinct hψ hμ hne
  have hμψ := scalarProduct_irreducible_distinct hμ hψ hne.symm
  have he0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  constructor
  · apply not_nine_dvd_degree_of_induced_pairing c hsmall i hψ
    rw [hid, scalarProduct_add_left, scalarProduct_smul_left, scalarProduct_sub_left,
      h1ψ, hψψ, hμψ]
    simpa using he0
  · apply not_nine_dvd_degree_of_induced_pairing c hsmall i hμ
    rw [hid, scalarProduct_add_left, scalarProduct_smul_left, scalarProduct_sub_left,
      h1μ, hψμ, hμμ]
    simpa using he0

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
