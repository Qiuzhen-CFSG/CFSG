module
public import Theory.Representation.SL2.OffenderFieldDegree
public import Theory.Representation.BinaryOffender.QuadraticFixedDimension
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.Representation.SpecialLinearNatural

/-!
# Quadratic natural extensions at every binary field degree

Two nontrivial sections of an SL₂(2ⁿ)-module each force every involution
to move at least n dimensions. In dimension at most 4n, a common fixed
space of dimension 2n is consequently the full fixed space of every
nonidentity Sylow element. Each such involution fixes its displacement,
so the whole Sylow acts quadratically. In particular this holds for a
natural submodule and natural quotient without splitting the extension.

Source: Niles, *Pushing-up in finite groups* (1979), the characteristic-two
case of Lemma 3.4, pp.37--39. The literal group-section application is in
`Theory.Representation.SL2.NaturalExtensionSection`.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped MatrixGroups
namespace Representation.SL2
variable {F Y : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]

/-- Two nontrivial sections and a half-dimensional common fixed space force
quadratic action of a full binary Sylow subgroup. -/
theorem sylow_quadratic_of_two_nontrivial_sections
    (ρ : Representation (ZMod 2) SL(2,F) Y) (X : Subrepresentation ρ)
    (hX : ∃ g, X.toRepresentation g ≠ 1)
    (hQ : ∃ g, X.quotientRepresentation g ≠ 1)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hdim : Module.finrank (ZMod 2) Y ≤ 4*n)
    (P : Sylow 2 SL(2,F))
    (hfixed : 2*n ≤ Module.finrank (ZMod 2) (fixedSpace ρ P)) :
    IsQuadratic ρ P := by
  have hsq (g : SL(2,F)) (hg : g ∈ P) : g^2 = 1 :=
    congrArg Subtype.val (Matrix.SpecialLinearGroup.twoSubgroup_pow_two
      (P : Subgroup SL(2,F)) P.isPGroup' ⟨g,hg⟩)
  apply isQuadratic_of_fixedDimension_bound ρ P hsq (2*n) ?_ hfixed
  intro g hg hne
  have hx := involution_fixedCodim_lower X.toRepresentation hX hn hF g hne (hsq g hg)
  have hq := involution_fixedCodim_lower X.quotientRepresentation hQ hn hF g hne (hsq g hg)
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ X (zpowers g)
  have htotal := fixedCodim_add_finrank ρ (zpowers g)
  omega

local instance naturalExtensionAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

omit [Finite F] in
private theorem nontrivial_of_natural_coordinates
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g w, E (σ g w) = Matrix.mulVec g.val (E w)) :
    ∃ g, σ g ≠ 1 := by
  let g : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  refine ⟨g,?_⟩
  intro hh
  have he := hE g (E.symm ![0,1])
  rw [hh,Module.End.one_apply,E.apply_symm_apply] at he
  have he0 := congrFun he 0
  simp [g,Matrix.mulVec] at he0

/-- Natural-by-natural extensions at the unchanged binary field degree. -/
theorem sylow_quadratic_of_natural_sections
    (ρ : Representation (ZMod 2) SL(2,F) Y) (X : Subrepresentation ρ)
    (eX : X.toSubmodule ≃ₗ[ZMod 2] (Fin 2 → F))
    (eQ : (Y ⧸ X.toSubmodule) ≃ₗ[ZMod 2] (Fin 2 → F))
    (heX : ∀ g x, eX (X.toRepresentation g x) = Matrix.mulVec g.val (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) = Matrix.mulVec g.val (eQ x))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (P : Sylow 2 SL(2,F))
    (hfixed : 2*n ≤ Module.finrank (ZMod 2) (fixedSpace ρ P)) :
    IsQuadratic ρ P := by
  have hdim : Module.finrank (ZMod 2) (Fin 2 → F) = 2*n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Fin 2 → F)
    rw [Nat.card_fun,Nat.card_fin,hF,Nat.card_zmod,←pow_mul] at hc
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc
    omega
  have hx := eX.finrank_eq.trans hdim
  have hq := eQ.finrank_eq.trans hdim
  have hy := X.toSubmodule.finrank_quotient_add_finrank
  exact sylow_quadratic_of_two_nontrivial_sections ρ X
    (nontrivial_of_natural_coordinates _ eX heX)
    (nontrivial_of_natural_coordinates _ eQ heQ) hn hF (by omega) P hfixed
end Representation.SL2
