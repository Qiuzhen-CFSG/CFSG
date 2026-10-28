module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedGeneration
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.NaturalDual.Seed
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Action
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Rows

/-!
# The natural-plus-dual exclusion on the original U-action

The source plane supplies a Sylow-fixed generating seed of U. The natural-dual
calculation identifies its centralizer with the centralizer of the full fixed
plane, whose cubic rank is at most one. The image of the original K has cubic
rank at least two and fixes the seed, giving the contradiction.

The original action is constructed internally. Component normality,
K-containment and the S₃-square quotient are explicit earlier source inputs. Component preparation and the small-parabolic
owner supply the latter three; this theorem discharges the module row, without
assuming centralizer alignment, fixed-space containment or seed generation.
It does not exclude the other three module rows or prove all of 15.2.23.

Source: Aschbacher--Smith, 15.2.23(b), printed pp.1116--1117; B.2.14 and B.5.1(6).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01

/-- The natural-dual row is impossible on the literal quotient action on U.
All geometric alignment and generation conditions are proved internally. -/
theorem false_of_naturalDual_source
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    letI := U_elementary d hI hfit hXI
    ∀ (σ : Representation (ZMod 2) (X ⧸ pCore 2 X) (Additive (U X ZS))),
      (∀ (x : X) (u : Additive (U X ZS)),
        ((σ (QuotientGroup.mk' (pCore 2 X) x) u).toMul : G) =
          (x : G) * (u.toMul : G) * (x : G)⁻¹) →
      ∀ n : ℕ, (n = 4 ∨ n = 5) → IsNaturalPlusDual σ n → False := by
  let := U_elementary d hI hfit hXI
  intro σ hσ n hn' hnat
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  exact false_of_naturalDual_generated_on_U d hKX hpair σ hσ hn' hnat S
    (hS.le.trans inf_le_left) (U_seed_module_generates d hI hfit hXI hn σ hσ)

/-- Source row (b) is excluded on the canonical action, with no action equation
or generating-space premise left for the classification consumer. -/
theorem not_naturalDual_canonical
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (n : ℕ) (hdegree : n = 4 ∨ n = 5) :
    letI := U_elementary d hI hfit hXI
    ¬ IsNaturalPlusDual (U_representation d hI hfit hXI hn) n :=
  false_of_naturalDual_source d hI hfit hXI hn hKX hpair
    (U_representation d hI hfit hXI hn) (U_representation_apply d hI hfit hXI hn) n hdegree

/-- Literal classification consumer: only rows (a), (c) and (d) remain.
Recognition of the four rows and exclusion of these three rows remain with
this module family's assembly owner. This is not the binary-branch exclusion. -/
theorem remaining_rows_of_source
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    ModuleRow σ →
      (∃ n r : ℕ, (n = 4 ∨ n = 5) ∧ 0 < r ∧ r ≤ n - 1 ∧
        Nonempty (ActionEquiv σ (repeated (linearNatural BinaryField.two n) r))) ∨
      (∃ C : Subrepresentation σ, C.toSubmodule = fixedSpace σ ⊤ ∧
        Nonempty (ActionEquiv C.quotientRepresentation (alternatingNatural 8))) ∨
      (∃ r : ℕ, (r = 2 ∨ r = 3) ∧ IsIrreducible σ ∧
        Module.finrank (ZMod 2) (Additive (U X ZS)) = 10 ∧
        Nonempty (ActionEquiv σ (Representation.SL5TenDimensional.exteriorAction r))) := by
  let := U_elementary d hI hfit hXI
  dsimp only
  intro hrow
  cases hrow with
  | repeatedNatural n r hd hp hb e => exact Or.inl ⟨n,r,hd,hp,hb,⟨e⟩⟩
  | naturalDual n hd hnat =>
    exact (not_naturalDual_canonical d hI hfit hXI hn hKX hpair n hd hnat).elim
  | orthogonalSix C hc e => exact Or.inr (Or.inl ⟨C,hc,⟨e⟩⟩)
  | exteriorFive r hd hi hf e => exact Or.inr (Or.inr ⟨r,hd,hi,hf,⟨e⟩⟩)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
