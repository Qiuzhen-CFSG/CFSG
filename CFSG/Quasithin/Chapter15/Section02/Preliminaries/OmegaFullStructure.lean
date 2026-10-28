module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaFullNoncentral
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaCubicSylow

/-!
# The full-module Omega residual alternatives

This applies the original intersection-core noncentrality proof to the
same prepared full local module used by the Case II residual. The cubic
branch combines its kernel, inversion and Sylow-three product proofs;
the order-nine branch supplies uniqueness of the maximal two-local
overgroup of YT. No additional noncentrality premise remains here.

The proper moved-module core argument and the order-nine central-extension
alternatives remain separate source obligations.
Source: Aschbacher--Smith, 14.1.17 and 15.2.3, printed pp.980,1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original full Omega row, with noncentrality and the cubic Sylow
structure supplied by their source proofs. -/
theorem source_omega_full_residual_alternatives
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} [IsElementaryAbelian 2 (localModule T M)]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M (localModule T M))
    (ho : SourceCases.Omega (imageRepresentation M (localModule T M) hV.normalized)) :
    let V := localModule T M
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let f := (actionHom M V hV.normalized).rangeRestrict
    let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
    (Y.subgroupOf M).map f ≠ ⊥ ∧
      ⁅(Y.subgroupOf M).map f, R⁆ = (Y.subgroupOf M).map f ∧
      ((Nat.card ((Y.subgroupOf M).map f) = 3 ∧
          Y ⊓ centralizer (V : Set G) = Y.pCoreIn 2 ∧
          Nat.card ((Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))) = 3 ∧
          Nat.card R = 2 ∧
          (∀ r ∈ R, r ≠ 1 → ∀ y ∈ (Y.subgroupOf M).map f,
            r * y * r⁻¹ = y⁻¹) ∧
          primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1 ∧
          ∀ P : Sylow 3 M, ∃ n : ℕ, 1 ≤ n ∧ Nonempty
            (P ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n)))) ∨
        (Nat.card ((Y.subgroupOf M).map f) = 9 ∧
          maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) = {M})) := by
  have hRc := source_omega_full_core_noncentral hG T hempty hM hu hmany ho
  have hs := source_omega_residual_structure hG T hempty hM hJ hu hV ho hRc
  refine ⟨hs.1,hs.2.1,?_⟩
  rcases hs.2.2 with hc | hn
  · have hp := source_omega_cubic_sylow_structure hG T hM.1 hu hV ho hc.1
    exact Or.inl ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,hp.1,hp.2⟩
  · exact Or.inr hn

end CFSG.Quasithin.Chapter15.Section02
