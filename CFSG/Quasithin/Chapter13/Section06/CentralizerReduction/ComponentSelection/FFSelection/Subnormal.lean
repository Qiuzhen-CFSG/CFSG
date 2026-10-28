module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification

/-!
# The conditional FF subnormal obstruction, 13.6.10

The actual A₅ marking and vanishing star two-core reduce a hypothetical
subnormal L_v* to order three. The faithful offender restriction satisfies
B.5.3 with its actual SQTK cover, and the full B.5.6 implication is applied
without replacing any group or module alternative.

The complete alternatives give moved-space rank two and a conjugacy orbit
of size at most two. The actual normalizing Sylow forces normality of L_v*;
the moved-space order then gives [U_v,L_v]=[V,L_v]. Adjoining the central
line reconstructs the forbidden relative normality of V_v in G_v.

The explicit earlier inputs are the marked module and local Sylow data on
p.926, the elementary U_v and vanishing star two-core preceding 13.6.9,
the SQTK property of G_v, and the nonnormality clause of 13.6.8. The universal
B.5.6 input remains conditional. No order, moved-space, orbit or branch
conclusion from the proof of 13.6.10 is assumed. The full commutator premise
and the actual A₅ marking already imply a nontrivial offender actor, so a
separate use of 13.6.9 is unnecessary.

The first export accepts the requested existing classification interface.
The source-classification export uses its corrected B.4.2(8) projective-line
variant, as required by `docs/quasithin-proof-basis.md`. Both retain the
printed outer alternative; neither uses its disputed fixed-space splitting.
These theorems do not assert B.5.6 or discharge its universal input. The
parent component-selection task owns those earlier-source premises and the
subsequent solvable exclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed p.928, with the local module setup on p.926.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "Lstar" => starImage z₀ v₀ (Lv L v₀)

/-- Conditional 13.6.10 through the existing full classification API.
`hcard`, `hsplit` and `hsmall` are the local module calculations on p.926;
`hcore` is the B.2.14 consequence before 13.6.9, and `hnormal` is 13.6.8.
The order-three reduction and both B.5.6 bounds are derived internally. -/
theorem marked_not_subnormal_of_classification (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L v₀ ≤ normalizer (V : Set G))
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hsplit : Vv L z₀ v₀ = zpowers v₀ ⊔ ⁅V, Lv L v₀⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L v₀⁆ : Subgroup G) = 4)
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hnormal : ¬ ((Vv L z₀ v₀).subgroupOf (Gv v₀)).Normal)
    {𝒦 : GroupClass.{u}} (classification : GeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀))
    (hfull : Lstar = ⁅Lstar, starImage z₀ v₀
      (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆) :
    ¬ (Lstar).IsSubnormal := by
  intro hs
  obtain ⟨hdim, horbit⟩ := Classification.marked_bounds_of_classification s T S hS hT
    hcore hcard hfull hs classification hSQ
  exact contradiction_of_linear_classification_bounds L V T z₀ v₀
    (A5Module.markedZ_mem_Gv s) S hS hT hV hL hsplit hsmall hdim horbit hnormal

/-- Conditional source 13.6.10 with the corrected projective-line contract.
All the local premises are the same earlier-source data as above. The full
universal classification supplies actual group and module alternatives;
no selected component, branch impossibility or classification bound is input. -/
theorem marked_not_subnormal_of_source_classification (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hV : IsPGroup 2 V) (hL : Lv L v₀ ≤ normalizer (V : Set G))
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hsplit : Vv L z₀ v₀ = zpowers v₀ ⊔ ⁅V, Lv L v₀⁆)
    (hsmall : Nat.card ↥(⁅V, Lv L v₀⁆ : Subgroup G) = 4)
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hnormal : ¬ ((Vv L z₀ v₀).subgroupOf (Gv v₀)).Normal)
    {𝒦 : GroupClass.{u}} (classification : ProjectiveLine.GeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀))
    (hfull : Lstar = ⁅Lstar, starImage z₀ v₀
      (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆) :
    ¬ (Lstar).IsSubnormal := by
  intro hs
  obtain ⟨hdim, horbit⟩ := Classification.marked_bounds_of_source_classification s T S hS hT
    hcore hcard hfull hs classification hSQ
  exact contradiction_of_linear_classification_bounds L V T z₀ v₀
    (A5Module.markedZ_mem_Gv s) S hS hT hV hL hsplit hsmall hdim horbit hnormal

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal
