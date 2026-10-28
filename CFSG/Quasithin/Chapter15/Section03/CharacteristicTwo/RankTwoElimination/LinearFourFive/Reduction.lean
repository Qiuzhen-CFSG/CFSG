module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.Basic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.Inheritance
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# Passing to the component and the fixed Sylow subgroup

In the binary rank-two cases, 15.3.17 gives `Y₊ ≤ L = θ(I)`.
The subgroup `LS` is again outside `M`, contains the old two-core, has
Sylow two-subgroup `S`, and inherits characteristic two. Solvable subgroup
control restricts to it. Since `S` normalizes `L` and centralizes `Z`, its
local span is exactly `⟨Z^L⟩`.

These are transport results for the first paragraph of 15.3.24. The
component `L`, its two-core quotient, and `W_L = ⟨V^L⟩` are unchanged.
No assertion is made that the old star quotient, whose module is `U_I`,
is unchanged, or that a component witness for its Thompson subgroup can
be reused without proof. The later module arguments use the displayed
subgroups directly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

variable {G : Type*} [Group G] (d : LocalData G)

/-- Solvable invariant subgroup control restricts to an actual subgroup of `I`.
The intersection on the right is recomputed in that subgroup. -/
theorem solvableInvariantControl_restrict {I K : Subgroup G} (hKI : K ≤ I)
    (h : SolvableInvariantControl d I) : SolvableInvariantControl d K := by
  intro X hX hsol hnorm
  exact le_inf ((h X (hX.trans hKI) hsol hnorm).trans inf_le_left) hX

/-- The original two-core survives in every intermediate overgroup of `S`. -/
theorem intermediate_core_ne_bot {I K : Subgroup G} (hI : I ∈ d.Hplus)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hKI : K ≤ I) (hSK : d.S ≤ K) :
    K.pCoreIn 2 ≠ ⊥ := by
  intro hbot
  exact hI.1.1 (le_bot_iff.mp
    ((twoCoreIn_le_of_sylow_overgroup hS hKI hSK).trans_eq hbot))

/-- A parabolic candidate containing `Y₊S` has all local-family and
characteristic-two properties required to invoke earlier exclusions.
Its construction and its failure of containment in `M` remain separate. -/
theorem intermediate_outside [Finite G] {I K : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) (hKI : K ≤ I)
    (hYK : d.Yplus ⊔ d.S ≤ K) (hKM : ¬ K ≤ d.M) :
    K ∈ d.Hplus ∧ Chapter1.IsSylowIn 2 d.S K ∧ HasCharacteristicTwo K := by
  have hSK := le_sup_right.trans hYK
  exact ⟨d.mem_Hplus_of_intermediate hI hS hKI hYK hKM,
    hS.restrict hSK hKI, characteristicTwo_of_sylow_overgroup hS hKI hSK hf⟩

/-- The source equality `L = θ(I)` gives relative normalization by `I`. -/
theorem normalizes_of_eq_theta {I L : Subgroup G} (hL : L = theta I) :
    I ≤ normalizer (L : Set G) := by
  rw [hL]
  exact I.le_normalizer.trans (normalizer_le_normalizer_theta I)

/-- The intersection `S_L = S ∩ L` is Sylow in the literal component.
The normality used here is relative to `I`. -/
theorem sylow_intersection_of_eq_theta [Finite G] {I L : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 d.S I) (hL : L = theta I) :
    Chapter1.IsSylowIn 2 (d.S ⊓ L) L := by
  have hLI : L ≤ I := hL ▸ theta_le I
  have hN : (L.subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizes_of_eq_theta hL)
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hLI hN.isSubnormal

private theorem normalizes_conjugateSpan {A Z L : Subgroup G}
    (hL : A ≤ normalizer (L : Set G))
    (hZ : A ≤ normalizer (Z : Set G)) :
    A ≤ normalizer (localSpan Z L : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨l, hl, z, hz, rfl⟩
  refine subset_closure ⟨a * l * a⁻¹, (hL ha l).mp hl,
    a * z * a⁻¹, (hZ ha z).mp hz, ?_⟩
  group

/-- The Sylow factor creates no further conjugates of `Z` once it
normalizes `L`. This identifies the new local module, not the old `U_I`. -/
theorem localSpan_join_sylow {L : Subgroup G}
    (hSL : d.S ≤ normalizer (L : Set G)) :
    d.UI (L ⊔ d.S) = localSpan d.Z L := by
  apply le_antisymm
  · apply conjugateSpanBy_le (le_conjugateSpanBy _ _)
    refine sup_le (le_normalizer_conjugateSpanBy _ _) ?_
    apply normalizes_conjugateSpan hSL
    have hSZ : d.S ≤ centralizer (d.Z : Set G) :=
      inf_le_left.trans (le_centralizer_iff.mp
        (centralInvolutions_le_centralizer_sylow d.T))
    exact hSZ.trans (Subgroup.centralizer_le_normalizer _)
  · exact conjugateSpanBy_mono le_rfl le_sup_left

/-- All overgroup hypotheses used after the source replacement `I := LS`
are proved from 15.3.11(1), 15.3.15(3), and the containment in 15.3.17(2).
The original component supplies `L ≤ I` and `L ≰ M`. -/
theorem component_join_reduction [Finite G] {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hS : Chapter1.IsSylowIn 2 d.S I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (hYL : d.Yplus ≤ c.L) (hθ : c.L = theta I)
    (hsol : SolvableInvariantControl d I) :
    c.L ⊔ d.S ≤ I ∧ (c.L ⊔ d.S) ∈ d.Hplus ∧
      Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.S) ∧
      HasCharacteristicTwo (c.L ⊔ d.S) ∧
      SolvableInvariantControl d (c.L ⊔ d.S) ∧
      I.pCoreIn 2 ≤ (c.L ⊔ d.S).pCoreIn 2 ∧
      (c.L.subgroupOf (c.L ⊔ d.S)).Normal ∧
      d.UI (c.L ⊔ d.S) = localSpan d.Z c.L := by
  have hSI : d.S ≤ I := le_sup_right.trans hI.1.2
  have hKI : c.L ⊔ d.S ≤ I := sup_le (component_le c) hSI
  have hKM : ¬ c.L ⊔ d.S ≤ d.M := fun h => c.outside (le_sup_left.trans h)
  have hYK : d.Yplus ⊔ d.S ≤ c.L ⊔ d.S := sup_le_sup_right hYL _
  obtain ⟨hK, hSK, hfK⟩ := intermediate_outside d hI hS hf hKI hYK hKM
  have hNI := normalizes_of_eq_theta hθ
  exact ⟨hKI, hK, hSK, hfK, solvableInvariantControl_restrict d hKI hsol,
    twoCoreIn_le_of_sylow_overgroup hS hKI le_sup_right,
    normal_subgroupOf_of_le_normalizer (hKI.trans hNI),
    localSpan_join_sylow d (hSI.trans hNI)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

end
