module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.Contradiction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer

/-!
# The swapped `L₃(2)` branch

The concrete wreath model computes its cubic two-residual, its three-rank, and
the actual dihedral conjugation image. The marked source assembly constructs
the solvable `H₁` inside the moving component overgroup, uses 13.7.3(9) to
identify its two-residual with `L₁`, derives the genuine `Â₆` model and its
`E₄` automizer, and closes the branch against the literal `D₈` image.

The superscript in `O²(H₁)` denotes the **two-residual**, distinct from
`O₂(H₁)`.

Source: Aschbacher--Smith 13.8.16(1), printed p.952 (PDF p.969), with
standing setup on printed pp.946--947.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.WreathOvergroup
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer.SourceAssembly
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree

variable {G : Type*} [Group G] [Finite G]

/-- The actual `L₃(2)` branch of 13.8.16(1) is impossible.

The inputs are the standing source outputs: the two compatible local model
alternatives, the source factorization, the moving pair `K,K₀`, the universal
solvable-overgroup clause 13.8.13, the theta identity 13.7.3(9), and the
three-rank bound for solvable subgroups of `G₁`. The proof first constructs the
literal solvable `H₁` and its wreath quotient. Its two-residual is the actual
`L₁`; the transported rank calculation gives rank two, so the simple `A₆`
model is excluded and the concrete triple cover is selected. The resulting
`E₄` automizer contradicts the dihedral image supplied by the same wreath
quotient.

The equality involving `closure` is the source's `θ(H ∩ M)` identity. The
ambient actor is `M = N_G(L)`, and all subgroup maps below are literal maps in
`G`.

Source: Aschbacher--Smith, proof of 13.8.16(1), printed p.952 (PDF p.969),
using 13.7.3(9), 13.8.13 and the standing setup on pp.946--947.
-/
theorem exclude_l3_branch
    (L V V₁ H G₁ K K₀ : Subgroup G) (T : Sylow 2 G)
    (hLV : L ≤ normalizer (V : Set G))
    (hmodels : Nonempty (SimplePointModel L V hLV) ∨
      Nonempty (CoverPointModel L V hLV))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV₁V : V₁ ≤ V) (hc : Nat.card V₁ = 2)
    (hfactor : CoverPointModel L V hLV →
      one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (hthree : ∀ J : Subgroup G,
      one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) ≤ J →
      J ≤ G₁ → Group.IsSolvable J → primeRank 3 J ≤ 2)
    (s : SourcePair.Input H (one L (T : Subgroup G) V₁)
      (T : Subgroup G) K K₀)
    (hH : H ≤ G₁)
    (hex : ∀ J : Subgroup G, one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G) ≤ J →
      J ≤ G₁ → Group.IsSolvable J → J ≤ normalizer (L : Set G))
    (htheta : one L (T : Subgroup G) V₁ =
      closure {x : G | x ∈ H ⊓ normalizer (L : Set G) ∧ orderOf x = 3}) :
    False := by
  obtain ⟨H₁, hbase, hHM, hsol, ⟨e⟩, _, hres, _⟩ :=
    exists_source_wreath_overgroup s G₁ (normalizer (L : Set G)) hH hex htheta
  have hH₁G₁ : H₁ ≤ G₁ := hHM.trans inf_le_left |>.trans hH
  have hrankH₁ : primeRank 3 H₁ ≤ 2 :=
    hthree H₁ hbase hH₁G₁ hsol
  have hrank : primeRank 3 (one L (T : Subgroup G) V₁) = 2 :=
    marked_threeRank (one L (T : Subgroup G) V₁) H₁ hres e hrankH₁
  obtain ⟨_, ⟨eE4⟩⟩ :=
    source_tripleCover_and_automizer L V V₁ H G₁ K K₀ T hLV hmodels hTL hTV
      hV₁V hc hrank hfactor s hH hex htheta
  exact no_wreath_residual_under_e4_automizer
    (one L (T : Subgroup G) V₁) H₁ (normalizer (L : Set G))
    (hHM.trans inf_le_right) hres e ⟨eE4⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree

end
