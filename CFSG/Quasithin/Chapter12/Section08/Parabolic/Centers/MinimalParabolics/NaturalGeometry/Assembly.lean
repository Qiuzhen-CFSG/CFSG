module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.MarkedGeneration
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.CoordinateConjugators
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics

/-!
# Natural geometry for the minimal-parabolic center induction

The full action on the original elementary abelian seed constructs a single
coordinate marking preserving every flag member and the original Sylow image.
In those coordinates, the proved binary flag generation and successive residual
conjugators supply both geometric premises of the center induction. The latter
lift through the actual two-core action kernel, with right conjugation and the
embedded O² residuals unchanged.

The final theorem applies `center_centralized_of_ordered_generation`, discharging
both its geometric premises. The terminal residual equality is also a consequence,
using two-perfectness of L and its normalization by T. No marking, residual bound,
generation statement or terminal equality is an input.

This covers the source dimensions three through five; the existing rank-two
route is separate because 12.8.3(1) only supplies the full LT action there.
The preceding-source action, kernel, residual and center calculations remain
explicit for the parent `qt-12-08-parabolic-centers-induction` assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 12.8.1 and Lemma 12.8.3(1), printed pp.849–850, and the proof of
Lemma 12.8.10(5), printed p.854 (PDF p.871), `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  [IsElementaryAbelian 2 V] {n : ℕ}

/-- The genuine full binary action and its two-core kernel imply both ambient
geometric premises of the center induction, using one common flag marking. -/
theorem ordered_generation_of_full_binary_action
    (F : InvariantFlag T V n) (hn : 3 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.orderedParabolic L j) =
      L ⊔ (T : Subgroup G) ∧
    ∀ j, 1 ≤ j → j + 1 < n →
      ∃ k ∈ F.orderedParabolic L (j + 1), F.initialResiduals L (j + 1) =
        F.initialResiduals L j ⊔ conjugate (F.initialResiduals L j) k := by
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨β, e, b, _, _, _, hmark⟩ := F.exists_marked_naturalFlag L hL hfull
    refine ⟨F.orderedParabolic_generation_of_full_binary_action (by omega) L hL hfull, ?_⟩
    intro j hj hjn
    exact F.initialResiduals_successor_of_coordinates e b hmark L hL hfull hcore j hj hjn

/-- Ordinary generation from the full action already implies the terminal
residual equality. This step needs no additional kernel or residual premise. -/
theorem initialResiduals_terminal_of_full_binary_action
    (F : InvariantFlag T V n) (hn : 3 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hperfect : IsPPerfect 2 L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G)) :
    F.initialResiduals L (n - 1) = L := by
  cases n with
  | zero => omega
  | succ m =>
    exact F.initialResiduals_terminal_of_parabolic_generation (by omega) L hperfect hTL
      (F.orderedParabolic_generation_of_full_binary_action (by omega) L hL hfull)

/-- Apply the corrected center induction with both natural geometry obligations
proved. The remaining premises are the preceding-source calculations retained
by the parent assembly, including the distinct local and natural action kernels. -/
theorem center_centralized_of_full_binary_action
    (F : InvariantFlag T V n) (hn : 3 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hUT : F.U ≤ T) (hI : F.Gi 2 ≤ normalizer (F.I₂ L : Set G))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hgen : F.I₂ L = F.U ⊔ conjugate F.U g)
    (e : (F.I₂ L ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3))
    (hfix : ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W)
    (hhat : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g)
    (htilde : F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU)
    (hcontained : conjugate F.ZU g ≤ F.U)
    (hresidual : (pResidual 2 (F.P L)).map (F.P L).subtype =
      (pResidual 2 (F.I₂ L)).map (F.I₂ L).subtype)
    (hperfect : IsPPerfect 2 L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hnaturalCore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  obtain ⟨hparabolics, hconjugator⟩ :=
    F.ordered_generation_of_full_binary_action hn L hL hfull hnaturalCore
  exact F.center_centralized_of_ordered_generation (by omega) L hL hcenter hcomm hUT hI
    g hgP hgH hgen e hfix hhat htilde hcore hZW hcontained hresidual hperfect hTL
    hparabolics hconjugator

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
