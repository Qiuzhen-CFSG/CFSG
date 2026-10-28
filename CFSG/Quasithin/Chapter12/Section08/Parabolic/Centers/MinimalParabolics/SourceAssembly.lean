module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Intersections
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.NaturalGeometry.Assembly
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration

/-!
# The minimal-parabolic center induction from preceding source results

This assembles both assertions of Lemma 12.8.10(5), with Z(W)=V₂Z(U)
and the precise earlier 12.8.3–9 action and center inputs still explicit.
The binary generation theorem constructs the original I₂, its relative
G₂-normality, its S₃ quotient and the parabolic core cover. That cover gives
the equality of the embedded two-residuals O²(P)=O²(I₂).

The intersection calculation constructs the internal product Z(U)=Z(I₂)×V₁,
including its multiplication map. In rank two, P=LT and the residual equality
already give [L,Z(I₂)]=1. In higher rank the genuine full L-action constructs
the ordered parabolics and their successive residual conjugators, then the
corrected center induction reaches L. Only the new residual at each step
acts trivially on Z(U); the accumulated subgroup centralizes Z(I₂).

No generation, conjugator, terminal residual equality, splitting or
centralization premise remains. The full L-action is required only for n≥3;
the full LT-action applies also to the rank-two source alternative. The parent
Centers assembly discharges Z(W)=V₂Z(U), and the parent Parabolic assembly
discharges the earlier source statements. Thus this is the completed
conditional induction, not a claim to the full Lemma 12.8.10.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 12.8.1, Lemmas 12.8.3–9 and Lemma 12.8.10(5),
printed pp.849–854, especially p.854 (PDF p.871), `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  [IsElementaryAbelian 2 V] {n : ℕ}

/-- Both assertions of 12.8.10(5), conditional only on the earlier source
calculations and the separately produced Z(W) identity. In particular,
neither the internal product nor either induction-generation premise is assumed.
The fixed-space and kernel inputs are exactly 12.8.9(3,5) and 12.8.4(4). -/
theorem center_product_and_centralization_of_binary_source
    (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hperfect : IsPPerfect 2 L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfullLT : Function.Surjective (F.binarySeedAction L hL))
    (hfullL : 3 ≤ n → ∀ a : MulAut V,
      ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hnaturalCore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcenter : V ⊓ F.ZU = F.Vi 1) (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hfix : ∀ a ∈ F.U, a ∉ F.W → ∀ z ∈ (F.I₂ L).pCoreIn 2,
      ⁅z, a⁆ ∈ F.E g → z ∈ F.W)
    (hhat : F.X g ⊓ F.uhatAction.ker.map F.H.subtype = F.E g)
    (htilde : F.X g ⊓ (F.localTildeAction F.H le_rfl).ker.map F.H.subtype = F.E g)
    (hcore : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H)
    (hZW : centerIn F.W = F.Vi 2 ⊔ F.ZU)
    (hcontained : conjugate F.ZU g ≤ F.U) :
    (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
      ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
        ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
    ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  obtain ⟨e, _, hgen, _, hIG, hIN, _, _, hfactor, _⟩ :=
    F.binary_generation hn L hL hfullLT hnaturalCore hcomm hsquare hspan hne g hgP hgH
  have hUT := F.binary_U_le_sylow (by omega) hsquare
  have hI := (normal_subgroupOf_iff_le_normalizer hIG).mp hIN
  have hcalc := F.center_and_kernel_calculations_of_centralizer_center hn L hL
    hcenter hcomm hUT hI g hgP hgH hgen e hfix hhat htilde hcore hZW
  refine ⟨hcalc.2.2.2.2.1 hcontained, ?_⟩
  have hresidual := (F.binary_residual_supplement (by omega) L hsquare hfactor).2.symm
  by_cases hnTwo : n = 2
  · subst n
    exact F.center_centralized_rankTwo L hperfect hTL hresidual
  · exact F.center_centralized_of_full_binary_action (by omega) L hL hcenter hcomm
      hUT hI g hgP hgH hgen e hfix hhat htilde hcore hZW hcontained hresidual
      hperfect hTL (hfullL (by omega)) hnaturalCore

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
