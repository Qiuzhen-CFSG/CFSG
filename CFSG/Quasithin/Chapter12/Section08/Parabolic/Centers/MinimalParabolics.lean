module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.Intersections
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.Residuals
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Centers.MinimalParabolics.Step

/-!
# Conditional assembly of the center induction

The center/intersection theorem supplies the internal splitting from the
literal preceding 12.8.3–9 inputs and the explicit Z(W) identity. The first
residual centralizes Z(I₂) by 12.8.9(1). Each subsequent residual uses the
corrected index-two action argument, and ordinary induction reaches L.
The n=2 case consists of the first residual and uses the same convention.

The terminal residual equality is derived from ordinary flag-stabilizer
generation. The reusable induction below keeps that generation and the
successive conjugating elements explicit. `NaturalGeometry.Assembly`
discharges both from the genuine action; `MinimalParabolics.SourceAssembly`
combines it with rank two and derives the residual identity from 12.8.9(1).
The parent Centers assembly discharges Z(W)=V₂Z(U), and the Parabolic
assembly retains the preceding-source inputs.

Source: Aschbacher–Smith, Lemma 12.8.10(5), printed p.854 (PDF p.871).
-/

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Conditional assembly of the corrected induction. The two natural-action
generation statements stay explicit here and are discharged in `SourceAssembly`.
The internal splitting is derived from the earlier center calculations. -/
public theorem center_centralized_of_ordered_generation
    (F : InvariantFlag T V n) [Finite G] [IsMulCommutative V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
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
    (hparabolics : (⨆ j : ℕ, ⨆ (_ : 1 ≤ j ∧ j < n), F.orderedParabolic L j) =
      L ⊔ (T : Subgroup G))
    (hconjugator : ∀ j, 1 ≤ j → j + 1 < n →
      ∃ k ∈ F.orderedParabolic L (j + 1),
        F.initialResiduals L (j + 1) =
          F.initialResiduals L j ⊔ conjugate (F.initialResiduals L j) k) :
    ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  have hterminal := F.initialResiduals_terminal_of_parabolic_generation hn L hperfect hTL hparabolics
  have hcalc := F.center_and_kernel_calculations_of_centralizer_center hn L hL
    hcenter hcomm hUT hI g hgP hgH hgen e hfix hhat htilde hcore hZW
  obtain ⟨hsplit, hdisjoint, _⟩ := hcalc.2.2.2.2.1 hcontained
  have hbase : F.initialResiduals L 1 ≤ centralizer (centerIn (F.I₂ L) : Set G) := by
    rw [F.initialResiduals_one, orderedResidual, F.orderedParabolic_one, hresidual]
    apply (map_subtype_le _).trans
    apply le_centralizer_iff.mpr
    rintro x ⟨z, hz, rfl⟩ a ha
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
  have hall : ∀ m, 1 ≤ m → m < n →
      F.initialResiduals L m ≤ centralizer (centerIn (F.I₂ L) : Set G) := by
    intro m
    induction m with
    | zero => omega
    | succ j ih =>
      intro hj hjn
      by_cases hjzero : j = 0
      · subst j; exact hbase
      obtain ⟨k, hk, he⟩ := hconjugator j (by omega) hjn
      rw [F.initialResiduals_succ] at he ⊢
      exact F.center_induction_step (by omega) L (F.initialResiduals L j)
        (F.orderedResidual L (j + 1)) hUT hsplit hdisjoint
        (ih (by omega) (by omega)) (F.orderedResidual_isPPerfect L (j + 1))
        ((F.orderedResidual_le L (j + 1)).trans (F.orderedParabolic_le_H hn L (by omega)))
        k (F.orderedParabolic_le_H hn L (by omega) hk) he
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hh := hall (n - 1) (by omega) (by omega)
  rwa [hterminal] at hh
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
