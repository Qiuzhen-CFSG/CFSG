module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking

/-!
# The cubic order in the original plus quotient

The marked conjugate span has order eight, whereas the seed has order two.
Consequently L_v moves the seed. Its two-perfect plus image cannot be a
two-group. The earlier quotient order three bounds its order by three times
a power of two, so every Sylow three-subgroup of the actual plus image has
order three. This is the cubic input for the diagonal argument in 13.6.14.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, printed p.929; the marking and cubic order precede 13.6.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open A5Module ComponentReduction InitialSieve
open ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original marked residual moves the seed. -/
theorem markedLv_not_centralizes_seed {L V : Subgroup G} (s : Marking L V) :
    ¬ Lv L (markedV s) ≤ centralizer ({markedZ s} : Set G) := by
  intro hc
  have hn : Lv L (markedV s) ≤ normalizer (zpowers (markedZ s) : Set G) := by
    apply le_trans hc
    rw [← centralizer_closure, ← zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hspan : Vv L (markedZ s) (markedV s) ≤ zpowers (markedZ s) :=
    conjugateSpanBy_le le_rfl hn
  have hb := card_le_of_le hspan
  rw [Vv_card s, Nat.card_zpowers, (marked_orders s).1] at hb
  omega

private theorem sylow_three_card_of_bound {D : Type*} [Group D] [Finite D]
    (hn : ¬ IsPGroup 2 D) (hb : ∃ n, Nat.card D ∣ 3 * 2 ^ n)
    (P : Sylow 3 D) : Nat.card P = 3 := by
  obtain ⟨n, hncard⟩ := hb
  have hd : 3 ∣ Nat.card D := by
    by_contra hd
    apply hn
    apply isPGroup_iff_card_dvd_pow.mpr
    exact ⟨n, (Nat.prime_three.coprime_iff_not_dvd.mpr hd).symm.dvd_of_dvd_mul_left hncard⟩
  apply Nat.dvd_antisymm ?_ (P.dvd_card_of_dvd_card hd)
  have hcop : (Nat.card P).Coprime (2 ^ n) := by
    obtain ⟨r, hr⟩ := P.isPGroup'.exists_card_eq
    rw [hr]
    exact (by decide : Nat.Coprime 3 2).pow r n
  exact hcop.dvd_of_dvd_mul_right ((P : Subgroup D).card_subgroup_dvd_card.trans hncard)

/-- The literal plus image has exactly one factor of three in its order. -/
theorem plusLv_sylow_three_card_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (P : Sylow 3 (plusImage K L T z v hL hz (Lv L v))) :
    Nat.card P = 3 :=
  sylow_three_card_of_bound (plusLv_not_isPGroup K L T z v hL hz hmove)
    (plusLv_card_dvd K L T z v hL hz hc) P

variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The original source hypotheses supply the cubic Sylow order with no
model or diagonal-action premise. -/
theorem plusLv_sylow_three_card_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (P : Sylow 3 (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz (Lv L (markedV d.flag.module)))) :
    Nat.card P = 3 := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact plusLv_sylow_three_card_source K L (T : Subgroup G) _ _ hL hz
    (markedLv_not_centralizes_seed d.flag.module) c.residual_card P

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
