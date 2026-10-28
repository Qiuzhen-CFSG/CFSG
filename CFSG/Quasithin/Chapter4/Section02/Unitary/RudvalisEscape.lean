module
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators
import Mathlib.Tactic

/-!
# The Rudvalis centralizer escape at the end of the unitary branch

J.2.3 gives an actual quaternion fixed subgroup of order eight. The central
product from J.2.2--4 places it in the centralizer of the original Ru2 group U.
Consequently V3 inside U has a centralizer escaping any subgroup meeting this
quaternion group in order at most four. The ambient version uses the literal
component embedding and the original intersection with M.

Constructing the Ru configuration, locating V3 in U and proving the
intersection bound remain the preceding source geometry of4.2.12/C.4.8;
none of those facts is asserted here. Source: Aschbacher--Smith, printed p.612.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup
open ChapterJ ChapterJ.Fusion
variable {K G : Type*} [Group K] [Finite K] [Group G]

/-- The exact quaternion fixed subgroup used on printed p.612, with its
centralization of the original Ru2 elementary subgroup derived from J.2.2–3. -/
theorem rudvalis_cubic_fixed_data (d : LocalSetup K) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    Nat.card (HB d.toTypeRuSetup B) = 8 ∧
      HB d.toTypeRuSetup B ≤ centralizer (d.toTypeRuSetup.U : Set K) := by
  obtain ⟨c,hc⟩ := lemma_J_2_3 d B
  have hq : Nonempty (HB d.toTypeRuSetup B ≃* QuaternionGroup 2) := hc.seven
  have hprod := centralProductData_of_quaternion d B hq
  refine ⟨?_,?_⟩
  · obtain ⟨e⟩ := hq
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  · have hle : HB d.toTypeRuSetup B ≤ d.toTypeRuSetup.HC := by
      rw [hprod.product_eq]
      exact le_sup_left
    exact hle.trans inf_le_right

/-- The source 8>4 argument with the actual V3≤U inclusion. No quaternion
or fixed-subgroup centralization statement remains as a premise. -/
theorem rudvalis_centralizer_escape (d : LocalSetup K) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (V3 M : Subgroup K) (hV3 : V3 ≤ d.toTypeRuSetup.U)
    (hcut : Nat.card (HB d.toTypeRuSetup B ⊓ M : Subgroup K) ≤ 4) :
    ¬ centralizer (V3 : Set K) ≤ M := by
  obtain ⟨hcard,hcentral⟩ := rudvalis_cubic_fixed_data d B
  intro hM
  have hle : HB d.toTypeRuSetup B ≤ M := (hcentral.trans (centralizer_le hV3)).trans hM
  rw [inf_eq_left.mpr hle,hcard] at hcut
  omega

/-- Ambient source transport through the literal embedding of the Ru component.
The intersection is taken with the original ambient M. -/
theorem rudvalis_ambient_escape (d : LocalSetup K) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (f : K →* G) (hf : Function.Injective f) (V3 M : Subgroup G)
    (hV3 : V3 ≤ d.toTypeRuSetup.U.map f)
    (hcut : Nat.card ((HB d.toTypeRuSetup B).map f ⊓ M : Subgroup G) ≤ 4) :
    ¬ centralizer (V3 : Set G) ≤ M := by
  obtain ⟨hcard,hcentral⟩ := rudvalis_cubic_fixed_data d B
  have hc : (HB d.toTypeRuSetup B).map f ≤ centralizer (V3 : Set G) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨b,hb,rfl⟩ := hV3 hv
    simpa only [← map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp (hcentral ha) b hb)
  intro hM
  have hle := hc.trans hM
  rw [inf_eq_left.mpr hle,card_map_of_injective hf,hcard] at hcut
  omega

/-- The unitary branch is impossible after the source centralizer bound, with
all fixed-group calculations discharged by the original Chapter J setup. -/
theorem not_unitary_counterexample (d : LocalSetup K) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (f : K →* G) (hf : Function.Injective f) (V3 M : Subgroup G)
    (hV3 : V3 ≤ d.toTypeRuSetup.U.map f)
    (hcut : Nat.card ((HB d.toTypeRuSetup B).map f ⊓ M : Subgroup G) ≤ 4)
    (hC : centralizer (V3 : Set G) ≤ M) : False :=
  rudvalis_ambient_escape d B f hf V3 M hV3 hcut hC

end CFSG.Quasithin.Chapter4.Section02.Unitary
