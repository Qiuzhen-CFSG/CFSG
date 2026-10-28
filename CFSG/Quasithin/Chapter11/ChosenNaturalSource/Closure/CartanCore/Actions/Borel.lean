module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore
public import Theory.GroupTheory.CoprimeProductIntersection


/-!
# The Borel normalizer contradiction for the source Cartan

Inside G₁, the normal subgroup Y meets R₁X inside R₁: normality separates
the odd and two-group factors and X∩Y=1. Consequently an odd subgroup
B≤N_Y(T) preserving R₁X satisfies [X,B]≤R₁≤T. This contradicts any
field action detected on the corresponding Borel torus modulo T.

The source consumer explicitly uses N_G(T)≤M. The two missing model
outputs are kept distinct: field action produces a literal BorelMovement,
and the marked point-normalizer calculation supplies OddPointNormalizerAction.
Neither is asserted from arbitrary Geometry data. The final component-action
theorem is conditional until their original-source producers are proved.
Source: Aschbacher--Smith 11.5.6(3), printed pp.780--781.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions

/-- Normality of Y separates the odd and two-group factors of RX.
In the source this is applied internally to G₁. -/
theorem cartan_intersection_le {H : Type*} [Group H] [Finite H]
    (R X Y : Subgroup H) [Y.Normal] (hR : IsPGroup 2 R)
    (hX : Odd (Nat.card X)) (hn : X ≤ normalizer (R : Set H))
    (hd : Disjoint X Y) : (R ⊔ X) ⊓ Y ≤ R := by
  have hcop : Nat.Coprime (Nat.card R) (Nat.card X) := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hX).pow_left n
  have hperm : (R : Set H) * (X : Set H) = (X : Set H) * (R : Set H) :=
    (set_mul_normalizer_comm (X : Set H) R hn).symm
  intro g hg
  have hh : g ∈ (↑(R ⊓ Y) : Set H) * (↑(X ⊓ Y) : Set H) := by
    rw [← set_mul_inter_normal_of_coprime R X Y hcop,
      ← coe_sup_of_set_mul_comm R X hperm]
    exact hg
  obtain ⟨r, hr, x, hx, rfl⟩ := hh
  have he : x = 1 := mem_bot.mp (hd.eq_bot ▸ hx)
  change r * x ∈ R
  rw [he, mul_one]
  exact hr.1

/-- The Borel normalizer cannot move the Cartan modulo R.
This avoids making a separate Hall-conjugation choice. -/
theorem borel_commutator_le {H : Type*} [Group H] [Finite H]
    (R X Y B : Subgroup H) [Y.Normal] (hR : IsPGroup 2 R)
    (hX : Odd (Nat.card X)) (hn : X ≤ normalizer (R : Set H))
    (hd : Disjoint X Y) (hB : B ≤ Y)
    (hBX : B ≤ normalizer ((R ⊔ X : Subgroup H) : Set H)) :
    ⁅X, B⁆ ≤ R := by
  apply le_trans _ (cartan_intersection_le R X Y hR hX hn hd)
  apply le_inf
  · exact (commutator_mono le_sup_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hBX)
  · exact (commutator_mono le_rfl hB).trans (commutator_le_right _ _)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- A nontrivial field action detected by an odd Borel normalizer in Y.
This is an output specification for the even/odd model analysis, not an
assumption that components centralize X. All subgroups are literal. -/
def BorelMovement : Prop :=
  ∃ B : Subgroup G, B ≤ E.Y ∧ B ≤ normalizer (T : Set G) ∧
    Odd (Nat.card B) ∧ ¬ ⁅E.X, B⁆ ≤ (T : Subgroup G)

/-- The model-analysis output needed in 11.5.6(3). Its producer must
construct the odd Borel subgroup from the actual component and field action. -/
def ComponentBorelDetection : Prop :=
  ∀ I : Subgroup G, Source.ComponentIn E.Y I →
    ¬ ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2 → E.BorelMovement

/-- The exact local point-stabilizer calculation used after applying
N_G(T)≤M. Its production is a separate marked SL₃/Sp₄ model calculation. -/
def OddPointNormalizerAction : Prop :=
  ∀ B : Subgroup G, B ≤ E.M → B ≤ E.Y → B ≤ normalizer (T : Set G) →
    Odd (Nat.card B) → B ≤ normalizer ((E.R₁ ⊔ E.X : Subgroup G) : Set G)

/-- The original N_G(T)≤M application rules out a detected field action.
Y is only normal in G₁; no ambient normality assumption is used. -/
theorem no_borel_movement (hT : (T : Subgroup G) ≤ E.G₁)
    (hX : E.X ≤ E.G₁) (hodd : Odd (Nat.card E.X))
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hd : Disjoint E.X E.Y)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hlocal : E.OddPointNormalizerAction) : ¬ E.BorelMovement := by
  rintro ⟨B, hBY, hBN, hBo, hmove⟩
  have hBX := hlocal B (hBN.trans hNG) hBY hBN hBo
  let H := E.G₁
  let R := E.R₁.subgroupOf H
  let X := E.X.subgroupOf H
  let Y := E.Y.subgroupOf H
  let B₀ := B.subgroupOf H
  have hRT : E.R₁ ≤ (T : Subgroup G) := by
    simpa only [R₁, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hRH : E.R₁ ≤ H := hRT.trans hT
  have hBH : B ≤ H := hBY.trans E.Y_le_G₁
  let : Y.Normal :=
    (normal_subgroupOf_iff_le_normalizer E.Y_le_G₁).mpr E.G₁_normalizes_Y
  have hR : IsPGroup 2 R := (isPGroup_pCoreIn 2 _).comap_subtype
  have hXo : Odd (Nat.card X) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]
  have hXR₀ : X ≤ normalizer (R : Set H) := by
    intro x hx
    exact fun r => hXR hx r.val
  have hd₀ : Disjoint X Y := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro a ha
    exact Subtype.ext (disjoint_def.mp hd ha.1 ha.2)
  have hBX₀ : B₀ ≤ normalizer ((R ⊔ X : Subgroup H) : Set H) := by
    rw [← subgroupOf_sup hRH hX]
    intro b hb
    exact fun a => hBX hb a.val
  have hc := CartanActions.borel_commutator_le R X Y B₀ hR hXo hXR₀ hd₀
    (comap_mono hBY) hBX₀
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hX, map_subgroupOf_eq_of_le hBH,
    map_subgroupOf_eq_of_le hRH] at hm
  exact hmove (hm.trans hRT)

/-- Component centralization follows from the two independent model outputs.
This is conditional until the field-detection and point-normalizer producers
have discharged their premises on the original marked geometry. -/
theorem component_actions_of_borel_detection
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hlocal : E.OddPointNormalizerAction) (hdetect : E.ComponentBorelDetection)
    (I : Subgroup G) (hI : Source.ComponentIn E.Y I) :
    ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2 := by
  by_contra hne
  exact E.no_borel_movement hT hX hcart.odd hXR
    (E.cartan_disjoint_Y hcart.odd hCX hz) hNG hlocal (hdetect I hI hne)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
