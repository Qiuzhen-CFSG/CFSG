module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ActionData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.CubicOrders
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.ComponentAction

/-!
# The missing central direction and the intersection with BX

Write D = L₁ and X = L₁,+. If a D-normalized subgroup J contains X but
fails to contain L₀, its image in D/O₂(D) is the actual X mark. Indeed,
that quotient has order nine and the mark has order three; a full image
would force D ≤ J by two-perfectness. Taking the two-residual of D ∩ J
therefore gives precisely X. The source normalization of B specializes
this reduction to J = BX.

This is a reduction of the placement problem, not an exclusion of its
remaining branch. It preserves both intrinsic two-cores and uses the
actual hexacode natural action for the marked quotient orders.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.2.2(3), printed p.877, and the calculation in 13.8.20, printed p.954.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LocalAction
universe u v
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_eq_self (A : Subgroup G) (hp : IsPPerfect 2 A) :
    residual A = A := by
  unfold LinearThree.Geometry.CoveredProduct.ResidualPlacement.residual
  rw [(pResidual_eq_top_iff 2 A).mpr hp, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
/-- In a two-perfect group, a normal subgroup surjecting onto the two-core
quotient is the whole group. -/
private theorem le_of_full_image (D J : Subgroup G)
    (hp : IsPPerfect 2 D) (hn : D ≤ normalizer (J : Set G))
    (hi : Source.starImage D J = ⊤) : D ≤ J := by
  let I := D ⊓ J
  have hID : I ≤ D := inf_le_left
  let : (I.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf D.le_normalizer hn).trans inf_normalizer_le_normalizer_inf)
  have he : Source.starImage D I = ⊤ := by
    have hh : I.subgroupOf D = J.subgroupOf D := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    change (I.subgroupOf D).map _ = ⊤
    rw [hh]
    exact hi
  have hD : Source.starImage D D ≤ Source.starImage D I := by rw [he]; exact le_top
  exact (le_of_star_le D I D hID le_rfl hp hD).trans inf_le_right

/-- A proper subgroup of the marked order-nine quotient containing the plus
mark equals that mark. -/
private theorem image_eq_plus (L T V V₁ V₃ J : Subgroup G)
    (a : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hXJ : plus L T V₁ ≤ J)
    (hn : one L T V₁ ≤ normalizer (J : Set G))
    (hz : ¬ zero L ≤ J) :
    Source.starImage (one L T V₁) J =
      Source.starImage (one L T V₁) (plus L T V₁) := by
  let D := one L T V₁
  let C := Source.starImage D J
  let X := Source.starImage D (plus L T V₁)
  have hXC : X ≤ C := map_mono (subgroupOf_mono D hXJ)
  have hXcard : Nat.card X = 3 := by
    change Nat.card (Source.starImage D (plus L T V₁)) = 3
    rw [← localCoreMap_range D (plus L T V₁) (plus_le_one L T V₁ a.line_stable)
      (one_normalizes_plus L T V₁)]
    exact (Nat.card_congr (MonoidHom.ofInjective
      (localCoreMap_injective D (plus L T V₁) (plus_le_one L T V₁ a.line_stable)
        (one_normalizes_plus L T V₁))).toEquiv).symm.trans (a.plus_core_card hfactor)
  have hnine : Nat.card (Source.Hstar D) = 9 := a.one_quotient_card hfactor
  have hproper : C ≠ ⊤ := by
    intro he
    exact hz ((zero_le_one_of_factorization L T V₁ hfactor).trans
      (le_of_full_image D J (residual_isPPerfect _) hn he))
  have hd : Nat.card C ∣ 3 ^ 2 := by simpa [hnine] using C.card_subgroup_dvd_card
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hle : 3 ≤ Nat.card C := hXcard ▸ card_le_of_le hXC
  have hc : Nat.card C = 3 := by
    interval_cases k
    · change Nat.card C = 1 at he
      omega
    · exact he
    · have htop : C = ⊤ := eq_of_le_of_card_ge le_top (by simp [he, hnine])
      exact (hproper htop).elim
  exact (eq_of_le_of_card_ge hXC (by omega)).symm

/-- Losing the central direction leaves exactly X as the two-residual of
 the intersection with L₁. -/
theorem intersection_residual_of_not_zero (L T V V₁ V₃ J : Subgroup G)
    (a : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hXJ : plus L T V₁ ≤ J)
    (hn : one L T V₁ ≤ normalizer (J : Set G))
    (hz : ¬ zero L ≤ J) :
    residual (one L T V₁ ⊓ J) = plus L T V₁ := by
  let D := one L T V₁
  let I := D ⊓ J
  let X := plus L T V₁
  have hXD : X ≤ D := plus_le_one L T V₁ a.line_stable
  let : (X.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXD).mpr (one_normalizes_plus L T V₁)
  apply le_antisymm
  · apply le_of_star_le D X (residual I) hXD ((residual_le I).trans inf_le_left)
      (residual_isPPerfect I)
    exact (map_mono (subgroupOf_mono D ((residual_le I).trans inf_le_right))).trans
      (image_eq_plus L T V V₁ V₃ J a hfactor hXJ hn hz).le
  · change X ≤ residual I
    rw [← residual_eq_self X (residual_isPPerfect _)]
    exact embedded_pResidual_mono 2 (le_inf hXD hXJ)


variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)

/-- The actual product is normalized by L₁. This is relative normality only. -/
theorem one_normalizes_product : one L (T : Subgroup G) V₁ ≤
    normalizer ((d.B ⊔ plus L (T : Subgroup G) V₁ : Subgroup G) : Set G) :=
  (le_inf (le_sup_left.trans d.borel_normalized)
    (one_normalizes_plus L (T : Subgroup G) V₁)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

include a hfactor in
/-- The precise remaining branch, expressed without replacing either source residual. -/
theorem source_intersection_residual_of_not_zero
    (hz : ¬ zero L ≤ d.B ⊔ plus L (T : Subgroup G) V₁) :
    residual (one L (T : Subgroup G) V₁ ⊓
      (d.B ⊔ plus L (T : Subgroup G) V₁)) = plus L (T : Subgroup G) V₁ :=
  intersection_residual_of_not_zero L (T : Subgroup G) V V₁ V₃ _ a hfactor
    le_sup_right (one_normalizes_product d) hz


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement
