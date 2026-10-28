module

public import CFSG.Quasithin.ChapterJ.Section04To05.SourceAmalgam.Local

/-!
# The original index-two overgroup of the first endpoint

The first endpoint intersects Q in its two-core of order1024, while Q has
order2048. Since the endpoint lies in H and H normalizes Q, the product formula
gives |F₁Q|=40960 and [F₁Q:F₁]=2. These are the original coordinates needed for
the first adjacent pair in the coset action of J.5.
Source: Aschbacher–Smith J.5.2–3, printed pp.445–446.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

theorem SourceChoice.card_F₁_sup_Q (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) :
    Nat.card (p.F₁ B5 ⊔ d.toTypeRuSetup.Q : Subgroup G) = 40960 := by
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes d.toTypeRuSetup.Q
    (p.F₁ B5) ((p.F₁_le_H B5).trans d.ru2.six.normalized)
  rw [d.ru2.card_Q d.card_Z,s.card_F₁ p B5 hi,inf_comm,s.F₁_inf_Q p B5 hi,
    fiveHyperplane_card,sup_comm] at h
  omega

theorem SourceChoice.F₁_relIndex_sup_Q (s : SourceChoice p)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (hi : ∀ a ∈ B5Image B5, s.v*a*s.v⁻¹=a⁻¹) :
    (p.F₁ B5).relIndex (p.F₁ B5 ⊔ d.toTypeRuSetup.Q) = 2 := by
  have h := ((p.F₁ B5).subgroupOf (p.F₁ B5 ⊔ d.toTypeRuSetup.Q)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show p.F₁ B5 ≤ p.F₁ B5 ⊔ d.toTypeRuSetup.Q from le_sup_left)).toEquiv] at h
  change Nat.card (p.F₁ B5) * (p.F₁ B5).relIndex (p.F₁ B5 ⊔ d.toTypeRuSetup.Q) = _ at h
  rw [s.card_F₁ p B5 hi,s.card_F₁_sup_Q p B5 hi] at h
  omega

end CFSG.Quasithin.ChapterJ.RuSubgroup
