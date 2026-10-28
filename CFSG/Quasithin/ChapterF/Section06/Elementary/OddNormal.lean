module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Intersections
public import FeitThompson.FinalTheorem

/-!
# Solvability of the normal quotient in a Goldschmidt triple

The elementary Sylow argument proves that `XO₂(G)/O₂(G)` has odd order
when X is normal and meets each generator inside its two-core. Applying
the unconditional Feit–Thompson theorem gives solvability. This adapter
isolates the named campaign dependency from the elementary group arguments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.8, printed p.305 (1 March 2004 manuscript).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

public theorem IsGoldschmidtTriple.normal_quotient_solvable
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₁ : G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype)
    (h₂ : G₂ ⊓ X ≤ (pCore 2 G₂).map G₂.subtype) :
    Group.IsSolvable ((X ⊔ pCore 2 G : Subgroup G) ⧸
      (pCore 2 G).subgroupOf (X ⊔ pCore 2 G)) :=
  odd_order_theorem _ (h.normal_quotient_odd X h₁ h₂)

/-- Lemma F.6.8, with the literal quotient of `XQ` by the intrinsic copy of Q. -/
public theorem IsGoldschmidtTriple.normal_quotient_structure
    (h : IsGoldschmidtTriple G₁ G₂) (X : Subgroup G) [X.Normal]
    (h₁ : G₁ ⊓ X ≤ (pCore 2 G₁).map G₁.subtype)
    (h₂ : G₂ ⊓ X ≤ (pCore 2 G₂).map G₂.subtype) :
    (G₁ ⊓ G₂) ⊓ X ≤ pCore 2 G ∧
      Odd (Nat.card ((X ⊔ pCore 2 G : Subgroup G) ⧸
        (pCore 2 G).subgroupOf (X ⊔ pCore 2 G))) ∧
      Group.IsSolvable ((X ⊔ pCore 2 G : Subgroup G) ⧸
        (pCore 2 G).subgroupOf (X ⊔ pCore 2 G)) :=
  ⟨h.normal_intersection_le_twoCore X h₁ h₂,
    h.normal_quotient_odd X h₁ h₂, h.normal_quotient_solvable X h₁ h₂⟩

end CFSG.Quasithin.ChapterF
